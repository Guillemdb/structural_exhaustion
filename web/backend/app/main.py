"""Flask application factory for the Hypostructure documentation site."""

from __future__ import annotations

import hashlib
import json
import logging
from pathlib import Path
import re
from typing import Any, Callable

from flask import Blueprint, Flask, Response, current_app, request, send_from_directory
from pydantic import JsonValue, TypeAdapter, ValidationError
from werkzeug.exceptions import HTTPException

from .models import SearchQuery, SourceExcerptQuery
from .repository import ArtifactError, EntityNotFound, SnapshotRepository


LOGGER = logging.getLogger("hypostructure.web")
JSON_OBJECT = TypeAdapter(dict[str, JsonValue])
HASHED_ASSET_RE = re.compile(r"[.-][A-Za-z0-9_-]{8,}[.-]")
SPA_ROUTE_RE = re.compile(
    r"^(?:"
    r"|start|graph|pde|examples|erdos|reference|search"
    r"|core(?:/cts(?:/[^/]+)?|/routes(?:/[^/]+)?|)?"
    r"|examples/[^/]+"
    r"|erdos/nodes/[^/]+"
    r"|reference/(?:modules|declarations)/[^/]+"
    r"|source/[^/]+"
    r")$"
)
PAGE_IDS = {
    "home",
    "start",
    "core",
    "graph",
    "pde",
    "examples",
    "erdos",
    "reference",
    "routes",
    "cts",
}


class SnapshotUnavailable(RuntimeError):
    """The canonical snapshot failed closed at application startup."""


def _problem(
    status: int,
    title: str,
    detail: str,
    *,
    problem_type: str = "about:blank",
) -> Response:
    payload = {
        "type": problem_type,
        "title": title,
        "status": status,
        "detail": detail,
        "instance": request.path,
    }
    response = current_app.response_class(
        json.dumps(payload, ensure_ascii=False, separators=(",", ":")),
        status=status,
        mimetype="application/problem+json",
    )
    response.headers["Cache-Control"] = "no-store"
    return response


def _json_response(payload: dict[str, Any], *, status: int = 200) -> Response:
    validated = JSON_OBJECT.validate_python(payload)
    encoded = json.dumps(
        validated,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    digest = hashlib.sha256(encoded).hexdigest()
    if request.if_none_match.contains(digest):
        response = current_app.response_class(status=304)
    else:
        response = current_app.response_class(
            encoded, status=status, mimetype="application/json"
        )
    response.set_etag(digest, weak=False)
    response.headers["Cache-Control"] = "public, max-age=0, must-revalidate"
    response.headers["X-Content-Type-Options"] = "nosniff"
    return response


def _repository() -> SnapshotRepository:
    repository = current_app.extensions.get("hypostructure_snapshot")
    if not isinstance(repository, SnapshotRepository):
        raise SnapshotUnavailable("canonical Hypostructure snapshot is unavailable")
    return repository


def _entity_response(loader: Callable[[str], dict[str, Any]], identifier: str) -> Response:
    try:
        return _json_response(loader(identifier))
    except EntityNotFound as error:
        raise EntityNotFound(identifier) from error


def _parse_search_query() -> SearchQuery:
    values = request.args.to_dict(flat=True)
    if "page_size" not in values and "pageSize" in values:
        values["page_size"] = values.pop("pageSize")
    return SearchQuery.model_validate(values)


def _parse_excerpt_query() -> SourceExcerptQuery:
    values = request.args.to_dict(flat=True)
    if "start" not in values and "startLine" in values:
        values["start"] = values.pop("startLine")
    if "end" not in values and "endLine" in values:
        values["end"] = values.pop("endLine")
    return SourceExcerptQuery.model_validate(values)


def _api_blueprint() -> Blueprint:
    api = Blueprint("api_v2", __name__, url_prefix="/api/v2")

    @api.get("/health/live")
    def live() -> Response:
        return _json_response({"status": "ok", "service": "hypostructure-web"})

    @api.get("/health/ready")
    def ready() -> Response:
        repository = _repository()
        return _json_response(
            {
                "status": "ready",
                "schemaVersion": repository.schema_version,
                "snapshotHash": repository.snapshot_hash,
                "counts": repository.counts,
            }
        )

    @api.get("/site")
    def site() -> Response:
        return _json_response(_repository().site())

    @api.get("/pages/<page_id>")
    def page(page_id: str) -> Response:
        if page_id not in PAGE_IDS:
            raise EntityNotFound(page_id)
        return _entity_response(_repository().page, page_id)

    @api.get("/cts/<ct_id>")
    def ct(ct_id: str) -> Response:
        return _entity_response(_repository().ct, ct_id)

    @api.get("/routes/<path:route_id>")
    def route(route_id: str) -> Response:
        return _entity_response(_repository().route, route_id)

    @api.get("/examples/<path:example_id>")
    def example(example_id: str) -> Response:
        return _entity_response(_repository().example, example_id)

    @api.get("/erdos/nodes/<path:node_id>")
    def erdos_node(node_id: str) -> Response:
        return _entity_response(_repository().erdos_node, node_id)

    @api.get("/reference/modules/<path:module_id>")
    def module(module_id: str) -> Response:
        return _entity_response(_repository().module, module_id)

    @api.get("/reference/declarations/<path:declaration_id>")
    def declaration(declaration_id: str) -> Response:
        return _entity_response(_repository().declaration, declaration_id)

    @api.get("/search")
    def search() -> Response:
        return _json_response(_repository().search(_parse_search_query()))

    @api.get("/sources/<path:source_id>/excerpt")
    def source_excerpt(source_id: str) -> Response:
        try:
            payload = _repository().source_excerpt(source_id, _parse_excerpt_query())
        except ValueError as error:
            return _problem(400, "Invalid source range", str(error))
        return _json_response(payload)

    return api


def create_app(
    repository: SnapshotRepository | None = None,
    dist_dir: Path | str | None = None,
    *,
    root: Path | str | None = None,
    artifact_dir: Path | str | None = None,
) -> Flask:
    """Create a same-origin Flask API and React static-file application."""

    repository_root = Path(root or Path(__file__).resolve().parents[3]).resolve()
    frontend = Path(dist_dir or repository_root / "build/web").resolve()
    app = Flask("hypostructure_web", static_folder=None)
    app.config.update(
        JSON_SORT_KEYS=False,
        MAX_CONTENT_LENGTH=1024 * 1024,
        FRONTEND_DIST=frontend,
    )

    load_error: ArtifactError | None = None
    if repository is None:
        try:
            repository = SnapshotRepository(repository_root, artifact_dir)
        except ArtifactError as error:
            load_error = error
            LOGGER.error("Hypostructure web snapshot rejected: %s", error)
    if repository is not None:
        app.extensions["hypostructure_snapshot"] = repository
    app.extensions["hypostructure_snapshot_error"] = load_error
    app.register_blueprint(_api_blueprint())

    @app.errorhandler(SnapshotUnavailable)
    def unavailable(_error: SnapshotUnavailable) -> Response:
        return _problem(
            503,
            "Service unavailable",
            "The verified Hypostructure documentation snapshot is unavailable.",
            problem_type="https://hypostructure.dev/problems/snapshot-unavailable",
        )

    @app.errorhandler(ArtifactError)
    def stale_artifact(_error: ArtifactError) -> Response:
        return _problem(
            503,
            "Service unavailable",
            "Published Hypostructure evidence failed verification.",
            problem_type="https://hypostructure.dev/problems/evidence-verification",
        )

    @app.errorhandler(EntityNotFound)
    def entity_not_found(_error: EntityNotFound) -> Response:
        return _problem(404, "Not found", "The requested resource does not exist.")

    @app.errorhandler(ValidationError)
    def invalid_query(error: ValidationError) -> Response:
        detail = "; ".join(
            f"{'.'.join(str(part) for part in item['loc'])}: {item['msg']}"
            for item in error.errors(include_url=False)
        )
        return _problem(400, "Invalid request", detail)

    @app.errorhandler(HTTPException)
    def http_error(error: HTTPException) -> Response:
        return _problem(error.code or 500, error.name, error.description)

    @app.errorhandler(Exception)
    def unexpected_error(_error: Exception) -> Response:
        app.logger.exception("Unhandled Hypostructure web error", exc_info=True)
        return _problem(
            500,
            "Internal server error",
            "The request could not be completed.",
        )

    @app.get("/")
    @app.get("/<path:requested_path>")
    def frontend_file(requested_path: str = "") -> Response:
        if requested_path.startswith("api/"):
            return _problem(404, "Not found", "The requested API resource does not exist.")
        candidate = (frontend / requested_path).resolve()
        if candidate != frontend and frontend not in candidate.parents:
            return _problem(404, "Not found", "The requested resource does not exist.")
        if candidate.is_file():
            response = send_from_directory(frontend, requested_path, conditional=True)
            if requested_path.startswith("assets/") and HASHED_ASSET_RE.search(
                Path(requested_path).name
            ):
                response.headers["Cache-Control"] = "public, max-age=31536000, immutable"
            else:
                response.headers["Cache-Control"] = "public, max-age=3600"
            return response
        if Path(requested_path).suffix:
            return _problem(404, "Not found", "The requested asset does not exist.")
        index = frontend / "index.html"
        if not index.is_file():
            return _problem(
                503,
                "Frontend unavailable",
                "The React production build is not available.",
            )
        response = send_from_directory(frontend, "index.html", conditional=True)
        if not SPA_ROUTE_RE.fullmatch(requested_path):
            # Return the React not-found document with an honest HTTP status.
            response.status_code = 404
        response.headers["Cache-Control"] = "no-cache"
        return response

    @app.after_request
    def security_headers(response: Response) -> Response:
        response.headers.setdefault("X-Content-Type-Options", "nosniff")
        response.headers.setdefault("X-Frame-Options", "DENY")
        response.headers.setdefault("Referrer-Policy", "strict-origin-when-cross-origin")
        response.headers.setdefault("Cross-Origin-Resource-Policy", "same-origin")
        response.headers.setdefault(
            "Permissions-Policy", "camera=(), geolocation=(), microphone=()"
        )
        response.headers.setdefault(
            "Content-Security-Policy",
            "default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline'; "
            "img-src 'self' data:; font-src 'self' data:; connect-src 'self'; "
            "object-src 'none'; base-uri 'self'; frame-ancestors 'none'; "
            "form-action 'self'",
        )
        return response

    return app
