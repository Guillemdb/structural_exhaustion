"""Validated, immutable access to the generated Hypostructure web snapshot."""

from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass
import hashlib
import html
import json
from pathlib import Path
import re
from typing import Any, Iterable, Mapping, Sequence

from jsonschema import Draft202012Validator
from jsonschema.exceptions import SchemaError
from pydantic import ValidationError

from .erdos_topology import (
    CANONICAL_ERDOS_EDGE_PAIRS,
    CANONICAL_ERDOS_INCOMING_NUMBERS,
    CANONICAL_ERDOS_NODE_IDS,
)
from .models import ManifestModel, SearchQuery, SnapshotModel, SourceExcerptQuery


SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
CONTRACT_ROOT = Path(__file__).resolve().parents[2] / "contracts"
WORD_RE = re.compile(r"[\w'-]+", re.UNICODE)
SEARCH_KIND_PRIOR = {
    "page": 18,
    "ct": 16,
    "module": 12,
    "example": 10,
    "route": 8,
    "erdos_node": 8,
    "declaration": 0,
}
FORBIDDEN_PUBLIC_TERMS = re.compile(
    r"\b(?:structural[ -]exhaustion|migration|legacy|cutover)\b",
    re.IGNORECASE,
)
ALLOWED_SOURCE_SUFFIXES = {".lean", ".md", ".tex"}
ALLOWED_SOURCE_ROOTS = (
    Path("hypostructure/Hypostructure"),
    Path("examples/hypostructure_erdos_64_eg"),
    Path("examples/hypostructure_pde"),
)
ENTITY_ID_FIELDS = {
    "cts": ("id", "ctId", "tacticId"),
    "routes": ("id", "routeId"),
    "examples": ("id", "exampleId"),
    "modules": ("id", "moduleId", "name"),
    "declarations": ("id", "declarationId", "name"),
    "nodes": ("id", "nodeId"),
}


class ArtifactError(RuntimeError):
    """A generated web artifact is absent, stale, or malformed."""


class EntityNotFound(KeyError):
    """A requested canonical entity does not exist in the snapshot."""


def _load_json_object(path: Path) -> tuple[dict[str, Any], bytes]:
    if not path.is_file():
        raise ArtifactError(f"required generated artifact is missing: {path}")
    try:
        payload = path.read_bytes()
        value = json.loads(payload.decode("utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ArtifactError(f"cannot load generated artifact {path}: {error}") from error
    if not isinstance(value, dict):
        raise ArtifactError(f"generated artifact must be a JSON object: {path}")
    return value, payload


def _validate_json_schema(value: dict[str, Any], schema_path: Path, label: str) -> None:
    """Validate a generated artifact against its bundled canonical schema."""

    schema, _schema_bytes = _load_json_object(schema_path)
    try:
        Draft202012Validator.check_schema(schema)
    except SchemaError as error:
        raise ArtifactError(f"invalid bundled {label} schema: {error.message}") from error
    errors = sorted(
        Draft202012Validator(schema).iter_errors(value),
        key=lambda error: tuple(str(part) for part in error.absolute_path),
    )
    if not errors:
        return
    details: list[str] = []
    for error in errors[:5]:
        location = "$" + "".join(
            f"[{part}]" if isinstance(part, int) else f".{part}"
            for part in error.absolute_path
        )
        details.append(f"{location}: {error.message}")
    if len(errors) > 5:
        details.append(f"and {len(errors) - 5} more validation errors")
    raise ArtifactError(f"{label} does not satisfy its JSON Schema: {'; '.join(details)}")


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _sha256_path(path: Path) -> str:
    try:
        return _sha256_bytes(path.read_bytes())
    except OSError as error:
        raise ArtifactError(f"cannot read published source {path}: {error}") from error


def _public_text_error(value: Any, location: str = "snapshot") -> str | None:
    """Return the first forbidden publish-facing term, if any.

    Source paths are validated separately. Searchable/public prose must describe
    only the finished Hypostructure product.
    """

    if isinstance(value, str):
        match = FORBIDDEN_PUBLIC_TERMS.search(value)
        if match:
            return f"{location} contains forbidden publish-facing term {match.group(0)!r}"
        return None
    if isinstance(value, Mapping):
        for key, child in value.items():
            key_error = _public_text_error(str(key), f"{location} key")
            if key_error:
                return key_error
            child_error = _public_text_error(child, f"{location}.{key}")
            if child_error:
                return child_error
        return None
    if isinstance(value, Sequence) and not isinstance(value, (bytes, bytearray)):
        for index, child in enumerate(value):
            child_error = _public_text_error(child, f"{location}[{index}]")
            if child_error:
                return child_error
    return None


def _entity_id(record: Mapping[str, Any], collection: str) -> str:
    for field in ENTITY_ID_FIELDS[collection]:
        value = record.get(field)
        if isinstance(value, (str, int)) and not isinstance(value, bool):
            identifier = str(value).strip()
            if identifier:
                return identifier
    raise ArtifactError(f"{collection} record has no stable identifier")


def _index_collection(value: Any, collection: str) -> dict[str, dict[str, Any]]:
    if isinstance(value, Mapping):
        items: Iterable[tuple[str | None, Any]] = (
            (str(key), record) for key, record in value.items()
        )
    elif isinstance(value, list):
        items = ((None, record) for record in value)
    else:
        raise ArtifactError(f"snapshot {collection} must be an object or array")

    result: dict[str, dict[str, Any]] = {}
    for map_id, raw_record in items:
        if not isinstance(raw_record, dict):
            raise ArtifactError(f"snapshot {collection} contains a non-object record")
        identifier = map_id or _entity_id(raw_record, collection)
        if map_id:
            embedded_ids = [
                str(raw_record[field])
                for field in ENTITY_ID_FIELDS[collection]
                if field in raw_record
                and isinstance(raw_record[field], (str, int))
                and not isinstance(raw_record[field], bool)
            ]
            if embedded_ids and identifier not in embedded_ids:
                raise ArtifactError(
                    f"snapshot {collection} key {identifier!r} disagrees with its record"
                )
        if identifier in result:
            raise ArtifactError(f"snapshot {collection} repeats ID {identifier!r}")
        result[identifier] = raw_record
    return result


def _canonical_lookup(index: Mapping[str, dict[str, Any]], identifier: str) -> dict[str, Any]:
    direct = index.get(identifier)
    if direct is not None:
        return direct
    folded = identifier.casefold()
    matches = [value for key, value in index.items() if key.casefold() == folded]
    if len(matches) == 1:
        return matches[0]
    raise EntityNotFound(identifier)


@dataclass(frozen=True)
class PublishedSource:
    source_id: str
    path: Path
    relative_path: str
    sha256: str


class SnapshotRepository:
    """Load and validate one generated snapshot for the process lifetime."""

    def __init__(
        self,
        root: Path | str | None = None,
        artifact_dir: Path | str | None = None,
    ) -> None:
        self.root = Path(root or Path(__file__).resolve().parents[3]).resolve()
        self.artifact_dir = Path(
            artifact_dir or self.root / "generated/hypostructure/web"
        ).resolve()
        snapshot_path = self.artifact_dir / "snapshot.json"
        manifest_path = self.artifact_dir / "manifest.json"

        raw_snapshot, snapshot_bytes = _load_json_object(snapshot_path)
        raw_manifest, _manifest_bytes = _load_json_object(manifest_path)
        _validate_json_schema(
            raw_snapshot,
            CONTRACT_ROOT / "snapshot.schema.json",
            "Hypostructure web snapshot",
        )
        _validate_json_schema(
            raw_manifest,
            CONTRACT_ROOT / "manifest.schema.json",
            "Hypostructure web manifest",
        )
        try:
            snapshot = SnapshotModel.model_validate(raw_snapshot)
            manifest = ManifestModel.model_validate(raw_manifest)
        except ValidationError as error:
            raise ArtifactError(f"invalid Hypostructure web snapshot: {error}") from error

        actual_hash = _sha256_bytes(snapshot_bytes)
        if not SHA256_RE.fullmatch(manifest.snapshot_sha256):
            raise ArtifactError("manifest snapshot hash is malformed")
        if actual_hash != manifest.snapshot_sha256:
            raise ArtifactError("generated Hypostructure web snapshot is stale")
        if snapshot.schema_version != manifest.schema_version:
            raise ArtifactError("snapshot and manifest schema versions disagree")
        trust_state = str(
            snapshot.trust.get("state", snapshot.trust.get("status", ""))
        ).casefold()
        if trust_state not in {"verified", "kernel_checked"}:
            raise ArtifactError("generated Hypostructure snapshot is not verified")

        publishable = {
            "site": snapshot.site,
            "pages": snapshot.pages,
            "modules": snapshot.modules,
            "declarations": snapshot.declarations,
            "cts": snapshot.cts,
            "routes": snapshot.routes,
            "examples": snapshot.examples,
            "erdos": snapshot.erdos,
            "search_documents": snapshot.search_documents,
            "trust": snapshot.trust,
        }
        if error := _public_text_error(publishable):
            raise ArtifactError(error)

        self.schema_version = snapshot.schema_version
        self.snapshot_hash = actual_hash
        self._site = snapshot.site
        self._pages = snapshot.pages
        self._cts = _index_collection(snapshot.cts, "cts")
        self._routes = _index_collection(snapshot.routes, "routes")
        self._examples = _index_collection(snapshot.examples, "examples")
        self._modules = _index_collection(snapshot.modules, "modules")
        self._declarations = _index_collection(snapshot.declarations, "declarations")
        nodes = snapshot.erdos.get("nodes", {})
        self._erdos_nodes = _index_collection(nodes, "nodes")
        self._validate_erdos_topology(snapshot.erdos)
        self._search_documents = self._validate_search_documents(
            snapshot.search_documents
        )
        self._sources = self._validate_sources(manifest.sources)
        self._validate_snapshot_source_ids(snapshot.sources)
        self._validate_manifest_counts(manifest.counts)

    @property
    def counts(self) -> dict[str, int]:
        return {
            "pages": len(self._pages),
            "cts": len(self._cts),
            "routes": len(self._routes),
            "examples": len(self._examples),
            "erdos_nodes": len(self._erdos_nodes),
            "modules": len(self._modules),
            "declarations": len(self._declarations),
            "sources": len(self._sources),
            "search_documents": len(self._search_documents),
        }

    def _validate_sources(self, records: list[Any]) -> dict[str, PublishedSource]:
        result: dict[str, PublishedSource] = {}
        resolved_source_roots = [
            (self.root / allowed_root).resolve()
            for allowed_root in ALLOWED_SOURCE_ROOTS
        ]
        for record in records:
            source_id = record.id
            if source_id in result:
                raise ArtifactError(f"manifest repeats source ID {source_id!r}")
            relative = Path(record.path)
            if relative.is_absolute() or ".." in relative.parts:
                raise ArtifactError(f"source {source_id!r} has an unsafe path")
            if not any(
                relative == allowed_root or allowed_root in relative.parents
                for allowed_root in ALLOWED_SOURCE_ROOTS
            ):
                raise ArtifactError(f"source {source_id!r} is outside publishable roots")
            if FORBIDDEN_PUBLIC_TERMS.search(record.path):
                raise ArtifactError(f"source {source_id!r} is not publishable")
            if relative.suffix.lower() not in ALLOWED_SOURCE_SUFFIXES:
                raise ArtifactError(f"source {source_id!r} has an unsupported file type")
            resolved = (self.root / relative).resolve()
            if resolved != self.root and self.root not in resolved.parents:
                raise ArtifactError(f"source {source_id!r} escapes the repository")
            if not any(
                resolved == allowed_root or allowed_root in resolved.parents
                for allowed_root in resolved_source_roots
            ):
                raise ArtifactError(f"source {source_id!r} resolves outside publishable roots")
            if not resolved.is_file():
                raise ArtifactError(f"published source {source_id!r} is missing")
            if _sha256_path(resolved) != record.sha256:
                raise ArtifactError(f"published source {source_id!r} is stale")
            result[source_id] = PublishedSource(
                source_id=source_id,
                path=resolved,
                relative_path=relative.as_posix(),
                sha256=record.sha256,
            )
        return result

    def _validate_snapshot_source_ids(self, value: Any) -> None:
        records: Iterable[tuple[str | None, Any]]
        if isinstance(value, Mapping):
            records = ((str(source_id), record) for source_id, record in value.items())
        elif isinstance(value, list):
            records = ((None, record) for record in value)
        else:
            raise ArtifactError("snapshot sources must be an object or array")
        for mapped_id, raw in records:
            if not isinstance(raw, Mapping):
                raise ArtifactError("snapshot source metadata must be objects")
            source_id = raw.get("id", raw.get("sourceId", mapped_id))
            if not isinstance(source_id, str) or source_id not in self._sources:
                raise ArtifactError("snapshot references an unknown source ID")
            if "content" in raw:
                raise ArtifactError("snapshot must not embed complete source files")
            manifest_source = self._sources[source_id]
            path = raw.get("path")
            if path is not None and path != manifest_source.relative_path:
                raise ArtifactError(f"snapshot source {source_id!r} path disagrees with manifest")
            digest = raw.get("sha256")
            if digest is not None and digest != manifest_source.sha256:
                raise ArtifactError(f"snapshot source {source_id!r} hash disagrees with manifest")

    def _validate_manifest_counts(self, counts: Mapping[str, int]) -> None:
        actual = self.counts
        aliases = {"erdosNodes": "erdos_nodes", "searchDocuments": "search_documents"}
        for manifest_key, expected in counts.items():
            key = aliases.get(manifest_key, manifest_key)
            if key in actual and actual[key] != expected:
                raise ArtifactError(f"manifest count {manifest_key!r} disagrees with snapshot")

    def _validate_erdos_topology(self, erdos: Mapping[str, Any]) -> None:
        """Require the complete immutable paper graph and its display mirror."""

        node_ids = set(self._erdos_nodes)
        if node_ids != CANONICAL_ERDOS_NODE_IDS:
            missing = sorted(CANONICAL_ERDOS_NODE_IDS - node_ids)
            extra = sorted(node_ids - CANONICAL_ERDOS_NODE_IDS)
            raise ArtifactError(
                "Erdős topology does not contain exactly nodes 1–157"
                f" (missing={missing[:3]!r}, extra={extra[:3]!r})"
            )

        for number, expected_predecessors in CANONICAL_ERDOS_INCOMING_NUMBERS.items():
            node_id = f"node-{number}"
            node = self._erdos_nodes[node_id]
            if node.get("number") != number:
                raise ArtifactError(f"Erdős topology node {node_id!r} has the wrong number")
            expected_incoming = [f"node-{value}" for value in expected_predecessors]
            if node.get("incoming") != expected_incoming:
                raise ArtifactError(
                    f"Erdős topology node {node_id!r} has incorrect predecessors"
                )

        roots = erdos.get("root_node_ids")
        if roots != ["node-1"]:
            raise ArtifactError("Erdős topology must have node-1 as its sole declared root")

        edges, edge_pairs = self._index_erdos_edges(erdos.get("edges"), "topology")
        if edge_pairs != CANONICAL_ERDOS_EDGE_PAIRS:
            missing = sorted(CANONICAL_ERDOS_EDGE_PAIRS - edge_pairs)
            extra = sorted(edge_pairs - CANONICAL_ERDOS_EDGE_PAIRS)
            raise ArtifactError(
                "Erdős topology does not match the canonical direct-predecessor relation"
                f" (missing={missing[:3]!r}, extra={extra[:3]!r})"
            )
        derived_roots = node_ids - {target for _source, target in edge_pairs}
        if derived_roots != {"node-1"}:
            raise ArtifactError("Erdős topology does not derive node-1 as its sole root")

        graph = erdos.get("graph")
        if not isinstance(graph, Mapping):
            raise ArtifactError("Erdős topology graph must be an object")
        graph_nodes = _index_collection(graph.get("nodes"), "nodes")
        if set(graph_nodes) != CANONICAL_ERDOS_NODE_IDS:
            raise ArtifactError("Erdős display graph does not mirror all canonical nodes")
        graph_edges, graph_edge_pairs = self._index_erdos_edges(
            graph.get("edges"), "display graph"
        )
        if graph_edge_pairs != CANONICAL_ERDOS_EDGE_PAIRS:
            raise ArtifactError("Erdős display graph does not mirror canonical edges")
        if graph_edges != edges:
            raise ArtifactError("Erdős display graph edges disagree with topology edges")

        for node_id, node in self._erdos_nodes.items():
            display_node = graph_nodes[node_id]
            if display_node.get("label") != node.get("label"):
                raise ArtifactError(
                    f"Erdős display graph label disagrees for node {node_id!r}"
                )
            if display_node.get("href") != node.get("url"):
                raise ArtifactError(
                    f"Erdős display graph link disagrees for node {node_id!r}"
                )

    @staticmethod
    def _index_erdos_edges(
        value: Any, label: str
    ) -> tuple[dict[str, dict[str, Any]], frozenset[tuple[str, str]]]:
        if not isinstance(value, list):
            raise ArtifactError(f"Erdős {label} edges must be an array")
        indexed: dict[str, dict[str, Any]] = {}
        pairs: set[tuple[str, str]] = set()
        for edge in value:
            if not isinstance(edge, dict):
                raise ArtifactError(f"Erdős {label} contains a non-object edge")
            edge_id = edge.get("id")
            source = edge.get("source")
            target = edge.get("target")
            if not all(isinstance(field, str) and field for field in (edge_id, source, target)):
                raise ArtifactError(f"Erdős {label} contains a malformed edge")
            if source not in CANONICAL_ERDOS_NODE_IDS or target not in CANONICAL_ERDOS_NODE_IDS:
                raise ArtifactError(f"Erdős {label} edge {edge_id!r} has an unknown endpoint")
            expected_id = f"{source}-to-{target.removeprefix('node-')}"
            if edge_id != expected_id:
                raise ArtifactError(f"Erdős {label} edge {edge_id!r} has a noncanonical ID")
            pair = (source, target)
            if edge_id in indexed or pair in pairs:
                raise ArtifactError(f"Erdős {label} repeats edge {edge_id!r}")
            indexed[edge_id] = edge
            pairs.add(pair)
        return indexed, frozenset(pairs)

    @staticmethod
    def _validate_search_documents(value: Any) -> list[dict[str, Any]]:
        if not isinstance(value, list):
            raise ArtifactError("snapshot search_documents must be an array")
        seen: set[str] = set()
        documents: list[dict[str, Any]] = []
        for raw in value:
            if not isinstance(raw, dict):
                raise ArtifactError("search document must be an object")
            required = ("id", "title", "url", "kind")
            if any(not isinstance(raw.get(field), str) or not raw[field] for field in required):
                raise ArtifactError("search document lacks an ID, title, URL, or kind")
            if raw["id"] in seen:
                raise ArtifactError(f"search document repeats ID {raw['id']!r}")
            if not raw["url"].startswith("/") or raw["url"].startswith("//"):
                raise ArtifactError(f"search document {raw['id']!r} has an unsafe URL")
            seen.add(raw["id"])
            documents.append(raw)
        return documents

    def site(self) -> dict[str, Any]:
        site = deepcopy(self._site)
        # The artifact carries a deterministic semantic content ID because a
        # JSON document cannot contain its own byte hash.  The public site
        # contract, however, must report the exact manifest-verified snapshot
        # served by this process.
        site["snapshot"] = self.snapshot_hash
        return site

    def page(self, page_id: str) -> dict[str, Any]:
        value = self._pages.get(page_id)
        if not isinstance(value, dict):
            raise EntityNotFound(page_id)
        return deepcopy(value)

    def ct(self, ct_id: str) -> dict[str, Any]:
        return deepcopy(_canonical_lookup(self._cts, ct_id))

    def route(self, route_id: str) -> dict[str, Any]:
        return deepcopy(_canonical_lookup(self._routes, route_id))

    def example(self, example_id: str) -> dict[str, Any]:
        return deepcopy(_canonical_lookup(self._examples, example_id))

    def erdos_node(self, node_id: str) -> dict[str, Any]:
        return deepcopy(_canonical_lookup(self._erdos_nodes, node_id))

    def module(self, module_id: str) -> dict[str, Any]:
        return deepcopy(_canonical_lookup(self._modules, module_id))

    def declaration(self, declaration_id: str) -> dict[str, Any]:
        return deepcopy(_canonical_lookup(self._declarations, declaration_id))

    def source_excerpt(self, source_id: str, query: SourceExcerptQuery) -> dict[str, Any]:
        source = self._sources.get(source_id)
        if source is None:
            raise EntityNotFound(source_id)
        if _sha256_path(source.path) != source.sha256:
            raise ArtifactError("a published source changed after snapshot generation")
        try:
            content = source.path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as error:
            raise ArtifactError("published source is not readable UTF-8") from error
        lines = content.splitlines()
        total = len(lines)
        start = query.start or 1
        end = query.end or min(total, start + query.default_span - 1)
        if total == 0:
            start, end = 1, 0
        elif start > total:
            raise ValueError("start line exceeds the source length")
        else:
            end = min(end, total)
        if end >= start and end - start + 1 > query.maximum_span:
            raise ValueError(f"source excerpts are limited to {query.maximum_span} lines")
        excerpt = "\n".join(lines[start - 1 : end])
        if error := _public_text_error(excerpt, "source excerpt"):
            raise ArtifactError(error)
        return {
            "sourceId": source.source_id,
            "path": source.relative_path,
            "sha256": source.sha256,
            "startLine": start,
            "endLine": end,
            "totalLines": total,
            "content": excerpt,
        }

    def search(self, query: SearchQuery) -> dict[str, Any]:
        tokens = [match.group(0).casefold() for match in WORD_RE.finditer(query.q)]
        ranked: list[tuple[int, str, str, dict[str, Any]]] = []
        for document in self._search_documents:
            title = str(document.get("title", ""))
            summary = str(document.get("summary", ""))
            body = str(document.get("body", ""))
            keywords = " ".join(str(value) for value in document.get("keywords", []))
            searchable = f"{title} {summary} {body} {keywords}".casefold()
            if any(token not in searchable for token in tokens):
                continue
            score = SEARCH_KIND_PRIOR.get(str(document.get("kind", "")), 0)
            for token in tokens:
                score += min(title.casefold().count(token), 2) * 10
                score += min(summary.casefold().count(token), 2) * 4
                score += min(body.casefold().count(token), 3)
                score += min(keywords.casefold().count(token), 3) * 2
            if query.q and title.casefold() == query.q.casefold().strip():
                score += 100
            ranked.append((score, title.casefold(), document["id"], document))

        kind_counts: dict[str, int] = {}
        module_counts: dict[str, int] = {}
        for _score, _title, _identifier, document in ranked:
            kind = str(document.get("kind", "other"))
            kind_counts[kind] = kind_counts.get(kind, 0) + 1
            module = document.get("module")
            if isinstance(module, str) and module:
                module_counts[module] = module_counts.get(module, 0) + 1

        filtered = [
            item
            for item in ranked
            if (query.kind is None or item[3].get("kind") == query.kind)
            and (query.module is None or item[3].get("module") == query.module)
        ]
        filtered.sort(key=lambda item: (-item[0], item[1], item[2]))
        offset = (query.page - 1) * query.page_size
        page_items = filtered[offset : offset + query.page_size]
        results = [self._search_result(document, tokens) for *_rank, document in page_items]
        facets = [
            {
                "field": "kind",
                "label": kind,
                "value": kind,
                "count": count,
                "active": kind == query.kind,
            }
            for kind, count in sorted(kind_counts.items())
        ]
        ranked_modules = sorted(
            module_counts.items(), key=lambda item: (-item[1], item[0])
        )
        visible_modules = ranked_modules[:12]
        if query.module is not None and query.module in module_counts and not any(
            module == query.module for module, _count in visible_modules
        ):
            visible_modules.append((query.module, module_counts[query.module]))
        facets.extend(
            {
                "field": "module",
                "label": module,
                "value": module,
                "count": count,
                "active": module == query.module,
            }
            for module, count in visible_modules
        )
        return {
            "query": query.q,
            "total": len(filtered),
            "facets": facets,
            "results": results,
            "page": query.page,
            "pageSize": query.page_size,
        }

    @staticmethod
    def _search_result(document: Mapping[str, Any], tokens: list[str]) -> dict[str, Any]:
        summary = str(document.get("summary", document.get("body", "")))
        result: dict[str, Any] = {
            "id": document["id"],
            "title": document["title"],
            "summary": summary[:360],
            "href": document["url"],
            "kind": document["kind"],
            "highlights": [_highlight_fragment(summary, tokens)] if tokens and summary else [],
        }
        module = document.get("module")
        if isinstance(module, str) and module:
            result["module"] = module
        return result


def _highlight_fragment(value: str, tokens: list[str], radius: int = 90) -> str:
    lowered = value.casefold()
    positions = [lowered.find(token) for token in tokens if lowered.find(token) >= 0]
    start = max(0, (min(positions) if positions else 0) - radius)
    end = min(len(value), start + radius * 2)
    fragment = value[start:end]
    escaped = html.escape(fragment)
    for token in sorted(set(tokens), key=len, reverse=True):
        escaped = re.sub(
            re.escape(html.escape(token)),
            lambda match: f"<mark>{match.group(0)}</mark>",
            escaped,
            flags=re.IGNORECASE,
        )
    return ("…" if start else "") + escaped + ("…" if end < len(value) else "")
