"""FastAPI entry point for the structural-exhaustion framework explorer."""

from __future__ import annotations

from contextlib import asynccontextmanager
import mimetypes
from pathlib import Path
from typing import AsyncIterator

from fastapi import FastAPI, HTTPException
from fastapi.responses import Response

from .models import (
    ExampleResponse,
    ExamplesResponse,
    FrameworkResponse,
    HealthResponse,
    TacticInternalsResponse,
    TacticResponse,
)
from .repository import ArtifactRepository


def _static_response(path: Path) -> Response:
    media_type, _ = mimetypes.guess_type(path.name)
    return Response(
        content=path.read_bytes(),
        media_type=media_type or "application/octet-stream",
    )


def create_app(
    repository: ArtifactRepository | None = None,
    dist_dir: Path | None = None,
) -> FastAPI:
    artifacts = repository or ArtifactRepository()
    frontend = (dist_dir or artifacts.root / "build/web").resolve()

    @asynccontextmanager
    async def lifespan(app: FastAPI) -> AsyncIterator[None]:
        app.state.artifacts = artifacts
        yield

    app = FastAPI(
        title="Structural Exhaustion Framework Explorer",
        version="0.1.0",
        lifespan=lifespan,
    )

    @app.get("/api/v1/health", response_model=HealthResponse)
    async def health() -> dict:
        return {
            "status": "ok",
            "artifactType": "frameworkExplorerHealth",
            "artifactWarnings": artifacts.artifact_warnings,
            "catalog": artifacts.catalog_view,
            "verification": artifacts.verification_status,
            "tacticCount": len(artifacts.tactics),
            "exampleCount": len(artifacts.examples),
        }

    @app.get("/api/v1/framework", response_model=FrameworkResponse)
    async def framework() -> dict:
        return artifacts.framework_response()

    @app.get("/api/v1/tactics/{tactic_id}", response_model=TacticResponse)
    async def tactic(tactic_id: str) -> dict:
        response = artifacts.tactic_response(tactic_id.upper())
        if response is None:
            raise HTTPException(status_code=404, detail=f"Unknown tactic {tactic_id}")
        return response

    @app.get(
        "/api/v1/tactics/{tactic_id}/internals",
        response_model=TacticInternalsResponse,
    )
    async def tactic_internals(tactic_id: str) -> dict:
        response = artifacts.tactic_internals_response(tactic_id.upper())
        if response is None:
            raise HTTPException(status_code=404, detail=f"Unknown tactic {tactic_id}")
        return response

    @app.get("/api/v1/examples", response_model=ExamplesResponse)
    async def examples() -> dict:
        return artifacts.examples_response()

    @app.get("/api/v1/examples/{example_id}", response_model=ExampleResponse)
    async def example(example_id: str) -> dict:
        response = artifacts.example_response(example_id)
        if response is None:
            raise HTTPException(
                status_code=404, detail=f"Unknown example {example_id}"
            )
        return response

    @app.get("/{full_path:path}", include_in_schema=False)
    async def frontend_file(full_path: str) -> Response:
        candidate = (frontend / full_path).resolve()
        if candidate != frontend and frontend not in candidate.parents:
            raise HTTPException(status_code=404, detail="Not found")
        if candidate.is_file():
            return _static_response(candidate)
        if Path(full_path).suffix:
            raise HTTPException(status_code=404, detail="Not found")
        index = frontend / "index.html"
        if not index.is_file():
            raise HTTPException(
                status_code=503,
                detail="Frontend build not found; run make web-build",
            )
        return _static_response(index)

    return app


app = create_app()
