from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from web.backend.app.main import create_app
from web.backend.app.erdos_topology import CANONICAL_ERDOS_INCOMING_NUMBERS
from web.backend.app.repository import ArtifactError, SnapshotRepository


def _write_snapshot(
    root: Path,
    *,
    forbidden_text: bool = False,
    public_summary: str | None = None,
) -> Path:
    source_path = root / "hypostructure/Hypostructure/Core/Problem.lean"
    source_path.parent.mkdir(parents=True)
    source_path.write_text(
        "namespace Hypostructure\n\nstructure Problem where\n  Ambient : Type\n\nend Hypostructure\n",
        encoding="utf-8",
    )
    source_hash = hashlib.sha256(source_path.read_bytes()).hexdigest()
    page = {
        "id": "home",
        "title": "Hypostructure",
        "summary": "A verified proof-program framework",
        "breadcrumbs": [],
        "metrics": [],
        "sections": [
            {
                "id": "introduction",
                "title": "Introduction",
                "blocks": [{"kind": "prose", "html": "<p>Verified content.</p>"}],
            }
        ],
    }
    page_ids = (
        "home",
        "start",
        "core",
        "graph",
        "pde",
        "examples",
        "erdos",
        "cts",
        "routes",
        "reference",
    )
    erdos_nodes = [
        {
            "id": f"node-{number}",
            "title": "Root registration" if number == 1 else f"Erdős node {number}",
            "summary": "Register the root." if number == 1 else "Canonical paper node.",
            "sections": [],
            "number": number,
            "incoming": [f"node-{value}" for value in predecessors],
            "label": f"Node {number}",
            "url": f"/erdos/nodes/node-{number}",
        }
        for number, predecessors in CANONICAL_ERDOS_INCOMING_NUMBERS.items()
    ]
    erdos_edges = [
        {
            "id": f"node-{predecessor}-to-{number}",
            "source": f"node-{predecessor}",
            "target": f"node-{number}",
            "label": "direct predecessor",
        }
        for number, predecessors in CANONICAL_ERDOS_INCOMING_NUMBERS.items()
        for predecessor in predecessors
    ]
    snapshot = {
        "schema_version": "2.0.0",
        "site": {
            "name": "Hypostructure",
            "tagline": "Proof programs",
            "navigation": [{"label": "Home", "href": "/"}],
            "searchEnabled": True,
            "verification": {
                "state": "verified",
                "label": "Verified",
                "summary": "Kernel checked",
            },
        },
        "pages": {
            page_id: {
                **page,
                "id": page_id,
                "title": (
                    "Hypostructure"
                    if page_id == "home"
                    else "CT chooser"
                    if page_id == "cts"
                    else page_id.title()
                ),
            }
            for page_id in page_ids
        },
        "modules": [
            {
                "id": "Hypostructure.Core.Problem",
                "title": "Core.Problem",
                "summary": "Core problem registration.",
                "sections": [],
            }
        ],
        "declarations": [
            {
                "id": "Hypostructure.Core.Problem",
                "title": "Problem",
                "summary": "Core problem registration.",
                "sections": [],
                "signature": "structure Problem",
                "sourceId": "core-problem",
            }
        ],
        "cts": [
            {
                "id": f"CT{number}",
                "title": "Target realization" if number == 1 else f"CT{number}",
                "summary": f"Executable CT{number} contract.",
                "sections": [],
            }
            for number in range(1, 18)
        ],
        "routes": [
            {
                "id": "ct1-to-ct2",
                "title": "CT1 to CT2",
                "summary": "Typed route.",
                "sections": [],
            }
        ],
        "examples": [
            {
                "id": "neutral",
                "title": "Neutral fixture",
                "summary": "A neutral example.",
                "sections": [],
            }
        ],
        "erdos": {
            "id": "erdos",
            "title": "Erdős case study",
            "summary": "A typed proof program.",
            "nodes": erdos_nodes,
            "edges": erdos_edges,
            "root_node_ids": ["node-1"],
            "graph": {
                "kind": "graph",
                "nodes": [
                    {
                        "id": node["id"],
                        "label": node["label"],
                        "x": (node["number"] - 1) % 20,
                        "y": (node["number"] - 1) // 20,
                        "kind": "application",
                        "summary": node["summary"],
                        "href": node["url"],
                    }
                    for node in erdos_nodes
                ],
                "edges": [dict(edge) for edge in erdos_edges],
            },
        },
        "sources": [
            {
                "id": "core-problem",
                "path": "hypostructure/Hypostructure/Core/Problem.lean",
                "sha256": source_hash,
                "module": "Hypostructure.Core.Problem",
                "layer": "core",
                "kind": "source",
            }
        ],
        "search_documents": [
            {
                "id": "decl-problem",
                "title": "Problem",
                "summary": "Register ambient data and a branch state.",
                "body": "The Core problem keeps the target external.",
                "url": "/reference/declarations/Hypostructure.Core.Problem",
                "kind": "declaration",
                "module": "Hypostructure.Core.Problem",
            },
            {
                "id": "ct1",
                "title": "CT1 target realization",
                "summary": "Find a target or return exact avoidance.",
                "body": "Finite candidate target scan.",
                "url": "/core/cts/CT1",
                "kind": "ct",
                "module": "Hypostructure.CT1",
            },
        ],
        "trust": {"state": "verified", "summary": "Kernel checked"},
    }
    if forbidden_text:
        snapshot["pages"]["home"]["summary"] = "A migration status page"
    if public_summary is not None:
        snapshot["pages"]["home"]["summary"] = public_summary

    artifact_dir = root / "generated/hypostructure/web"
    artifact_dir.mkdir(parents=True)
    snapshot_bytes = json.dumps(
        snapshot, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    (artifact_dir / "snapshot.json").write_bytes(snapshot_bytes)
    manifest = {
        "schema_version": "2.0.0",
        "snapshot_sha256": hashlib.sha256(snapshot_bytes).hexdigest(),
        "counts": {
            "pages": 10,
            "cts": 17,
            "routes": 1,
            "examples": 1,
            "erdos_nodes": 157,
            "modules": 1,
            "declarations": 1,
            "sources": 1,
            "search_documents": 2,
        },
        "sources": [
            {
                "id": "core-problem",
                "path": "hypostructure/Hypostructure/Core/Problem.lean",
                "sha256": source_hash,
            }
        ],
    }
    (artifact_dir / "manifest.json").write_text(
        json.dumps(manifest), encoding="utf-8"
    )
    return artifact_dir


def _rewrite_snapshot(artifact_dir: Path, snapshot: dict[str, object]) -> None:
    snapshot_bytes = json.dumps(
        snapshot, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    (artifact_dir / "snapshot.json").write_bytes(snapshot_bytes)
    manifest_path = artifact_dir / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["snapshot_sha256"] = hashlib.sha256(snapshot_bytes).hexdigest()
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")


def _client(tmp_path: Path):
    artifact_dir = _write_snapshot(tmp_path)
    dist = tmp_path / "build/web"
    (dist / "assets").mkdir(parents=True)
    (dist / "index.html").write_text("<main>Hypostructure</main>", encoding="utf-8")
    (dist / "assets/app.js").write_text("console.log('app')", encoding="utf-8")
    (dist / "assets/app.abcdef12.js").write_text(
        "console.log('hashed')", encoding="utf-8"
    )
    repository = SnapshotRepository(tmp_path, artifact_dir)
    return create_app(repository, dist).test_client(), repository


def test_checked_in_snapshot_loads_against_current_published_sources() -> None:
    """The generated artifact must be deployable, not merely schema-valid."""

    repository = SnapshotRepository(Path(__file__).resolve().parents[1])

    assert repository.counts["cts"] == 17
    assert repository.counts["erdos_nodes"] == 157
    assert repository.site()["snapshot"] == repository.snapshot_hash


def test_snapshot_repository_fails_closed_on_stale_or_unpublishable_data(
    tmp_path: Path,
) -> None:
    artifact_dir = _write_snapshot(tmp_path)
    snapshot_path = artifact_dir / "snapshot.json"
    snapshot_path.write_bytes(snapshot_path.read_bytes() + b"\n")
    with pytest.raises(ArtifactError, match="snapshot is stale"):
        SnapshotRepository(tmp_path, artifact_dir)

    second = tmp_path / "forbidden"
    forbidden_dir = _write_snapshot(second, forbidden_text=True)
    with pytest.raises(ArtifactError, match="forbidden publish-facing term"):
        SnapshotRepository(second, forbidden_dir)

    parity_root = tmp_path / "mathematical-parity"
    parity_dir = _write_snapshot(
        parity_root,
        public_summary="CT9 detects parity-label fibre overload.",
    )
    assert SnapshotRepository(parity_root, parity_dir).page("home")["summary"].startswith(
        "CT9"
    )


def test_snapshot_sources_are_limited_to_current_production_roots(
    tmp_path: Path,
) -> None:
    artifact_dir = _write_snapshot(tmp_path)
    outside = tmp_path / "examples/current_app/Problem.lean"
    outside.parent.mkdir(parents=True)
    outside.write_text("namespace CurrentApp\n", encoding="utf-8")
    outside_hash = hashlib.sha256(outside.read_bytes()).hexdigest()

    snapshot_path = artifact_dir / "snapshot.json"
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    snapshot["sources"][0]["path"] = "examples/current_app/Problem.lean"
    snapshot["sources"][0]["sha256"] = outside_hash
    snapshot_bytes = json.dumps(
        snapshot, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    snapshot_path.write_bytes(snapshot_bytes)

    manifest_path = artifact_dir / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["snapshot_sha256"] = hashlib.sha256(snapshot_bytes).hexdigest()
    manifest["sources"][0]["path"] = "examples/current_app/Problem.lean"
    manifest["sources"][0]["sha256"] = outside_hash
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")

    with pytest.raises(ArtifactError, match="JSON Schema|outside publishable roots"):
        SnapshotRepository(tmp_path, artifact_dir)


def test_nested_snapshot_corruption_is_rejected_by_bundled_schema(
    tmp_path: Path,
) -> None:
    artifact_dir = _write_snapshot(tmp_path)
    snapshot_path = artifact_dir / "snapshot.json"
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    snapshot["pages"]["home"]["sections"][0]["blocks"][0]["html"] = 42
    snapshot_bytes = json.dumps(
        snapshot, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    snapshot_path.write_bytes(snapshot_bytes)
    manifest_path = artifact_dir / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["snapshot_sha256"] = hashlib.sha256(snapshot_bytes).hexdigest()
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")

    with pytest.raises(ArtifactError, match="does not satisfy its JSON Schema"):
        SnapshotRepository(tmp_path, artifact_dir)


def test_schema_rejects_a_truncated_erdos_topology(tmp_path: Path) -> None:
    artifact_dir = _write_snapshot(tmp_path)
    snapshot_path = artifact_dir / "snapshot.json"
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    snapshot["erdos"]["nodes"] = snapshot["erdos"]["nodes"][:1]
    snapshot["erdos"]["edges"] = []
    snapshot["erdos"]["graph"]["nodes"] = snapshot["erdos"]["graph"]["nodes"][:1]
    snapshot["erdos"]["graph"]["edges"] = []
    _rewrite_snapshot(artifact_dir, snapshot)

    with pytest.raises(ArtifactError, match="does not satisfy its JSON Schema"):
        SnapshotRepository(tmp_path, artifact_dir)


def test_schema_requires_node_one_as_the_sole_erdos_root(tmp_path: Path) -> None:
    artifact_dir = _write_snapshot(tmp_path)
    snapshot_path = artifact_dir / "snapshot.json"
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    snapshot["erdos"]["root_node_ids"] = ["node-1", "node-2"]
    _rewrite_snapshot(artifact_dir, snapshot)

    with pytest.raises(ArtifactError, match="does not satisfy its JSON Schema"):
        SnapshotRepository(tmp_path, artifact_dir)


def test_runtime_rejects_a_different_erdos_relation_with_canonical_counts(
    tmp_path: Path,
) -> None:
    artifact_dir = _write_snapshot(tmp_path)
    snapshot_path = artifact_dir / "snapshot.json"
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    replacement = {
        "id": "node-3-to-2",
        "source": "node-3",
        "target": "node-2",
        "label": "direct predecessor",
    }
    snapshot["erdos"]["edges"][0] = replacement
    snapshot["erdos"]["graph"]["edges"][0] = dict(replacement)
    snapshot["erdos"]["nodes"][1]["incoming"] = ["node-3"]
    _rewrite_snapshot(artifact_dir, snapshot)

    with pytest.raises(ArtifactError, match="incorrect predecessors|canonical"):
        SnapshotRepository(tmp_path, artifact_dir)


def test_runtime_rejects_an_erdos_display_graph_that_disagrees_with_nodes(
    tmp_path: Path,
) -> None:
    artifact_dir = _write_snapshot(tmp_path)
    snapshot_path = artifact_dir / "snapshot.json"
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    snapshot["erdos"]["graph"]["nodes"][0]["label"] = "Wrong node"
    _rewrite_snapshot(artifact_dir, snapshot)

    with pytest.raises(ArtifactError, match="display graph label disagrees"):
        SnapshotRepository(tmp_path, artifact_dir)


@pytest.mark.parametrize(
    "href",
    [
        None,
        "https://example.com",
        "//example.com",
        "/\\example.com",
        "/core\njavascript:alert(1)",
        "/core<script>",
    ],
)
def test_site_navigation_requires_a_safe_internal_href(
    tmp_path: Path, href: str | None
) -> None:
    artifact_dir = _write_snapshot(tmp_path)
    snapshot_path = artifact_dir / "snapshot.json"
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    snapshot["site"]["navigation"][0]["href"] = href
    _rewrite_snapshot(artifact_dir, snapshot)

    with pytest.raises(ArtifactError, match="does not satisfy its JSON Schema"):
        SnapshotRepository(tmp_path, artifact_dir)


def test_site_navigation_href_is_required(tmp_path: Path) -> None:
    artifact_dir = _write_snapshot(tmp_path)
    snapshot_path = artifact_dir / "snapshot.json"
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    del snapshot["site"]["navigation"][0]["href"]
    _rewrite_snapshot(artifact_dir, snapshot)

    with pytest.raises(ArtifactError, match="does not satisfy its JSON Schema"):
        SnapshotRepository(tmp_path, artifact_dir)


def test_callout_contract_accepts_a_semantic_nonempty_item_list(tmp_path: Path) -> None:
    artifact_dir = _write_snapshot(tmp_path)
    snapshot_path = artifact_dir / "snapshot.json"
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    snapshot["pages"]["home"]["sections"][0]["blocks"].append(
        {
            "kind": "callout",
            "tone": "warning",
            "title": "Check every branch",
            "body": "The executor owns the outcome split.",
            "items": ["Handle the terminal.", "Handle the residual."],
        }
    )
    _rewrite_snapshot(artifact_dir, snapshot)

    repository = SnapshotRepository(tmp_path, artifact_dir)

    callout = repository.page("home")["sections"][0]["blocks"][-1]
    assert callout["items"] == ["Handle the terminal.", "Handle the residual."]


def test_callout_contract_rejects_an_empty_item_list(tmp_path: Path) -> None:
    artifact_dir = _write_snapshot(tmp_path)
    snapshot_path = artifact_dir / "snapshot.json"
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    snapshot["pages"]["home"]["sections"][0]["blocks"].append(
        {
            "kind": "callout",
            "tone": "warning",
            "title": "Check every branch",
            "body": "The executor owns the outcome split.",
            "items": [],
        }
    )
    _rewrite_snapshot(artifact_dir, snapshot)

    with pytest.raises(ArtifactError, match="does not satisfy its JSON Schema"):
        SnapshotRepository(tmp_path, artifact_dir)


def test_flask_api_serves_page_oriented_snapshot_and_etags(tmp_path: Path) -> None:
    client, repository = _client(tmp_path)

    live = client.get("/api/v2/health/live")
    assert live.status_code == 200
    assert live.json == {"service": "hypostructure-web", "status": "ok"}

    ready = client.get("/api/v2/health/ready")
    assert ready.status_code == 200
    assert ready.json["snapshotHash"] == repository.snapshot_hash
    assert ready.json["counts"]["cts"] == 17

    site = client.get("/api/v2/site")
    assert site.status_code == 200
    assert site.json["snapshot"] == ready.json["snapshotHash"]

    endpoints = {
        "/api/v2/site": "Hypostructure",
        "/api/v2/pages/home": "Hypostructure",
        "/api/v2/pages/reference": "Reference",
        "/api/v2/pages/routes": "Routes",
        "/api/v2/pages/cts": "CT chooser",
        "/api/v2/cts/ct1": "Target realization",
        "/api/v2/routes/ct1-to-ct2": "CT1 to CT2",
        "/api/v2/examples/neutral": "Neutral fixture",
        "/api/v2/erdos/nodes/node-1": "Root registration",
        "/api/v2/reference/modules/Hypostructure.Core.Problem": "Core.Problem",
        "/api/v2/reference/declarations/Hypostructure.Core.Problem": "Problem",
    }
    for endpoint, title in endpoints.items():
        response = client.get(endpoint)
        assert response.status_code == 200, endpoint
        assert response.json.get("title", response.json.get("name")) == title
        assert response.headers["ETag"].startswith('"')
        cached = client.get(endpoint, headers={"If-None-Match": response.headers["ETag"]})
        assert cached.status_code == 304
        assert cached.data == b""


def test_search_is_ranked_filtered_paginated_and_validated_server_side(
    tmp_path: Path,
) -> None:
    client, _repository = _client(tmp_path)

    response = client.get("/api/v2/search?q=target")
    assert response.status_code == 200
    assert response.json["total"] == 2
    assert response.json["results"][0]["id"] == "ct1"
    assert "<mark>target</mark>" in response.json["results"][0]["highlights"][0]

    filtered = client.get("/api/v2/search?q=target&kind=declaration&page_size=1")
    assert filtered.status_code == 200
    assert filtered.json["total"] == 1
    assert filtered.json["results"][0]["kind"] == "declaration"
    assert any(facet["active"] for facet in filtered.json["facets"])
    assert {facet["field"] for facet in filtered.json["facets"]} == {
        "kind",
        "module",
    }

    by_module = client.get(
        "/api/v2/search?q=target&module=Hypostructure.Core.Problem"
    )
    assert by_module.status_code == 200
    assert by_module.json["total"] == 1
    assert any(
        facet["active"] and facet["field"] == "module"
        for facet in by_module.json["facets"]
    )

    invalid = client.get("/api/v2/search?page=0&unexpected=value")
    assert invalid.status_code == 400
    assert invalid.content_type == "application/problem+json"
    assert invalid.json["status"] == 400


def test_source_excerpt_is_allowlisted_bounded_and_reverified(tmp_path: Path) -> None:
    client, repository = _client(tmp_path)

    excerpt = client.get("/api/v2/sources/core-problem/excerpt?start=2&end=4")
    assert excerpt.status_code == 200
    assert excerpt.json["startLine"] == 2
    assert excerpt.json["endLine"] == 4
    assert "structure Problem" in excerpt.json["content"]

    missing = client.get("/api/v2/sources/unknown/excerpt")
    assert missing.status_code == 404
    reversed_range = client.get(
        "/api/v2/sources/core-problem/excerpt?start=4&end=2"
    )
    assert reversed_range.status_code == 400
    overridden_limit = client.get(
        "/api/v2/sources/core-problem/excerpt?maximum_span=100000"
    )
    assert overridden_limit.status_code == 400

    repository._sources["core-problem"].path.write_text("tampered", encoding="utf-8")
    stale = client.get("/api/v2/sources/core-problem/excerpt")
    assert stale.status_code == 503
    assert stale.content_type == "application/problem+json"


def test_api_errors_and_spa_are_served_from_one_origin(tmp_path: Path) -> None:
    client, _repository = _client(tmp_path)

    missing = client.get("/api/v2/cts/CT99")
    assert missing.status_code == 404
    assert missing.content_type == "application/problem+json"
    assert missing.json["instance"] == "/api/v2/cts/CT99"

    deep_link = client.get("/core/cts/CT1")
    assert deep_link.status_code == 200
    assert b"Hypostructure" in deep_link.data
    unknown_client_route = client.get("/not-a-real-page")
    assert unknown_client_route.status_code == 404
    assert b"Hypostructure" in unknown_client_route.data
    asset = client.get("/assets/app.js")
    assert asset.status_code == 200
    assert asset.headers["Cache-Control"] == "public, max-age=3600"
    hashed_asset = client.get("/assets/app.abcdef12.js")
    assert hashed_asset.status_code == 200
    assert hashed_asset.headers["Cache-Control"] == (
        "public, max-age=31536000, immutable"
    )
    missing_asset = client.get("/assets/missing.js")
    assert missing_asset.status_code == 404

    index = client.get("/")
    assert index.headers["Cache-Control"] == "no-cache"
    for header in (
        "Content-Security-Policy",
        "Permissions-Policy",
        "Referrer-Policy",
        "X-Content-Type-Options",
        "X-Frame-Options",
    ):
        assert header in index.headers


def test_missing_snapshot_keeps_liveness_but_not_readiness(tmp_path: Path) -> None:
    app = create_app(root=tmp_path, artifact_dir=tmp_path / "missing")
    client = app.test_client()

    assert client.get("/api/v2/health/live").status_code == 200
    ready = client.get("/api/v2/health/ready")
    assert ready.status_code == 503
    assert ready.content_type == "application/problem+json"
    assert client.get("/api/v2/pages/home").status_code == 503
