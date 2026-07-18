from __future__ import annotations

import asyncio
import hashlib
import json
from pathlib import Path

import httpx2
import pytest

from web.backend.app.main import create_app
from web.backend.app.repository import (
    ArtifactError,
    _validate_manuscript_svg,
    _validate_tactic_graph,
    ArtifactRepository,
    example_verification_view,
    verification_view,
)


ROOT = Path(__file__).resolve().parents[1]


def test_artifact_repository_projects_the_generated_framework() -> None:
    repository = ArtifactRepository(ROOT)
    response = repository.framework_response()

    assert response["totals"] == {
        "tactics": 17,
        "nodes": 124,
        "transitions": 108,
        "terminals": 55,
        "residualKinds": 37,
        "routes": 9,
        "implementedTransitions": 33,
        "manualObligations": 0,
    }
    assert [item["tacticId"] for item in response["tactics"]] == [
        f"CT{number}" for number in range(1, 18)
    ]
    assert all(
        repository.graphs[tactic_id]["tacticId"] == tactic_id
        for tactic_id in repository.tactics
    )
    assert repository._internals == {}
    detail = repository.tactic_internals_response("CT6")
    assert detail is not None
    assert detail["internals"]["tacticId"] == "CT6"
    assert len(detail["internals"]["nodes"]) == len(repository.tactics["CT6"]["nodes"])
    assert detail["internals"]["sources"]
    assert set(repository._internals) == {"CT6"}
    assert "internalDeclarations" not in repository.tactic_response("CT6")["tactic"]
    assert {route["sourceTacticId"] for route in response["routes"]} == {
        "CT1",
        "CT2",
        "CT5",
        "CT6",
        "CT9",
        "CT14",
    }
    assert response["exampleVerification"]["exampleCatalogHash"] == (
        response["exampleCatalog"]["catalogHash"]
    )
    assert response["exampleVerification"]["state"] in {"verified", "stale"}
    assert [
        (
            transition["exampleId"],
            transition["sourceTacticId"],
            transition["targetTacticId"],
            transition["relationshipKind"],
        )
        for transition in response["implementedTransitions"]
    ] == [
        ("erdos-64", "CT1", "CT2", "frameworkComposition"),
        ("erdos-64", "CT2", "CT3", "frameworkComposition"),
        ("erdos-64", "CT3", "CT1", "frameworkComposition"),
        ("erdos-64", "CT1", "CT12", "registeredRoute"),
        ("erdos-64", "CT12", "CT10", "frameworkComposition"),
        ("erdos-64", "CT3", "CT15", "frameworkComposition"),
        ("erdos-64", "CT10", "CT6", "frameworkComposition"),
        ("erdos-64", "CT6", "CT9", "registeredRoute"),
        ("erdos-64", "CT9", "CT1", "sharedProblem"),
        ("erdos-64", "CT1", "CT10", "sharedProblem"),
        ("erdos-64", "CT10", "CT9", "sharedProblem"),
        ("erdos-64", "CT9", "CT7", "registeredRoute"),
        ("erdos-64", "CT7", "CT5", "sharedProblem"),
        ("erdos-64", "CT5", "CT7", "sharedProblem"),
        ("erdos-64", "CT7", "CT10", "sharedProblem"),
        ("erdos-64", "CT10", "CT5", "sharedProblem"),
        ("erdos-64", "CT10", "CT14", "frameworkComposition"),
        ("erdos-64", "CT14", "CT12", "frameworkComposition"),
        ("erdos-64", "CT12", "CT14", "frameworkComposition"),
        ("erdos-64", "CT5", "CT2", "sharedProblem"),
        ("erdos-64", "CT2", "CT1", "frameworkComposition"),
        ("erdos-64", "CT1", "CT10", "frameworkComposition"),
        ("erdos-64", "CT10", "CT9", "sharedProblem"),
        ("erdos-64", "CT9", "CT5", "sharedProblem"),
        ("erdos-64", "CT5", "CT14", "registeredRoute"),
        ("erdos-64", "CT14", "CT1", "frameworkComposition"),
        ("erdos-64", "CT1", "CT9", "frameworkComposition"),
        ("erdos-64", "CT9", "CT14", "frameworkComposition"),
            ("erdos-64", "CT12", "CT15", "frameworkComposition"),
            ("erdos-64", "CT15", "CT9", "frameworkComposition"),
            ("erdos-64", "CT9", "CT10", "frameworkComposition"),
            ("even-cycle", "CT6", "CT9", "registeredRoute"),
        ("greedy-coloring", "CT12", "CT4", "scheduleAudit"),
    ]
    assert all(
        transition["frameworkAutomated"]
        and transition["automationDeclarationIds"]
        for transition in response["implementedTransitions"]
    )
    ct10_to_ct6 = next(
        transition
        for transition in response["implementedTransitions"]
        if transition["sourceTacticId"] == "CT10"
        and transition["targetTacticId"] == "CT6"
    )
    assert ct10_to_ct6["exampleId"] == "erdos-64"
    assert ct10_to_ct6["linkId"] == "proof-slice.labels-surplus-ct6"
    assert ct10_to_ct6["automationClass"] == "frameworkExecutor"
    assert ct10_to_ct6["automationDeclarationIds"] == [
        "StructuralExhaustion.Graph.SurplusPortActivity.run"
    ]
    assert ct10_to_ct6["evidenceDeclarationIds"] == [
        "Erdos64EG.Internal.verifiedSparseSurplusPrefix",
        "Erdos64EG.Internal.VerifiedSparseSurplusPrefix.previous",
    ]


def test_artifact_repository_projects_all_compiled_examples() -> None:
    repository = ArtifactRepository(ROOT)
    response = repository.examples_response()

    assert [item["exampleId"] for item in response["examples"]] == [
        "erdos-64",
        "even-cycle",
        "greedy-coloring",
        "mantel",
    ]
    assert response["examples"][0]["proofStatus"] == "partial"
    assert response["examples"][1]["workflowCount"] >= 3

    even_cycle = repository.example_response("even-cycle")
    assert even_cycle is not None
    registered = [
        link
        for workflow in even_cycle["example"]["workflows"]
        for link in workflow["links"]
        if link["kind"] == "registeredRoute"
    ]
    assert [link["routeId"] for link in registered] == [
        "CT6.residual.activeLedger->CT9"
    ]

    other_registered = [
        (example_id, link["routeId"])
        for example_id in ("greedy-coloring", "mantel", "erdos-64")
        for workflow in repository.examples[example_id]["workflows"]
        for link in workflow["links"]
        if link["kind"] == "registeredRoute"
    ]
    assert other_registered == [
        ("erdos-64", "CT1.terminal.c1->CT12"),
        ("erdos-64", "CT6.residual.activeLedger->CT9"),
        ("erdos-64", "CT9.residual.overload->CT7"),
        ("erdos-64", "CT5.residual.chargeLedger->CT14"),
        ("erdos-64", "CT14.residual.capacity->CT14"),
    ]

    erdos = repository.examples["erdos-64"]
    manuscript = erdos["manuscript"]
    referenced = {
        reference["label"]
        for step in manuscript["proofSteps"]
        for reference in step["manuscriptRefs"]
    }
    assert {fragment["label"] for fragment in manuscript["fragments"]} == referenced
    assert any(
        block["kind"] == "figure"
        for fragment in manuscript["fragments"]
        for block in fragment["blocks"]
    )


def test_artifact_repository_rejects_a_stale_manuscript_projection() -> None:
    repository = ArtifactRepository(ROOT)
    detail = json.loads(json.dumps(repository.examples["erdos-64"]))
    detail["manuscript"]["sha256"] = "0" * 64

    with pytest.raises(ArtifactError, match="manuscript hash is stale"):
        repository._validate_example_detail(detail)


def test_web_dev_mode_warns_and_serves_a_stale_manuscript_projection(
    caplog: pytest.LogCaptureFixture,
) -> None:
    repository = ArtifactRepository(ROOT, allow_stale_hashes=True)
    detail = json.loads(json.dumps(repository.examples["erdos-64"]))
    detail["manuscript"]["sha256"] = "0" * 64

    with caplog.at_level("WARNING", logger="structural_exhaustion.web"):
        repository._validate_example_detail(detail)

    warning = repository.artifact_warnings[-1]
    assert warning["code"] == "staleHash"
    assert "manuscript hash is stale" in warning["message"]
    assert "STALE ARTIFACT" in caplog.text
    assert repository.example_response("erdos-64")["artifactWarnings"] == [warning]


def test_artifact_repository_rejects_unsafe_manuscript_svg_styles() -> None:
    repository = ArtifactRepository(ROOT)
    figure = next(
        block
        for fragment in repository.examples["erdos-64"]["manuscript"]["fragments"]
        for block in fragment["blocks"]
        if block["kind"] == "figure"
    )
    svg = figure["svg"].replace(
        "</ns0:svg>",
        "<style>path { fill: url(https://example.invalid/paint); }</style></ns0:svg>",
    )

    with pytest.raises(ArtifactError, match="unsafe SVG style content"):
        _validate_manuscript_svg(
            figure["label"], svg, hashlib.sha256(svg.encode("utf-8")).hexdigest()
        )


def test_internal_artifact_must_match_the_compiled_node_flow(tmp_path: Path) -> None:
    repository = ArtifactRepository(ROOT)
    original = json.loads(repository.internal_paths["CT1"].read_text(encoding="utf-8"))
    original["nodes"][0]["internalFlow"]["steps"][0]["label"] = "tampered"
    tampered = tmp_path / "CT1.json"
    tampered.write_text(json.dumps(original), encoding="utf-8")
    repository.internal_paths["CT1"] = tampered

    with pytest.raises(ArtifactError, match="disagree with compiled flow"):
        repository.tactic_internals_response("CT1")


def test_cytoscape_transition_must_match_the_compiled_edge() -> None:
    repository = ArtifactRepository(ROOT)
    graph = json.loads(json.dumps(repository.graphs["CT1"]))
    transition = next(
        element["data"]
        for element in graph["elements"]
        if element["data"].get("kind") == "ctTransition"
    )
    transition["label"] = "hidden-or-renamed-transition"

    with pytest.raises(ArtifactError, match="transitions disagree"):
        _validate_tactic_graph(repository.tactics["CT1"], graph)


def test_verification_view_distinguishes_fresh_stale_and_failed() -> None:
    base = {"toolchain": {}, "aggregate": {}}
    assert verification_view(
        "a" * 64,
        {**base, "status": "kernel_checked", "catalogHash": "a" * 64},
    )["state"] == "verified"
    assert verification_view(
        "a" * 64,
        {**base, "status": "kernel_checked", "catalogHash": "b" * 64},
    )["state"] == "stale"
    assert verification_view(
        "a" * 64,
        {**base, "status": "failed", "catalogHash": "a" * 64},
    )["state"] == "failed"

    assert example_verification_view(
        "c" * 64,
        {**base, "status": "kernel_checked", "exampleCatalogHash": "c" * 64},
    )["state"] == "verified"
    assert example_verification_view(
        "c" * 64,
        {**base, "status": "kernel_checked", "exampleCatalogHash": "d" * 64},
    )["state"] == "stale"


def test_api_and_spa_are_served_from_one_application(tmp_path: Path) -> None:
    (tmp_path / "assets").mkdir()
    (tmp_path / "index.html").write_text("<main>framework explorer</main>")
    (tmp_path / "assets/app.js").write_text("console.log('explorer')")
    app = create_app(ArtifactRepository(ROOT), tmp_path)

    async def exercise_api() -> None:
        transport = httpx2.ASGITransport(app=app)
        async with httpx2.AsyncClient(
            transport=transport, base_url="http://testserver"
        ) as client:
            async def get(path: str) -> httpx2.Response:
                return await client.get(path)

            health = await get("/api/v1/health")
            assert health.status_code == 200
            assert health.json()["tacticCount"] == 17
            assert health.json()["exampleCount"] == 4

            framework = await get("/api/v1/framework")
            assert framework.status_code == 200
            assert framework.json()["totals"]["routes"] == 9
            assert framework.json()["totals"]["implementedTransitions"] == 33
            assert any(
                transition["sourceTacticId"] == "CT10"
                and transition["targetTacticId"] == "CT6"
                for transition in framework.json()["implementedTransitions"]
            )

            tactic = await get("/api/v1/tactics/ct6")
            assert tactic.status_code == 200
            assert tactic.json()["tactic"]["tacticId"] == "CT6"
            assert tactic.json()["graph"]["tacticId"] == "CT6"
            assert "internalDeclarations" not in tactic.json()["tactic"]

            internals = await get("/api/v1/tactics/ct6/internals")
            assert internals.status_code == 200
            assert internals.json()["artifactType"] == "frameworkExplorerTacticInternals"
            assert internals.json()["internals"]["tacticId"] == "CT6"
            assert internals.json()["internals"]["sources"]

            missing = await get("/api/v1/tactics/CT99")
            assert missing.status_code == 404
            missing_internals = await get("/api/v1/tactics/CT99/internals")
            assert missing_internals.status_code == 404

            examples = await get("/api/v1/examples")
            assert examples.status_code == 200
            assert len(examples.json()["examples"]) == 4

            example = await get("/api/v1/examples/even-cycle")
            assert example.status_code == 200
            assert example.json()["example"]["proofStatus"] == "complete"
            assert "content" in example.json()["example"]["sources"][0]

            erdos = await get("/api/v1/examples/erdos-64")
            assert erdos.status_code == 200
            assert erdos.json()["example"]["schemaVersion"] == "1.4.0"
            assert erdos.json()["example"]["manuscript"]["fragments"]
            assert erdos.json()["example"]["manuscript"]["coverage"]["verifiedDiagramNodes"] == 39
            assert erdos.json()["example"]["manuscript"]["coverage"]["totalDiagramNodes"] == 157

            missing_example = await get("/api/v1/examples/not-an-example")
            assert missing_example.status_code == 404

            deep_link = await get("/ct/CT6")
            assert deep_link.status_code == 200
            assert "framework explorer" in deep_link.text

            example_deep_link = await get("/examples/even-cycle")
            assert example_deep_link.status_code == 200
            assert "framework explorer" in example_deep_link.text

            erdos_deep_link = await get("/erdos-gyarfas")
            assert erdos_deep_link.status_code == 200
            assert "framework explorer" in erdos_deep_link.text

            asset = await get("/assets/app.js")
            assert asset.status_code == 200
            assert "explorer" in asset.text

            missing_asset = await get("/assets/missing.js")
            assert missing_asset.status_code == 404

    asyncio.run(exercise_api())
