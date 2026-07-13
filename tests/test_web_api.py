from __future__ import annotations

import asyncio
from pathlib import Path

import httpx2

from web.backend.app.main import create_app
from web.backend.app.repository import (
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
        "residualKinds": 36,
        "routes": 5,
        "manualObligations": 0,
    }
    assert [item["tacticId"] for item in response["tactics"]] == [
        f"CT{number}" for number in range(1, 18)
    ]
    assert all(
        repository.graphs[tactic_id]["tacticId"] == tactic_id
        for tactic_id in repository.tactics
    )
    assert {route["sourceTacticId"] for route in response["routes"]} == {
        "CT1",
        "CT2",
        "CT6",
    }


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
        link
        for example_id in ("greedy-coloring", "mantel", "erdos-64")
        for workflow in repository.examples[example_id]["workflows"]
        for link in workflow["links"]
        if link["kind"] == "registeredRoute"
    ]
    assert other_registered == []


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
            assert framework.json()["totals"]["routes"] == 5

            tactic = await get("/api/v1/tactics/ct6")
            assert tactic.status_code == 200
            assert tactic.json()["tactic"]["tacticId"] == "CT6"
            assert tactic.json()["graph"]["tacticId"] == "CT6"

            missing = await get("/api/v1/tactics/CT99")
            assert missing.status_code == 404

            examples = await get("/api/v1/examples")
            assert examples.status_code == 200
            assert len(examples.json()["examples"]) == 4

            example = await get("/api/v1/examples/even-cycle")
            assert example.status_code == 200
            assert example.json()["example"]["proofStatus"] == "complete"
            assert "content" in example.json()["example"]["sources"][0]

            missing_example = await get("/api/v1/examples/not-an-example")
            assert missing_example.status_code == 404

            deep_link = await get("/ct/CT6")
            assert deep_link.status_code == 200
            assert "framework explorer" in deep_link.text

            example_deep_link = await get("/examples/even-cycle")
            assert example_deep_link.status_code == 200
            assert "framework explorer" in example_deep_link.text

            asset = await get("/assets/app.js")
            assert asset.status_code == 200
            assert "explorer" in asset.text

            missing_asset = await get("/assets/missing.js")
            assert missing_asset.status_code == 404

    asyncio.run(exercise_api())
