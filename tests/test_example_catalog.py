from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from tools.render_example_catalog import (
    ExampleCatalogError,
    hydrate_example,
    render_example_catalog,
    trusted_source_path,
)


ROOT = Path(__file__).resolve().parents[1]
CATALOG = json.loads((ROOT / "generated/lean-machines.json").read_text())
ROOT_MODULES = {
    "EvenCycleExample": "even-cycle",
    "Erdos64EG": "erdos-64",
    "GreedyColoringExample": "greedy-coloring",
    "MantelExample": "mantel",
}


def declaration(module: str, name: str | None = None) -> dict:
    return {
        "name": name or f"{module}.synthetic",
        "kind": "definition",
        "type": "True",
        "module": module,
        "sourceFile": module.replace(".", "/") + ".lean",
        "range": {
            "start": {"line": 1, "column": 0},
            "end": {"line": 1, "column": 0},
        },
        "selectionRange": {
            "start": {"line": 1, "column": 0},
            "end": {"line": 1, "column": 0},
        },
    }


def raw_example(root_module: str, example_id: str) -> dict:
    return {
        "artifactType": "structuralExhaustionExample",
        "schemaVersion": "1.0.0",
        "sourceOfTruth": {
            "kind": "compiledLeanEnvironment",
            "rootModule": root_module,
            "descriptor": f"{root_module}.WebExport.descriptor",
        },
        "example": {
            "exampleId": example_id,
            "title": f"{root_module} example",
            "summary": "Synthetic renderer fixture.",
            "proofStatus": "complete",
            "workflows": [
                {
                    "workflowId": "main",
                    "title": "Main workflow",
                    "purpose": "Exercise deterministic hydration.",
                    "completion": "complete",
                    "stages": [
                        {
                            "stageId": "main.problem",
                            "title": "Problem",
                            "summary": "The compiled problem declaration.",
                            "kind": "problem",
                            "tacticId": None,
                            "primaryDeclaration": declaration(root_module),
                            "evidenceDeclarations": [],
                        }
                    ],
                    "links": [],
                }
            ],
            "interfaceBindings": [],
        },
    }


def generated_files(root: Path) -> dict[str, bytes]:
    directory = root / "generated/examples"
    return {
        path.relative_to(directory).as_posix(): path.read_bytes()
        for path in sorted(directory.glob("*.json"))
    }


def test_renderer_is_byte_deterministic_and_hashes_exact_details(tmp_path: Path) -> None:
    raw_root = tmp_path / "raw"
    raw_root.mkdir()
    for root_module, example_id in ROOT_MODULES.items():
        (raw_root / f"{example_id}.json").write_text(
            json.dumps(raw_example(root_module, example_id)), encoding="utf-8"
        )

    first = tmp_path / "first"
    second = tmp_path / "second"
    first_index = render_example_catalog(
        raw_root=raw_root,
        output_root=first,
        source_root=ROOT,
        catalog_path=ROOT / "generated/lean-machines.json",
    )
    second_index = render_example_catalog(
        raw_root=raw_root,
        output_root=second,
        source_root=ROOT,
        catalog_path=ROOT / "generated/lean-machines.json",
    )

    assert first_index == second_index
    assert generated_files(first) == generated_files(second)
    for summary in first_index["examples"]:
        detail = first / "generated/examples" / summary["detailFile"]
        assert hashlib.sha256(detail.read_bytes()).hexdigest() == summary["detailHash"]


def test_renderer_rejects_links_outside_their_workflow() -> None:
    raw = raw_example("EvenCycleExample", "even-cycle")
    workflow = raw["example"]["workflows"][0]
    workflow["links"].append(
        {
            "linkId": "main.dangling",
            "sourceStageId": "main.problem",
            "targetStageId": "missing",
            "kind": "proofData",
            "label": "dangling",
            "description": "This endpoint is not declared.",
            "routeId": None,
            "evidenceDeclarations": [],
        }
    )
    with pytest.raises(ExampleCatalogError, match="endpoints must belong"):
        hydrate_example(raw, ROOT, CATALOG)


def test_renderer_checks_registered_route_tactic_endpoints() -> None:
    raw = raw_example("EvenCycleExample", "even-cycle")
    workflow = raw["example"]["workflows"][0]
    workflow["stages"] = [
        {
            "stageId": "main.ct1",
            "title": "Wrong source",
            "summary": "CT1 cannot source the registered CT6 route.",
            "kind": "tactic",
            "tacticId": "CT1",
            "primaryDeclaration": declaration("EvenCycleExample", "EvenCycleExample.ct1"),
            "evidenceDeclarations": [],
        },
        {
            "stageId": "main.ct9",
            "title": "CT9",
            "summary": "The target tactic.",
            "kind": "tactic",
            "tacticId": "CT9",
            "primaryDeclaration": declaration("EvenCycleExample", "EvenCycleExample.ct9"),
            "evidenceDeclarations": [],
        },
    ]
    workflow["links"] = [
        {
            "linkId": "main.route",
            "sourceStageId": "main.ct1",
            "targetStageId": "main.ct9",
            "kind": "registeredRoute",
            "label": "invalid source",
            "description": "The declared source tactic does not own this residual.",
            "routeId": "CT6.residual.activeLedger->CT9",
            "evidenceDeclarations": [],
        }
    ]
    with pytest.raises(ExampleCatalogError, match="expects CT6 -> CT9"):
        hydrate_example(raw, ROOT, CATALOG)


def test_trusted_source_resolution_rejects_symlink_escape(tmp_path: Path) -> None:
    package_root = tmp_path / "examples/even_cycle"
    package_root.mkdir(parents=True)
    outside = tmp_path / "outside.lean"
    outside.write_text("def escaped := true\n", encoding="utf-8")
    (package_root / "EvenCycleExample.lean").symlink_to(outside)

    with pytest.raises(ExampleCatalogError, match="escapes trusted package root"):
        trusted_source_path(declaration("EvenCycleExample"), tmp_path)


def test_committed_example_artifacts_validate_and_hash_sources() -> None:
    examples_root = ROOT / "generated/examples"
    index = json.loads((examples_root / "index.json").read_text(encoding="utf-8"))
    index_schema = json.loads(
        (ROOT / "schemas/example-index.schema.json").read_text(encoding="utf-8")
    )
    detail_schema = json.loads(
        (ROOT / "schemas/example-detail.schema.json").read_text(encoding="utf-8")
    )
    assert list(Draft202012Validator(index_schema).iter_errors(index)) == []
    assert [item["exampleId"] for item in index["examples"]] == sorted(
        ROOT_MODULES.values()
    )

    for summary in index["examples"]:
        detail_path = examples_root / summary["detailFile"]
        detail_bytes = detail_path.read_bytes()
        assert hashlib.sha256(detail_bytes).hexdigest() == summary["detailHash"]
        detail = json.loads(detail_bytes)
        assert list(Draft202012Validator(detail_schema).iter_errors(detail)) == []
        for source in detail["sources"]:
            assert not Path(source["path"]).is_absolute()
            assert ".." not in Path(source["path"]).parts
            assert hashlib.sha256(source["content"].encode("utf-8")).hexdigest() == source["sha256"]
            assert (ROOT / source["path"]).read_text(encoding="utf-8") == source["content"]
