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
from tools.render_manuscript_fragments import (
    ManuscriptRenderError,
    _sanitize_svg,
    render_manuscript_fragments,
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
        "schemaVersion": "1.2.0",
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
            "manuscript": None,
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
            "automationDeclarations": [],
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
            "automationDeclarations": [],
            "evidenceDeclarations": [],
        }
    ]
    with pytest.raises(ExampleCatalogError, match="expects CT6 -> CT9"):
        hydrate_example(raw, ROOT, CATALOG)


def cross_ct_fixture() -> tuple[dict, dict]:
    raw = raw_example("EvenCycleExample", "even-cycle")
    workflow = raw["example"]["workflows"][0]
    workflow["stages"] = [
        {
            "stageId": "main.ct10",
            "title": "CT10",
            "summary": "A compiled CT10 stage.",
            "kind": "tactic",
            "tacticId": "CT10",
            "primaryDeclaration": declaration(
                "EvenCycleExample", "EvenCycleExample.ct10"
            ),
            "evidenceDeclarations": [],
        },
        {
            "stageId": "main.ct6",
            "title": "CT6",
            "summary": "A compiled CT6 stage.",
            "kind": "tactic",
            "tacticId": "CT6",
            "primaryDeclaration": declaration(
                "EvenCycleExample", "EvenCycleExample.ct6"
            ),
            "evidenceDeclarations": [],
        },
    ]
    link = {
        "linkId": "main.ct10-ct6",
        "sourceStageId": "main.ct10",
        "targetStageId": "main.ct6",
        "kind": "frameworkComposition",
        "label": "compiled transition",
        "description": "The framework executes the next CT.",
        "routeId": None,
        "automationDeclarations": [],
        "evidenceDeclarations": [],
    }
    workflow["links"] = [link]
    return raw, link


def test_renderer_rejects_cross_ct_transition_without_framework_automation() -> None:
    raw, _ = cross_ct_fixture()
    with pytest.raises(
        ExampleCatalogError, match="cross-CT transition has no framework automation"
    ):
        hydrate_example(raw, ROOT, CATALOG)


def test_renderer_rejects_example_local_transition_automation() -> None:
    raw, link = cross_ct_fixture()
    link["automationDeclarations"] = [
        declaration("EvenCycleExample", "EvenCycleExample.localExecutor")
    ]
    with pytest.raises(ExampleCatalogError, match="is not framework-owned"):
        hydrate_example(raw, ROOT, CATALOG)


def manuscript_for_single_stage(raw: dict) -> dict:
    stage = raw["example"]["workflows"][0]["stages"][0]
    return {
        "title": "Synthetic manuscript mapping",
        "path": "proofs/erdos_64_eg/erdos_64_proof.tex",
        "formalizedNodeIds": [1],
        "proofSteps": [
            {
                "stepId": "main.statement",
                "stageId": stage["stageId"],
                "title": "Statement",
                "plainExplanation": "Explains the synthetic statement.",
                "formalStatement": "P \\Longrightarrow P",
                "status": "implemented",
                "correspondence": "support",
                "manuscriptRefs": [
                    {"label": "thm:main", "title": "Main closure", "nodeIds": [1]}
                ],
                "declarationGroups": [
                    {
                        "groupId": "statement",
                        "title": "Statement declaration",
                        "role": "mathematicalDefinition",
                        "explanation": "The displayed declaration states the proposition.",
                        "declarations": [stage["primaryDeclaration"]],
                    }
                ],
                "scopeNotes": "Synthetic support mapping.",
                "workBound": "No computation.",
            }
        ],
    }


def test_renderer_validates_manuscript_labels_nodes_and_complete_coverage() -> None:
    raw = raw_example("EvenCycleExample", "even-cycle")
    raw["example"]["manuscript"] = manuscript_for_single_stage(raw)
    detail = hydrate_example(raw, ROOT, CATALOG)
    coverage = detail["manuscript"]["coverage"]
    assert {
        key: coverage[key]
        for key in (
            "implementedSteps",
            "totalSteps",
            "explainedDeclarations",
            "displayedDeclarations",
            "verifiedMathematicalObjects",
            "verifiedDiagramNodes",
            "verifiedWorkflowSteps",
        )
    } == {
        "implementedSteps": 1,
        "totalSteps": 1,
        "explainedDeclarations": 1,
        "displayedDeclarations": 1,
        "verifiedMathematicalObjects": 1,
        "verifiedDiagramNodes": 1,
        "verifiedWorkflowSteps": 1,
    }
    assert coverage["totalMathematicalObjects"] >= 1
    assert coverage["totalDiagramNodes"] >= 1
    assert detail["manuscript"]["sha256"] == hashlib.sha256(
        (ROOT / detail["manuscript"]["path"]).read_bytes()
    ).hexdigest()
    fragment = detail["manuscript"]["fragments"][0]
    assert fragment["label"] == "thm:main"
    assert fragment["environment"] == "theorem"
    assert fragment["includesProof"] is True
    assert [block["environment"] for block in fragment["blocks"]] == [
        "theorem",
        "proof",
    ]
    assert "".join(
        inline.get("text", " ")
        for inline in fragment["blocks"][0]["title"]
    ) == "Main closure"

    def walk(value: object):
        if isinstance(value, dict):
            yield value
            for child in value.values():
                yield from walk(child)
        elif isinstance(value, list):
            for child in value:
                yield from walk(child)

    first_reference = next(
        node for node in walk(fragment["blocks"]) if node.get("kind") == "reference"
    )
    assert first_reference["labels"] == ["lem:return-equivalence"]
    assert first_reference["prefix"] == "lemma"

    raw["example"]["manuscript"]["proofSteps"][0]["manuscriptRefs"][0][
        "label"
    ] = "lem:does-not-exist"
    with pytest.raises(ExampleCatalogError, match="unknown manuscript label"):
        hydrate_example(raw, ROOT, CATALOG)


def test_renderer_exports_a_complete_section_and_checked_tikz_figure() -> None:
    manuscript = render_manuscript_fragments(
        path="proofs/erdos_64_eg/erdos_64_proof.tex",
        source_root=ROOT,
        requested_labels=["sec:remainder"],
    )
    fragment = manuscript["fragments"][0]
    assert fragment["environment"] == "section"
    assert fragment["includesProof"] is False
    figures = [block for block in fragment["blocks"] if block["kind"] == "figure"]
    assert [figure["label"] for figure in figures] == ["fig:p13-remainder-ledger"]
    assert figures[0]["svg"].startswith("<")
    assert hashlib.sha256(figures[0]["svg"].encode("utf-8")).hexdigest() == figures[0][
        "svgSha256"
    ]


def test_manuscript_renderer_rejects_active_svg_content() -> None:
    with pytest.raises(ManuscriptRenderError, match="unsupported element script"):
        _sanitize_svg(
            '<svg xmlns="http://www.w3.org/2000/svg"><script>alert(1)</script></svg>',
            "fig:unsafe",
        )


def test_renderer_rejects_unexplained_displayed_declarations() -> None:
    raw = raw_example("EvenCycleExample", "even-cycle")
    raw["example"]["manuscript"] = manuscript_for_single_stage(raw)
    raw["example"]["manuscript"]["proofSteps"][0]["declarationGroups"] = []
    with pytest.raises(ExampleCatalogError, match="declaration coverage mismatch"):
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
        if detail["manuscript"] is not None:
            manuscript = detail["manuscript"]
            assert hashlib.sha256((ROOT / manuscript["path"]).read_bytes()).hexdigest() == manuscript[
                "sha256"
            ]
            referenced = {
                reference["label"]
                for step in manuscript["proofSteps"]
                for reference in step["manuscriptRefs"]
            }
            assert {fragment["label"] for fragment in manuscript["fragments"]} == referenced
            rendered = render_manuscript_fragments(
                path=manuscript["path"],
                source_root=ROOT,
                requested_labels=[],
            )
            implemented = [
                step for step in manuscript["proofSteps"]
                if step["status"] == "implemented"
            ]
            fragment_kinds = {
                fragment["label"]: fragment["environment"]
                for fragment in manuscript["fragments"]
            }
            verified_objects = {
                reference["label"]
                for step in implemented
                for reference in step["manuscriptRefs"]
                if fragment_kinds[reference["label"]] in {
                    "theorem", "lemma", "proposition", "corollary",
                    "claim", "definition", "remark",
                }
            }
            assert manuscript["coverage"] == {
                "implementedSteps": len(implemented),
                "totalSteps": len(manuscript["proofSteps"]),
                "explainedDeclarations": len(detail["declarations"]),
                "displayedDeclarations": len(detail["declarations"]),
                "verifiedMathematicalObjects": len(verified_objects),
                "totalMathematicalObjects": len(
                    rendered["mathematicalObjectLabels"]
                ),
                "verifiedDiagramNodes": len(manuscript["formalizedNodeIds"]),
                "totalDiagramNodes": len(rendered["nodeIds"]),
                "verifiedWorkflowSteps": len(implemented),
            }
