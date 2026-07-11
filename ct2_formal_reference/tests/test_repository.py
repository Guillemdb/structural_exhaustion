from __future__ import annotations

import subprocess
import sys
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools.verify_lean import (
    checked_declaration_types,
    version_from_lean_output,
    version_from_toolchain,
)
from tools.generate_binding_check import (
    render_binding_check,
    render_cytoscape,
    render_node_index,
)


def test_repository_validator() -> None:
    result = subprocess.run(
        [sys.executable, "tools/validate_repository.py"],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_version_parsing() -> None:
    assert version_from_toolchain("leanprover/lean4:v4.31.0") == "4.31.0"
    assert (
        version_from_lean_output(
            "Lean (version 4.31.0, x86_64-unknown-linux-gnu, Release)"
        )
        == "4.31.0"
    )


def test_multiline_check_output_parsing() -> None:
    output = """\
Example.first.{u_1} (alpha : Type u_1) :
  alpha → alpha
Example.second : Prop
"""
    assert checked_declaration_types(output) == {
        "Example.first": "(alpha : Type u_1) : alpha → alpha",
        "Example.second": "Prop",
    }


def test_graph_artifacts_are_generated_views() -> None:
    assert (ROOT / "StructuralExhaustion/Generated/BindingCheck.lean").read_text() == render_binding_check(ROOT)
    for tactic_id in (f"CT{number}" for number in range(1, 18)):
        stem = tactic_id.lower()
        assert (ROOT / f"generated/{stem}-node-index.csv").read_text() == render_node_index(ROOT, tactic_id)
        assert (ROOT / f"generated/{stem}.cytoscape.json").read_text() == render_cytoscape(ROOT, tactic_id)


def test_semantic_graph_paths_have_typed_edges() -> None:
    manifest = json.loads((ROOT / "manifest.json").read_text())
    instances = [json.loads((ROOT / ref).read_text()) for ref in manifest["instances"]]
    for record in manifest["tactics"]:
        tactic_path = ROOT / record["specRef"]
        tactic = json.loads(tactic_path.read_text())
        nodes = {
            node["nodeId"]: node
            for node in (
                json.loads((tactic_path.parent / ref).read_text())
                for ref in tactic["nodeRefs"]
            )
        }
        edges = {edge["transitionId"]: edge for edge in tactic["transitions"]}
        assert nodes[tactic["entryNodeId"]]["nodeKind"] == "entry"
        assert {
            node["terminal"]["terminalCase"]
            for node in nodes.values()
            if node["nodeKind"] == "terminal"
        } == set(tactic["terminalCases"])
        assert all(
            edge["transitionConstructorRef"]["declarationKind"] == "constructor"
            for edge in edges.values()
        )
        assert all(
            edge["guard"]["kind"] == "unconditional"
            or (
                edge["guard"]["resultConstructorRef"]["declarationKind"] == "constructor"
                and edge["guard"]["evidenceSlots"]
            )
            for edge in edges.values()
        )
        for instance in (item for item in instances if item["tacticId"] == record["tacticId"]):
            assert len(instance["expectedNodePath"]) == len(instance["expectedEdgePath"]) + 1
            for source, edge_id, target in zip(
                instance["expectedNodePath"],
                instance["expectedEdgePath"],
                instance["expectedNodePath"][1:],
            ):
                assert edges[edge_id]["fromNodeId"] == source
                assert edges[edge_id]["toNodeId"] == target


def test_ct1_is_the_declared_staged_machine() -> None:
    tactic = json.loads((ROOT / "framework/CT1/tactic.json").read_text())
    assert len(tactic["nodeRefs"]) == 13
    assert len(tactic["transitions"]) == 12
    assert set(tactic["terminalCases"]) == {
        "scope", "c1", "ct2", "ct3", "ct4", "ct5", "ct6", "ct17"
    }
    certification = [
        edge for edge in tactic["transitions"]
        if edge["fromNodeId"] == "CT1.certify.equivalence"
    ]
    assert len(certification) == 1
    assert certification[0]["guard"]["kind"] == "unconditional"
    assert certification[0]["guard"]["evidenceSlots"][0]["typeExpression"].endswith(
        "EquivalenceState framework input"
    )


def test_ct3_through_ct17_are_declared_staged_machines() -> None:
    expected = {
        "CT3": (13, 12, {"scope", "c2", "c3", "c5", "ct7", "ct12", "ct8"}),
        "CT4": (11, 10, {"scope", "ct13", "ct9", "c4", "ct14"}),
        "CT5": (11, 10, {"scope", "ct11", "c4", "ct4", "ct14"}),
        "CT6": (13, 12, {"scope", "ct4", "c1", "ct3", "ct7", "ct9", "ct10"}),
        "CT7": (15, 14, {"scope", "c1", "c3", "ct3", "ct12", "c2", "ct10", "ct16"}),
        "CT8": (12, 11, {"scope", "ct10", "c5", "c2", "ct3", "ct7"}),
        "CT9": (12, 11, {"scope", "ct10", "ct4", "c1", "ct7", "ct8"}),
        "CT10": (12, 12, {"scope", "c5", "ct3", "ct7", "ct15"}),
        "CT11": (11, 10, {"scope", "ct10", "ct1", "ct7", "ct14"}),
        "CT12": (11, 11, {"scope", "c4", "ct4", "ct13"}),
        "CT13": (14, 13, {"scope", "ct4", "c4", "ct9", "ct14"}),
        "CT14": (9, 8, {"scope", "ct9", "ct10", "c4"}),
        "CT15": (13, 12, {"scope", "ct3", "ct7", "ct16", "c4", "ct4"}),
        "CT16": (9, 8, {"ct3", "scope", "c2", "ct10"}),
        "CT17": (15, 14, {"scope", "ct3", "ct10", "c5", "ct8", "c1", "ct14"}),
    }
    for tactic_id, (nodes, transitions, terminals) in expected.items():
        tactic = json.loads((ROOT / f"framework/{tactic_id}/tactic.json").read_text())
        assert len(tactic["nodeRefs"]) == nodes
        assert len(tactic["transitions"]) == transitions
        assert set(tactic["terminalCases"]) == terminals
        formal_nodes = [
            json.loads((ROOT / f"framework/{tactic_id}" / ref).read_text())
            for ref in tactic["nodeRefs"]
        ]
        certification_ids = {
            node["nodeId"] for node in formal_nodes if node["nodeKind"] == "certification"
        }
        for node_id in certification_ids:
            outgoing = [edge for edge in tactic["transitions"] if edge["fromNodeId"] == node_id]
            assert len(outgoing) == 1
            assert outgoing[0]["guard"]["kind"] == "unconditional"
            assert outgoing[0]["guard"]["evidenceSlots"]


def test_all_kernel_verification_records_pass() -> None:
    for tactic_id in (f"ct{number}" for number in range(1, 18)):
        result = json.loads((ROOT / f"generated/{tactic_id}-lean-verification.json").read_text())
        assert result["status"] == "kernel_checked"
        assert all(status == "passed" for status in result["aggregateResults"].values())
