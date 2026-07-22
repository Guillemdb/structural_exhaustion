import csv
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_node1_and_node2_reviewed_status_stays_honest_without_clean_baseline() -> None:
    baseline_manifest = ROOT / "migration/hypostructure/baseline/manifest.json"
    assert not baseline_manifest.exists()

    with (ROOT / "migration/hypostructure/eg-node-matrix.csv").open(
        encoding="utf-8", newline=""
    ) as handle:
        rows = {
            int(row["node_id"]): row
            for row in csv.DictReader(handle)
        }

    expected = {
        1: {
            "paper_ref": "original_erdos_64_proof.tex node 1",
            "direct_predecessors": "",
            "normalized_input": "root",
            "normalized_outcomes": "finite simple graph G",
        },
        2: {
            "paper_ref": "original_erdos_64_proof.tex node 2",
            "direct_predecessors": "1",
            "normalized_input": "node 1 residual",
            "normalized_outcomes": "counterexample decision",
        },
    }

    for node_id, fields in expected.items():
        node = rows[node_id]
        for key, value in fields.items():
            assert node[key] == value
        assert node["new_kernel"] == "fresh"
        assert node["parity_status"] == "not_run"
        assert node["math_status"] == "closed"
        assert node["work_status"] == "captured"
        assert node["status"] == "typechecked"
        assert node["web_evidence"] == "generated/hypostructure/web/snapshot.json"
        assert node["blocker"] == "semantic parity baseline not frozen"


def test_node1_and_node2_web_presentation_uses_direct_native_evidence_without_closure() -> None:
    snapshot = json.loads(
        (ROOT / "generated/hypostructure/web/snapshot.json").read_text(
            encoding="utf-8"
        )
    )
    nodes = {
        int(node["number"]): node
        for node in snapshot["erdos"]["nodes"]
    }
    for node_id in (1, 2):
        node = nodes[node_id]
        assert node["new_kernel"] == "fresh"
        assert node["math_status"] == "closed"
        assert node["work_status"] == "captured"
        assert node["direct_kernel_fresh"] is True
        assert node["has_compiled_direct_declaration"] is True
        assert node["closed"] is False
        assert node["presentation_status"] == "implemented"
        assert node["blocker"] == "semantic parity baseline not frozen"
