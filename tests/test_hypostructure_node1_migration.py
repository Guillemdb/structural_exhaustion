import csv
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_nodes_1_to_13_reviewed_status_stays_honest_without_clean_baseline() -> None:
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
        3: {
            "paper_ref": "original_erdos_64_proof.tex node 3",
            "direct_predecessors": "2",
            "normalized_input": "node 2 residual",
            "normalized_outcomes": "not a counterexample terminal",
        },
        4: {
            "paper_ref": "original_erdos_64_proof.tex node 4",
            "direct_predecessors": "2",
            "normalized_input": "node 2 residual",
            "normalized_outcomes": "lexicographically minimal counterexample",
        },
        5: {
            "paper_ref": "original_erdos_64_proof.tex node 5",
            "direct_predecessors": "4",
            "normalized_input": "node 4 residual",
            "normalized_outcomes": "edge-rooted target algebra",
        },
        6: {
            "paper_ref": "original_erdos_64_proof.tex node 6",
            "direct_predecessors": "5",
            "normalized_input": "node 5 residual",
            "normalized_outcomes": "Mersenne return decision",
        },
        7: {
            "paper_ref": "original_erdos_64_proof.tex node 7",
            "direct_predecessors": "6",
            "normalized_input": "node 6 residual",
            "normalized_outcomes": "power-of-two cycle terminal",
        },
        8: {
            "paper_ref": "original_erdos_64_proof.tex node 8",
            "direct_predecessors": "6",
            "normalized_input": "node 6 residual",
            "normalized_outcomes": "no proper minimum-degree-three subgraph",
        },
        9: {
            "paper_ref": "original_erdos_64_proof.tex node 9",
            "direct_predecessors": "8",
            "normalized_input": "node 8 residual",
            "normalized_outcomes": "edge-deletion criticality",
        },
        10: {
            "paper_ref": "original_erdos_64_proof.tex node 10",
            "direct_predecessors": "9",
            "normalized_input": "node 9 residual",
            "normalized_outcomes": "high-degree vertices independent",
        },
        11: {
            "paper_ref": "original_erdos_64_proof.tex node 11",
            "direct_predecessors": "10",
            "normalized_input": "node 10 residual",
            "normalized_outcomes": "boundaried atoms and degree profile",
        },
        12: {
            "paper_ref": "original_erdos_64_proof.tex node 12",
            "direct_predecessors": "11",
            "normalized_input": "node 11 residual",
            "normalized_outcomes": (
                "context-universal target-complete identifications"
            ),
        },
        13: {
            "paper_ref": "original_erdos_64_proof.tex node 13",
            "direct_predecessors": "12",
            "normalized_input": "node 12 residual",
            "normalized_outcomes": "boundaried replacement",
        },
    }

    for node_id, fields in expected.items():
        node = rows[node_id]
        for key, value in fields.items():
            assert node[key] == value
        assert node["new_kernel"] == "fresh"
        if node_id == 13:
            assert node["parity_status"] == "checked"
            assert node["math_status"] == "open"
            assert node["status"] == "migrated_open"
            assert node["blocker"] == (
                "original Node 13 boundary-overlap implication is false under "
                "stated union gluing; overlap-count preservation remains a "
                "recorded residual"
            )
        else:
            assert node["parity_status"] == "not_run"
            assert node["math_status"] == "closed"
            assert node["status"] == "typechecked"
            assert node["blocker"] == "semantic parity baseline not frozen"
        assert node["work_status"] == "captured"
        assert node["web_evidence"] == "generated/hypostructure/web/snapshot.json"


def test_nodes_1_to_13_web_presentation_uses_direct_native_evidence_without_closure() -> None:
    snapshot = json.loads(
        (ROOT / "generated/hypostructure/web/snapshot.json").read_text(
            encoding="utf-8"
        )
    )
    nodes = {
        int(node["number"]): node
        for node in snapshot["erdos"]["nodes"]
    }
    for node_id in (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12):
        node = nodes[node_id]
        assert node["new_kernel"] == "fresh"
        assert node["math_status"] == "closed"
        assert node["work_status"] == "captured"
        assert node["direct_kernel_fresh"] is True
        assert node["has_compiled_direct_declaration"] is True
        assert node["closed"] is False
        assert node["presentation_status"] == "implemented"
        assert node["blocker"] == "semantic parity baseline not frozen"

    node13 = nodes[13]
    assert node13["new_kernel"] == "fresh"
    assert node13["math_status"] == "open"
    assert node13["work_status"] == "captured"
    assert node13["direct_kernel_fresh"] is True
    assert node13["has_compiled_direct_declaration"] is True
    assert node13["closed"] is False
    assert node13["presentation_status"] == "implemented"
    assert "overlap-count preservation" in node13["blocker"]
