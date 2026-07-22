from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path
import re
import sys

import pytest

from tools.update_hypostructure_migration_records import (
    ORIGINAL_EG_PREDECESSORS,
    SourceAuthorityError,
    main as update_migration_records,
    validate_eg_source_authority,
)
from web.backend.app.erdos_topology import CANONICAL_ERDOS_INCOMING_NUMBERS


ROOT = Path(__file__).resolve().parents[1]
AUTHORITY_PATH = ROOT / "migration/hypostructure/source-authority.json"


# Cross-panel continuations are prose-level diagram edges. Each pattern is
# checked against the original diagram before its edge is admitted.
CROSS_PANEL_CONTINUATIONS = (
    (25, 26, r"node \[25\] continues in \\cref\{fig:proof-diagram-part-ii\}"),
    (33, 35, r"the rank-drop branch, closed in Part III"),
    (34, 47, r"the full-rank residual, continued in Part IV"),
    (56, 57, r"The surviving continuation node is the large-budget net-deficiency residual"),
    (64, 65, r"node \[64\] continues in \\cref\{fig:proof-diagram-part-vi\}"),
    (108, 66, r"exit 7 hands off to Type B \[65\] through node \[108\]"),
    (68, 78, r"The degree-\\\(4\\\) no-branch of \[68\] is expanded in \\cref\{fig:proof-diagram-part-vii\}"),
    (63, 86, r"Node \[63\] continues in \\cref\{fig:proof-diagram-part-viii\}"),
    (77, 110, r"\[77\]\}~route-8 cores\\\\continue in Part IX"),
    (109, 110, r"the route-8 residual \[109\], is expanded in \\cref\{fig:proof-diagram-part-ix\}"),
    (20, 125, r"node \[20\] is the continuation expanded in \\cref\{fig:proof-diagram-part-x\}"),
    (24, 145, r"interface behind nodes \[22\]--\[24\]"),
)


def load_authority() -> dict[str, object]:
    return json.loads(AUTHORITY_PATH.read_text(encoding="utf-8"))


LEDGER_FILENAMES = (
    "api-feature-matrix.csv",
    "eg-node-matrix.csv",
    "supplemental-legacy-evidence.csv",
    "pde-row-matrix.csv",
)


def stage_authority_root(
    root: Path,
    authority: dict[str, object],
    original_bytes: bytes,
) -> dict[Path, bytes]:
    output = root / "migration/hypostructure"
    output.mkdir(parents=True)
    (output / "source-authority.json").write_text(
        json.dumps(authority), encoding="utf-8"
    )
    (output / "eg-original-node-anchors.json").write_bytes(
        (ROOT / "migration/hypostructure/eg-original-node-anchors.json").read_bytes()
    )
    (root / "original_erdos_64_proof.tex").write_bytes(original_bytes)

    sentinels: dict[Path, bytes] = {}
    for filename in LEDGER_FILENAMES:
        path = output / filename
        sentinel = f"sentinel:{filename}\n".encode()
        path.write_bytes(sentinel)
        sentinels[path] = sentinel
    return sentinels


def assert_sentinels_unchanged(sentinels: dict[Path, bytes]) -> None:
    assert {path: path.read_bytes() for path in sentinels} == sentinels


def original_diagram_predecessors(source: str) -> dict[int, tuple[int, ...]]:
    diagram = source[
        source.index(r"\subsection*{Proof-dependency diagram}") : source.index(
            r"\subsection*{Detailed dependency table}"
        )
    ]
    blocks = re.findall(
        r"\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}",
        diagram,
        flags=re.DOTALL,
    )
    predecessors = {node_id: set() for node_id in range(1, 158)}
    seen_nodes: set[int] = set()

    for block in blocks:
        aliases = {
            alias: int(node_id)
            for alias, node_id in re.findall(
                r"\\node\[[^\]]+\]\s*\((\w+)\).*?"
                r"\\textbf\{\[(\d+)\]\}",
                block,
            )
        }
        seen_nodes.update(aliases.values())
        for arrow in re.findall(
            r"\\draw\[arrow(?:,[^\]]*)?\](.*?);", block, flags=re.DOTALL
        ):
            path_aliases = [
                alias
                for alias in re.findall(r"\((\w+)(?:\.[^)]+)?\)", arrow)
                if alias in aliases
            ]
            assert len(path_aliases) >= 2
            predecessors[aliases[path_aliases[-1]]].add(aliases[path_aliases[0]])

    assert len(blocks) == 11
    assert seen_nodes == set(range(1, 158))
    for predecessor, node_id, evidence_pattern in CROSS_PANEL_CONTINUATIONS:
        assert re.search(evidence_pattern, diagram), evidence_pattern
        predecessors[node_id].add(predecessor)

    return {
        node_id: tuple(sorted(incoming))
        for node_id, incoming in predecessors.items()
    }


def test_eg_source_authority_manifest_and_pinned_bytes() -> None:
    authority = load_authority()
    assert authority["schema_version"] == 1
    assert authority["scope"] == "erdos-gyarfas-problem-64"

    original = authority["original"]
    assert isinstance(original, dict)
    assert original["role"] == "sole EG mathematical and DAG authority"
    assert original["mathematical_authority"] is True
    assert original["dag_authority"] is True
    assert original["must_not_be_edited"] is True
    assert original["corrections_require_explicit_approval"] is True

    raw = (ROOT / original["path"]).read_bytes()
    assert len(raw) == original["byte_size"]
    assert hashlib.sha256(raw).hexdigest() == original["sha256"]

    living = authority["living_proof"]
    assert isinstance(living, dict)
    assert living["role"] == "non-binding editorial cross-check only"
    assert living["mathematical_authority"] is False
    assert living["dag_authority"] is False

    legacy = authority["legacy_lean"]
    assert isinstance(legacy, dict)
    assert legacy["role"] == "kernel-checked implementation and parity evidence only"
    assert legacy["mathematical_authority"] is False
    assert legacy["dag_authority"] is False

    anchors = authority["original_node_anchor_registry"]
    assert isinstance(anchors, dict)
    assert anchors["path"] == (
        "migration/hypostructure/eg-original-node-anchors.json"
    )
    assert anchors["generator"] == "tools/extract_eg_original_node_anchors.py"
    assert anchors["role"] == (
        "exact diagram locator generated only from the pinned original"
    )
    assert anchors["scope"] == "diagram_anchor_only"
    assert anchors["mathematical_authority"] is False
    assert anchors["full_quantified_contract_reviewed"] is False

    registry = json.loads((ROOT / anchors["path"]).read_text(encoding="ascii"))
    assert registry["scope"] == anchors["scope"]
    assert registry["original"]["path"] == original["path"]
    assert registry["original"]["byte_size"] == original["byte_size"]
    assert registry["original"]["sha256"] == original["sha256"]
    assert registry["claims"]["full_quantified_contract_reviewed"] is False

    workflow = authority["migration_workflow"]
    assert isinstance(workflow, dict)
    assert workflow["requirements_source"] == original["path"]
    assert workflow["first_step"].startswith("extract and freeze")
    assert "legacy NodeX.lean" in workflow["second_step"]
    assert workflow["discrepancy_policy"].startswith("record an issue and block")
    assert living["path"] in workflow["prohibited_requirements_sources"]


def test_updater_preflight_accepts_the_repository_authority() -> None:
    validate_eg_source_authority(ROOT)


def test_updater_rejects_altered_original_before_any_ledger_write(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    original_bytes = bytearray((ROOT / "original_erdos_64_proof.tex").read_bytes())
    original_bytes[0] ^= 1
    sentinels = stage_authority_root(
        tmp_path, load_authority(), bytes(original_bytes)
    )
    monkeypatch.setattr(
        sys, "argv", ["update_hypostructure_migration_records.py", "--root", str(tmp_path)]
    )

    with pytest.raises(SourceAuthorityError, match=r"original_erdos_64_proof\.tex sha256"):
        update_migration_records()

    assert_sentinels_unchanged(sentinels)


def test_updater_rejects_bad_workflow_before_any_ledger_write(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    authority = load_authority()
    workflow = authority["migration_workflow"]
    assert isinstance(workflow, dict)
    workflow["first_step"] = "consult legacy implementation before the original"
    sentinels = stage_authority_root(
        tmp_path,
        authority,
        (ROOT / "original_erdos_64_proof.tex").read_bytes(),
    )
    monkeypatch.setattr(
        sys, "argv", ["update_hypostructure_migration_records.py", "--root", str(tmp_path)]
    )

    with pytest.raises(SourceAuthorityError, match=r"migration_workflow\.first_step"):
        update_migration_records()

    assert_sentinels_unchanged(sentinels)


def test_updater_rejects_drifted_anchor_registry_before_any_ledger_write(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    sentinels = stage_authority_root(
        tmp_path,
        load_authority(),
        (ROOT / "original_erdos_64_proof.tex").read_bytes(),
    )
    anchor_path = (
        tmp_path / "migration/hypostructure/eg-original-node-anchors.json"
    )
    anchors = json.loads(anchor_path.read_text(encoding="ascii"))
    anchors["nodes"][0]["byte_start"] += 1
    anchor_path.write_text(json.dumps(anchors, indent=2) + "\n", encoding="ascii")
    monkeypatch.setattr(
        sys,
        "argv",
        ["update_hypostructure_migration_records.py", "--root", str(tmp_path)],
    )

    with pytest.raises(SourceAuthorityError, match="does not match the pinned original"):
        update_migration_records()

    assert_sentinels_unchanged(sentinels)


def test_every_eg_migration_row_names_the_original_as_its_requirement_source() -> None:
    matrix = ROOT / "migration/hypostructure/eg-node-matrix.csv"
    with matrix.open(newline="", encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream))

    assert [int(row["node_id"]) for row in rows] == list(range(1, 158))
    assert all(
        row["paper_ref"] ==
        f"original_erdos_64_proof.tex node {row['node_id']}"
        for row in rows
    )


def test_all_eg_topology_maps_equal_the_original_diagram() -> None:
    source = (ROOT / "original_erdos_64_proof.tex").read_text(encoding="utf-8")
    original_map = original_diagram_predecessors(source)

    assert ORIGINAL_EG_PREDECESSORS == original_map
    assert dict(CANONICAL_ERDOS_INCOMING_NUMBERS) == original_map
