from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
ORIGINAL_PATH = ROOT / "original_erdos_64_proof.tex"
REGISTRY_PATH = ROOT / "migration/hypostructure/eg-original-node-anchors.json"
EXTRACTOR_PATH = ROOT / "tools/extract_eg_original_node_anchors.py"
ORIGINAL_SHA256 = (
    "215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10"
)
DIAGRAM_START_MARKER = b"\\subsection*{Proof-dependency diagram}"
DIAGRAM_END_MARKER = b"\\subsection*{Detailed dependency table}"
NODE_LINE = re.compile(rb"(?m)^(\\node[^\r\n]*;)$")
NODE_ID = re.compile(rb"\\textbf\{\[([0-9]+)\]\}")
SCOPE_NOTE = (
    "This registry anchors only node identity and each displayed proof-dependency "
    "diagram statement. It does not claim that normalized_input, "
    "normalized_outcomes, or any node's full quantified contract has been "
    "reviewed. Before implementation, read the definitions and theorems cited by "
    "the node in original_erdos_64_proof.tex."
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def line_number(source: bytes, offset: int) -> int:
    return source.count(b"\n", 0, offset) + 1


def unique_marker(source: bytes, marker: bytes) -> int:
    assert source.count(marker) == 1
    offset = source.index(marker)
    assert offset == 0 or source[offset - 1 : offset] == b"\n"
    assert source[offset + len(marker) : offset + len(marker) + 1] == b"\n"
    return offset


def independently_reconstruct_registry(source: bytes) -> dict[str, object]:
    diagram_start = unique_marker(source, DIAGRAM_START_MARKER)
    diagram_end = unique_marker(source, DIAGRAM_END_MARKER)
    assert diagram_start < diagram_end
    diagram = source[diagram_start:diagram_end]

    entries: list[dict[str, object]] = []
    node_ids: list[int] = []
    for source_order, match in enumerate(NODE_LINE.finditer(diagram), start=1):
        raw = match.group(1)
        identifiers = NODE_ID.findall(raw)
        assert len(identifiers) == 1
        node_id = int(identifiers[0])
        node_ids.append(node_id)
        start = diagram_start + match.start(1)
        end = diagram_start + match.end(1)
        entries.append(
            {
                "node_id": node_id,
                "source_order": source_order,
                "line_start": line_number(source, start),
                "line_end": line_number(source, end - 1),
                "byte_start": start,
                "byte_end_exclusive": end,
                "raw_tex_sha256": sha256(raw),
                "raw_tex": raw.decode("ascii"),
            }
        )

    assert diagram.count(b"\\node") == len(entries)
    assert len(entries) == 157
    assert len(set(node_ids)) == 157
    assert node_ids == list(range(1, 158))

    return {
        "schema_version": 1,
        "scope": "diagram_anchor_only",
        "scope_note": SCOPE_NOTE,
        "claims": {
            "node_identity_and_diagram_statement_anchored": True,
            "normalized_input_reviewed": False,
            "normalized_outcomes_reviewed": False,
            "full_quantified_contract_reviewed": False,
        },
        "original": {
            "path": "original_erdos_64_proof.tex",
            "byte_size": len(source),
            "sha256": sha256(source),
        },
        "diagram_slice": {
            "start_marker": DIAGRAM_START_MARKER.decode("ascii"),
            "end_marker_exclusive": DIAGRAM_END_MARKER.decode("ascii"),
            "line_start": line_number(source, diagram_start),
            "line_end": line_number(source, diagram_end - 1),
            "byte_start": diagram_start,
            "byte_end_exclusive": diagram_end,
            "sha256": sha256(diagram),
        },
        "node_count": len(entries),
        "nodes": entries,
    }


def run_extractor(root: Path, *extra_args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(EXTRACTOR_PATH),
            "--root",
            str(root),
            *extra_args,
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )


def test_registry_is_exactly_reconstructed_from_original_bytes() -> None:
    source = ORIGINAL_PATH.read_bytes()
    assert sha256(source) == ORIGINAL_SHA256
    expected = independently_reconstruct_registry(source)
    committed = json.loads(REGISTRY_PATH.read_text(encoding="ascii"))

    assert committed == expected
    for entry in committed["nodes"]:
        assert isinstance(entry, dict)
        raw = entry["raw_tex"].encode("ascii")
        start = entry["byte_start"]
        end = entry["byte_end_exclusive"]
        assert source[start:end] == raw
        assert sha256(source[start:end]) == entry["raw_tex_sha256"]
        assert line_number(source, start) == entry["line_start"]
        assert line_number(source, end - 1) == entry["line_end"]


def test_extractor_check_accepts_only_the_committed_registry() -> None:
    result = run_extractor(ROOT, "--check")
    assert result.returncode == 0, result.stderr


def test_extractor_fails_closed_on_original_drift(tmp_path: Path) -> None:
    source = bytearray(ORIGINAL_PATH.read_bytes())
    source[0] ^= 1
    (tmp_path / "original_erdos_64_proof.tex").write_bytes(source)

    result = run_extractor(tmp_path)

    assert result.returncode == 2
    assert "SHA-256" in result.stderr
    assert not (tmp_path / "migration/hypostructure/eg-original-node-anchors.json").exists()


def test_extractor_fails_closed_on_registry_drift(tmp_path: Path) -> None:
    (tmp_path / "original_erdos_64_proof.tex").write_bytes(ORIGINAL_PATH.read_bytes())
    output = tmp_path / "migration/hypostructure/eg-original-node-anchors.json"
    output.parent.mkdir(parents=True)
    drifted = json.loads(REGISTRY_PATH.read_text(encoding="ascii"))
    drifted["nodes"][0]["line_start"] += 1
    output.write_text(json.dumps(drifted, indent=2) + "\n", encoding="ascii")

    result = run_extractor(tmp_path, "--check")

    assert result.returncode == 2
    assert "registry drift" in result.stderr
