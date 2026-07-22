#!/usr/bin/env python3
"""Extract immutable EG proof-diagram node anchors from the original TeX."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re


ORIGINAL_PATH = Path("original_erdos_64_proof.tex")
REGISTRY_PATH = Path("migration/hypostructure/eg-original-node-anchors.json")
ORIGINAL_BYTE_SIZE = 835801
ORIGINAL_SHA256 = (
    "215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10"
)
DIAGRAM_START_MARKER = b"\\subsection*{Proof-dependency diagram}"
DIAGRAM_END_MARKER = b"\\subsection*{Detailed dependency table}"
NODE_START = re.compile(rb"(?m)^\\node(?=\[)")
NODE_ID = re.compile(rb"\\textbf\{\[([0-9]+)\]\}")
EXPECTED_NODE_IDS = list(range(1, 158))
SCOPE_NOTE = (
    "This registry anchors only node identity and each displayed proof-dependency "
    "diagram statement. It does not claim that normalized_input, "
    "normalized_outcomes, or any node's full quantified contract has been "
    "reviewed. Before implementation, read the definitions and theorems cited by "
    "the node in original_erdos_64_proof.tex."
)


class AnchorExtractionError(RuntimeError):
    """Raised when immutable source anchors cannot be extracted exactly."""


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _line_number(source: bytes, offset: int) -> int:
    if not 0 <= offset < len(source):
        raise AnchorExtractionError(f"source offset {offset} is out of range")
    return source.count(b"\n", 0, offset) + 1


def _unique_marker(source: bytes, marker: bytes, label: str) -> int:
    if source.count(marker) != 1:
        raise AnchorExtractionError(f"expected exactly one {label} marker")
    offset = source.index(marker)
    if offset != 0 and source[offset - 1 : offset] != b"\n":
        raise AnchorExtractionError(f"{label} marker is not at the start of a line")
    marker_end = offset + len(marker)
    if source[marker_end : marker_end + 1] not in (b"\n", b"\r"):
        raise AnchorExtractionError(f"{label} marker is not a complete source line")
    return offset


def _node_command_end(source: bytes, start: int, limit: int) -> int:
    """Return the exclusive end of one TeX node command.

    TikZ terminates a command with a semicolon. Semicolons inside TeX groups and
    escaped semicolons are part of the displayed statement and must be retained.
    """

    brace_depth = 0
    in_comment = False
    offset = start
    while offset < limit:
        current = source[offset]
        if in_comment:
            if current in (10, 13):
                in_comment = False
            offset += 1
            continue
        if current == ord("\\"):
            if offset + 1 >= limit:
                raise AnchorExtractionError("unterminated TeX escape in node command")
            offset += 2
            continue
        if current == ord("%"):
            in_comment = True
        elif current == ord("{"):
            brace_depth += 1
        elif current == ord("}"):
            brace_depth -= 1
            if brace_depth < 0:
                raise AnchorExtractionError("unbalanced closing brace in node command")
        elif current == ord(";") and brace_depth == 0:
            return offset + 1
        offset += 1
    raise AnchorExtractionError("node command has no top-level terminating semicolon")


def _read_pinned_original(root: Path) -> bytes:
    source_path = root / ORIGINAL_PATH
    try:
        source = source_path.read_bytes()
    except OSError as error:
        raise AnchorExtractionError(f"cannot read {ORIGINAL_PATH}: {error}") from error
    if len(source) != ORIGINAL_BYTE_SIZE:
        raise AnchorExtractionError(
            f"{ORIGINAL_PATH} byte size is {len(source)}, expected {ORIGINAL_BYTE_SIZE}"
        )
    observed_sha = _sha256(source)
    if observed_sha != ORIGINAL_SHA256:
        raise AnchorExtractionError(
            f"{ORIGINAL_PATH} SHA-256 is {observed_sha}, expected {ORIGINAL_SHA256}"
        )
    return source


def extract_registry(root: Path) -> dict[str, object]:
    """Build the exact diagram-only anchor registry from the pinned original."""

    source = _read_pinned_original(root)
    diagram_start = _unique_marker(
        source, DIAGRAM_START_MARKER, "proof-dependency diagram start"
    )
    diagram_end = _unique_marker(
        source, DIAGRAM_END_MARKER, "detailed dependency table start"
    )
    if diagram_start >= diagram_end:
        raise AnchorExtractionError("diagram source markers are out of order")

    diagram = source[diagram_start:diagram_end]
    relative_starts = [match.start() for match in NODE_START.finditer(diagram)]
    entries: list[dict[str, object]] = []
    observed_ids: list[int] = []
    previous_end = diagram_start

    for source_order, relative_start in enumerate(relative_starts, start=1):
        start = diagram_start + relative_start
        if start < previous_end:
            raise AnchorExtractionError("overlapping node command slices")
        end = _node_command_end(source, start, diagram_end)
        raw = source[start:end]
        id_matches = NODE_ID.findall(raw)
        if len(id_matches) != 1:
            raise AnchorExtractionError(
                f"node command at line {_line_number(source, start)} must contain "
                "exactly one bracketed textbf node identifier"
            )
        node_id = int(id_matches[0])
        observed_ids.append(node_id)
        try:
            raw_tex = raw.decode("ascii")
        except UnicodeDecodeError as error:
            raise AnchorExtractionError(
                f"node {node_id} command is not exact ASCII TeX"
            ) from error
        entries.append(
            {
                "node_id": node_id,
                "source_order": source_order,
                "line_start": _line_number(source, start),
                "line_end": _line_number(source, end - 1),
                "byte_start": start,
                "byte_end_exclusive": end,
                "raw_tex_sha256": _sha256(raw),
                "raw_tex": raw_tex,
            }
        )
        previous_end = end

    if observed_ids != EXPECTED_NODE_IDS:
        raise AnchorExtractionError(
            "diagram nodes must occur exactly once in source order as Node 1..157; "
            f"observed {observed_ids}"
        )

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
            "path": ORIGINAL_PATH.as_posix(),
            "byte_size": len(source),
            "sha256": _sha256(source),
        },
        "diagram_slice": {
            "start_marker": DIAGRAM_START_MARKER.decode("ascii"),
            "end_marker_exclusive": DIAGRAM_END_MARKER.decode("ascii"),
            "line_start": _line_number(source, diagram_start),
            "line_end": _line_number(source, diagram_end - 1),
            "byte_start": diagram_start,
            "byte_end_exclusive": diagram_end,
            "sha256": _sha256(diagram),
        },
        "node_count": len(entries),
        "nodes": entries,
    }


def render_registry(registry: dict[str, object]) -> bytes:
    return (json.dumps(registry, indent=2, ensure_ascii=True) + "\n").encode("ascii")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Extract exact diagram-only node anchors from the immutable EG original."
    )
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--output", type=Path, default=REGISTRY_PATH)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail unless the committed registry is byte-for-byte current",
    )
    args = parser.parse_args()

    root = args.root.resolve()
    output = args.output if args.output.is_absolute() else root / args.output
    try:
        rendered = render_registry(extract_registry(root))
        if args.check:
            try:
                committed = output.read_bytes()
            except OSError as error:
                raise AnchorExtractionError(f"cannot read registry {output}: {error}") from error
            if committed != rendered:
                raise AnchorExtractionError(
                    f"registry drift: regenerate {output} from the pinned original"
                )
        else:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(rendered)
    except AnchorExtractionError as error:
        parser.exit(2, f"error: {error}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
