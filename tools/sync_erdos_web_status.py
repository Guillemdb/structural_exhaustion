#!/usr/bin/env python3
"""Refresh Erdős node status from the Lean-owned WebExport descriptor.

This is a narrow recovery path for the dashboard projection when unrelated
downstream modules prevent recompiling the monolithic example aggregator.
It never invents status: it parses only `formalizedNodeIds` and the canonical
`ExampleNodeObligationDescriptor` constructors in `WebExport.lean`, updates
the existing compiled raw descriptor, and leaves declarations/workflows/proof
steps untouched.  The normal catalog renderer remains responsible for schema
and cross-reference validation.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


class StatusSyncError(RuntimeError):
    pass


STRING = r'"((?:[^"\\]|\\.)*)"'
PAIR_RE = re.compile(r"\(\s*" + STRING + r"\s*,\s*" + STRING + r"\s*\)", re.S)
HEADER_RE = re.compile(
    r"ExampleNodeObligationDescriptor\.(?:(provedForStep|partialForStep)\s+"
    r"(\d+)\s+" + STRING + r"|(missing)\s+(\d+))\s*\[",
    re.S,
)


def lean_string(value: str) -> str:
    return json.loads(f'"{value}"')


def bracket_body(source: str, opening: int) -> tuple[str, int]:
    depth = 0
    quoted = False
    escaped = False
    for index in range(opening, len(source)):
        char = source[index]
        if quoted:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                quoted = False
            continue
        if char == '"':
            quoted = True
        elif char == "[":
            depth += 1
        elif char == "]":
            depth -= 1
            if depth == 0:
                return source[opening + 1 : index], index + 1
    raise StatusSyncError("unterminated Lean obligation list")


def extract_status(source: str) -> tuple[list[int], list[dict[str, object]]]:
    manuscript_match = re.search(
        r"private def erdosManuscript\b.*?formalizedNodeIds\s*:=\s*\[(.*?)\]"
        r"\s*nodeObligations\s*:=\s*(.*?)\n\s*proofSteps\s*:=",
        source,
        re.S,
    )
    if manuscript_match is None:
        raise StatusSyncError("cannot locate the Lean-owned manuscript status block")

    ids = [int(value) for value in re.findall(r"\b\d+\b", manuscript_match.group(1))]
    if ids != sorted(set(ids)):
        raise StatusSyncError("formalizedNodeIds must be sorted and duplicate-free")

    obligations: list[dict[str, object]] = []
    obligation_source = manuscript_match.group(2)
    position = 0
    while header := HEADER_RE.search(obligation_source, position):
        body, position = bracket_body(obligation_source, header.end() - 1)
        if header.group(1) is not None:
            constructor = header.group(1)
            node_id = int(header.group(2))
            step_id = lean_string(header.group(3))
            status = "proved" if constructor == "provedForStep" else "partial"
            evidence = [step_id]
        else:
            node_id = int(header.group(5))
            status = "missing"
            evidence = []
        for pair in PAIR_RE.finditer(body):
            obligation_id = lean_string(pair.group(1))
            statement = lean_string(pair.group(2))
            obligations.append(
                {
                    "title": obligation_id,
                    "status": status,
                    "statement": statement,
                    "obligationId": obligation_id,
                    "nodeId": node_id,
                    "evidenceStepIds": evidence,
                }
            )

    obligation_ids = [item["obligationId"] for item in obligations]
    if len(obligation_ids) != len(set(obligation_ids)):
        raise StatusSyncError("Lean-owned node obligation IDs are not unique")
    if not obligations:
        raise StatusSyncError("Lean-owned node obligation ledger is empty")
    return ids, obligations


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    root = args.root.resolve()
    source_path = root / "examples/erdos_64_eg/Erdos64EG/WebExport.lean"
    raw_path = root / "build/example-exports/erdos-64.raw.json"

    ids, obligations = extract_status(source_path.read_text(encoding="utf-8"))
    raw = json.loads(raw_path.read_text(encoding="utf-8"))
    manuscript = raw["example"]["manuscript"]
    manuscript["formalizedNodeIds"] = ids
    manuscript["nodeObligations"] = obligations
    raw_path.write_text(json.dumps(raw, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"synced {len(ids)} green nodes and {len(obligations)} obligations")


if __name__ == "__main__":
    main()
