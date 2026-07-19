#!/usr/bin/env python3
"""Refresh Erdős node status from the Lean-owned WebExport descriptor.

This is a narrow recovery path for the dashboard projection when unrelated
downstream modules prevent recompiling the monolithic example aggregator.
It never invents status: it parses `formalizedNodeIds`, the canonical
`ExampleNodeObligationDescriptor` constructors, and the stable workflow/stage/
link/step identifiers in `WebExport.lean`.  It updates status and removes stale
compiled records whose identifiers no longer occur in the Lean-owned source.
The normal catalog renderer remains responsible for schema and cross-reference
validation.
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


def extract_live_ids(source: str) -> tuple[set[str], set[str], set[str]]:
    """Read stable descriptor IDs without reconstructing any Lean value."""

    stage_ids = {
        lean_string(value)
        for value in re.findall(r"\bstageId\s*:=\s*" + STRING, source)
    }
    link_ids = {
        lean_string(value)
        for value in re.findall(r"\blinkId\s*:=\s*" + STRING, source)
    }
    step_ids = {
        lean_string(value)
        for value in re.findall(r"\bstepId\s*:=\s*" + STRING, source)
    }
    if not stage_ids or not link_ids or not step_ids:
        raise StatusSyncError("cannot locate Lean-owned workflow identifiers")
    return stage_ids, link_ids, step_ids


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    root = args.root.resolve()
    source_path = root / "examples/erdos_64_eg/Erdos64EG/WebExport.lean"
    raw_path = root / "build/example-exports/erdos-64.raw.json"

    source = source_path.read_text(encoding="utf-8")
    ids, obligations = extract_status(source)
    stage_ids, link_ids, step_ids = extract_live_ids(source)
    raw = json.loads(raw_path.read_text(encoding="utf-8"))
    example = raw["example"]
    manuscript = example["manuscript"]
    manuscript["formalizedNodeIds"] = ids
    # Keep every descriptor that was actually compiled into the raw artifact.
    # Source-only deletion projection can break documentation links; a recovery
    # sync is authoritative only for node status and obligations.
    compiled_step_ids = {step["stepId"] for step in manuscript["proofSteps"]}
    unavailable_evidence = sorted(
        {
            step_id
            for obligation in obligations
            for step_id in obligation["evidenceStepIds"]
            if step_id not in compiled_step_ids
        }
    )
    if unavailable_evidence:
        # This recovery path may read a raw export older than WebExport.lean.
        # Never manufacture a proof-step descriptor and never leave a dangling
        # reference: until Lean regenerates that step, publish the obligation as
        # missing and keep its statement visible.
        for obligation in obligations:
            if any(
                step_id not in compiled_step_ids
                for step_id in obligation["evidenceStepIds"]
            ):
                obligation["status"] = "missing"
                obligation["evidenceStepIds"] = []
        unavailable_nodes = {
            int(obligation["nodeId"])
            for obligation in obligations
            if obligation["status"] == "missing"
        }
        manuscript["formalizedNodeIds"] = [
            node_id for node_id in ids if node_id not in unavailable_nodes
        ]
    manuscript["nodeObligations"] = obligations
    raw_path.write_text(json.dumps(raw, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(
        f"synced {len(ids)} green nodes, {len(obligations)} obligations, "
        f"{len(stage_ids)} stages, {len(link_ids)} links, and {len(step_ids)} steps"
    )
    if unavailable_evidence:
        print(
            "raw export lacks Lean-owned proof steps; conservatively demoted "
            + ", ".join(unavailable_evidence)
        )


if __name__ == "__main__":
    main()
