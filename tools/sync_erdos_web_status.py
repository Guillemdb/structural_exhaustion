#!/usr/bin/env python3
"""Refresh Erdős node status from checked per-node Lean files.

This is a narrow recovery path for the dashboard projection when unrelated
downstream modules prevent recompiling the monolithic example aggregator.
It never trusts stale exported node claims: green nodes are direct
`Erdos64EG/NodeX.lean` files with a fresh kernel-checked `.olean`; yellow nodes
are direct `NodeX.lean` files without that checked artifact; nodes with no
direct Lean file remain missing so the frontend can render them white or
frontier-orange from topology.
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
NODE_FILE_RE = re.compile(r"^Node(\d+)\.lean$")
ORIGINAL_NODE_IDS = set(range(1, 158))


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


def direct_node_files(root: Path) -> set[int]:
    node_root = root / "examples/erdos_64_eg/Erdos64EG"
    result: set[int] = set()
    for path in node_root.glob("Node*.lean"):
        match = NODE_FILE_RE.match(path.name)
        if match is None:
            continue
        node_id = int(match.group(1))
        if node_id in ORIGINAL_NODE_IDS:
            result.add(node_id)
    return result


def fresh_checked_node_ids(root: Path, node_ids: set[int]) -> set[int]:
    source_root = root / "examples/erdos_64_eg/Erdos64EG"
    olean_root = root / "examples/erdos_64_eg/.lake/build/lib/lean/Erdos64EG"
    checked: set[int] = set()
    for node_id in node_ids:
        source = source_root / f"Node{node_id}.lean"
        olean = olean_root / f"Node{node_id}.olean"
        if olean.exists() and olean.stat().st_mtime >= source.stat().st_mtime:
            checked.add(node_id)
    return checked


def implemented_evidence_by_node(
    proof_steps: list[dict[str, object]],
) -> dict[int, list[str]]:
    evidence: dict[int, list[str]] = {}
    for step in proof_steps:
        if step.get("status") != "implemented":
            continue
        step_id = step.get("stepId")
        if not isinstance(step_id, str):
            continue
        for reference in step.get("manuscriptRefs", []):
            if not isinstance(reference, dict):
                continue
            for raw_node_id in reference.get("nodeIds", []):
                if not isinstance(raw_node_id, int):
                    continue
                node_evidence = evidence.setdefault(raw_node_id, [])
                if step_id not in node_evidence:
                    node_evidence.append(step_id)
    return evidence


def synchronize_node_file_status(
    obligations: list[dict[str, object]],
    existing_node_ids: set[int],
    checked_node_ids: set[int],
    evidence_by_node: dict[int, list[str]],
) -> list[dict[str, object]]:
    by_node: dict[int, list[dict[str, object]]] = {}
    for obligation in obligations:
        node_id = int(obligation["nodeId"])
        if node_id in ORIGINAL_NODE_IDS:
            by_node.setdefault(node_id, []).append(dict(obligation))

    synchronized: list[dict[str, object]] = []
    for node_id in sorted(ORIGINAL_NODE_IDS):
        node_obligations = by_node.get(node_id)
        if not node_obligations:
            status = (
                "proved"
                if node_id in checked_node_ids
                else "partial"
                if node_id in existing_node_ids
                else "missing"
            )
            evidence = [] if status == "missing" else evidence_by_node.get(node_id, [])
            if status != "missing" and not evidence:
                status = "missing"
            synchronized.append(
                {
                    "title": f"N{node_id}-NODE-FILE",
                    "status": status,
                    "statement": (
                        f"Direct Erdos64EG/Node{node_id}.lean kernel-check status."
                    ),
                    "obligationId": f"N{node_id}-NODE-FILE",
                    "nodeId": node_id,
                    "evidenceStepIds": evidence if status != "missing" else [],
                }
            )
            continue

        for obligation in node_obligations:
            if node_id in checked_node_ids:
                obligation["status"] = "proved"
                if not obligation["evidenceStepIds"]:
                    obligation["evidenceStepIds"] = evidence_by_node.get(node_id, [])
            elif node_id in existing_node_ids:
                obligation["status"] = "partial"
                if not obligation["evidenceStepIds"]:
                    obligation["evidenceStepIds"] = evidence_by_node.get(node_id, [])
            else:
                obligation["status"] = "missing"
                obligation["evidenceStepIds"] = []
            if obligation["status"] != "missing" and not obligation["evidenceStepIds"]:
                obligation["status"] = "missing"
            synchronized.append(obligation)

    return synchronized


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
    exported_ids, obligations = extract_status(source)
    raw = json.loads(raw_path.read_text(encoding="utf-8"))
    example = raw["example"]
    manuscript = example["manuscript"]
    evidence_by_node = implemented_evidence_by_node(manuscript["proofSteps"])
    existing_node_ids = direct_node_files(root)
    checked_node_ids = fresh_checked_node_ids(root, existing_node_ids)
    ids = sorted(checked_node_ids)
    obligations = synchronize_node_file_status(
        obligations, existing_node_ids, checked_node_ids, evidence_by_node
    )
    stage_ids, link_ids, step_ids = extract_live_ids(source)
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
    else:
        missing_nodes = {
            int(obligation["nodeId"])
            for obligation in obligations
            if obligation["status"] == "missing"
        }
        manuscript["formalizedNodeIds"] = [
            node_id for node_id in ids if node_id not in missing_nodes
        ]
    manuscript["nodeObligations"] = obligations
    raw_path.write_text(json.dumps(raw, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    unchecked_existing = sorted(existing_node_ids - checked_node_ids)
    print(
        f"synced {len(ids)} checked green nodes, {len(unchecked_existing)} "
        f"unchecked yellow node files, {len(obligations)} obligations, "
        f"{len(stage_ids)} stages, {len(link_ids)} links, and {len(step_ids)} steps"
    )
    if sorted(exported_ids) != ids:
        print(
            "replaced stale WebExport formalizedNodeIds "
            f"{sorted(exported_ids)} with checked NodeX.lean ids {ids}"
        )
    if unchecked_existing:
        print("unchecked direct node files: " + ", ".join(map(str, unchecked_existing)))
    if unavailable_evidence:
        print(
            "raw export lacks Lean-owned proof steps; conservatively demoted "
            + ", ".join(unavailable_evidence)
        )


if __name__ == "__main__":
    main()
