#!/usr/bin/env python3
"""Generate combined Lean bindings and per-tactic graph views."""
from __future__ import annotations

import argparse
import csv
import io
import json
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def manifest(root: Path = ROOT) -> dict:
    return load(root / "manifest.json")


def tactic_record(root: Path, tactic_id: str) -> dict:
    for record in manifest(root)["tactics"]:
        if record["tacticId"] == tactic_id:
            return record
    raise KeyError(f"unknown tactic {tactic_id}")


def tactic_ids(root: Path = ROOT) -> list[str]:
    return [record["tacticId"] for record in manifest(root)["tactics"]]


def load_graph(root: Path = ROOT, tactic_id: str = "CT2") -> tuple[dict, list[dict]]:
    record = tactic_record(root, tactic_id)
    tactic_path = root / record["specRef"]
    tactic = load(tactic_path)
    tactic_root = tactic_path.parent
    nodes = [load(tactic_root / ref) for ref in tactic["nodeRefs"]]
    return tactic, nodes


def tactic_instances(root: Path, tactic_id: str) -> list[tuple[Path, dict]]:
    result = []
    for relative in manifest(root)["instances"]:
        path = root / relative
        instance = load(path)
        if instance["tacticId"] == tactic_id:
            result.append((path, instance))
    return result


def declaration_refs(root: Path = ROOT, selected: Iterable[str] | None = None) -> list[dict]:
    selected_ids = list(selected) if selected is not None else tactic_ids(root)
    refs: list[dict] = []
    for tactic_id in selected_ids:
        record = tactic_record(root, tactic_id)
        tactic, nodes = load_graph(root, tactic_id)
        for node in nodes:
            refs.extend(binding["ref"] for binding in node["leanImplementation"]["declarations"])
            if terminal := node.get("terminal"):
                refs.extend([terminal["terminalConstructorRef"], terminal["outcomeConstructorRef"]])
            for branch in node["formalContract"].get("branches", []):
                refs.append(branch["resultConstructorRef"])
        for transition in tactic["transitions"]:
            refs.append(transition["transitionConstructorRef"])
            if constructor := transition["guard"].get("resultConstructorRef"):
                refs.append(constructor)
        refs.extend(tactic["formalApi"].values())
        refs.extend(
            coverage["theoremRef"]
            for coverage in tactic["terminalCoverage"]
            if coverage["mode"] == "parametric_theorem"
        )
        inventory = load(root / record["contractInventoryRef"])
        for contract in inventory["contracts"]:
            refs.extend(contract["leanEvidence"])
        for _, instance in tactic_instances(root, tactic_id):
            refs.extend(binding["leanRef"] for binding in instance["bindings"])
            refs.extend([
                instance["executionResultRef"],
                instance["terminalTheoremRef"],
                instance["traceTheoremRef"],
            ])

    seen: set[str] = set()
    unique: list[dict] = []
    for declaration_ref in refs:
        declaration = declaration_ref["declaration"]
        if declaration not in seen:
            seen.add(declaration)
            unique.append(declaration_ref)
    return unique


def render_binding_check(root: Path = ROOT) -> str:
    declarations = [item["declaration"] for item in declaration_refs(root)]
    versions = ", ".join(load_graph(root, tactic_id)[0]["graphVersion"] for tactic_id in tactic_ids(root))
    header = (
        "import StructuralExhaustion\n\n"
        f"-- Generated from the {versions} semantic graphs, contracts, and instances.\n"
    )
    return header + "\n".join(f"#check {name}" for name in declarations) + "\n"


def render_node_index(root: Path = ROOT, tactic_id: str = "CT2") -> str:
    _, nodes = load_graph(root, tactic_id)
    output = io.StringIO(newline="")
    writer = csv.writer(output, lineterminator="\n")
    writer.writerow([
        "graph_order", "node_id", "node_kind", "title", "terminal_case",
        "contracts", "lean_contract", "source_file",
    ])
    for order, node in enumerate(nodes, 1):
        contract_ref = node["formalContract"]["leanContractRef"]
        writer.writerow([
            order,
            node["nodeId"],
            node["nodeKind"],
            node["title"],
            node.get("terminal", {}).get("terminalCase", ""),
            "|".join(node["contracts"]),
            contract_ref["declaration"],
            contract_ref["sourceFile"],
        ])
    return output.getvalue()


def cytoscape_document(root: Path = ROOT, tactic_id: str = "CT2") -> dict:
    tactic, nodes = load_graph(root, tactic_id)
    return {
        "tacticId": tactic["tacticId"],
        "graphVersion": tactic["graphVersion"],
        "entryNodeId": tactic["entryNodeId"],
        "nodes": [
            {
                "data": {
                    "id": node["nodeId"],
                    "label": node["title"],
                    "nodeKind": node["nodeKind"],
                    "terminalCase": node.get("terminal", {}).get("terminalCase"),
                    "contracts": node["contracts"],
                    "leanContract": node["formalContract"]["leanContractRef"]["declaration"],
                }
            }
            for node in nodes
        ],
        "edges": [
            {
                "data": {
                    "id": edge["transitionId"],
                    "source": edge["fromNodeId"],
                    "target": edge["toNodeId"],
                    "kind": edge["kind"],
                    "branchTag": edge["guard"]["branchTag"],
                    "transitionConstructor": edge["transitionConstructorRef"]["declaration"],
                    "resultConstructor": edge["guard"].get("resultConstructorRef", {}).get("declaration"),
                    "evidence": [
                        {"slotId": slot["slotId"], "typeExpression": slot["typeExpression"]}
                        for slot in edge["guard"]["evidenceSlots"]
                    ],
                }
            }
            for edge in tactic["transitions"]
        ],
    }


def render_cytoscape(root: Path = ROOT, tactic_id: str = "CT2") -> str:
    return json.dumps(cytoscape_document(root, tactic_id), indent=2, ensure_ascii=False) + "\n"


def write_binding_check(root: Path = ROOT) -> Path:
    output = root / manifest(root)["leanProject"]["bindingCheckRef"]
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(render_binding_check(root), encoding="utf-8")
    return output


def write_graph_artifacts(root: Path = ROOT, selected: Iterable[str] | None = None) -> Iterable[Path]:
    selected_ids = list(selected) if selected is not None else tactic_ids(root)
    outputs: list[Path] = []
    for tactic_id in selected_ids:
        stem = tactic_id.lower()
        index = root / f"generated/{stem}-node-index.csv"
        cytoscape = root / f"generated/{stem}.cytoscape.json"
        index.write_text(render_node_index(root, tactic_id), encoding="utf-8")
        cytoscape.write_text(render_cytoscape(root, tactic_id), encoding="utf-8")
        outputs.extend([index, cytoscape])
    return outputs


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--graph-only", action="store_true")
    parser.add_argument("--binding-only", action="store_true")
    parser.add_argument("--tactic", action="append", choices=tactic_ids())
    args = parser.parse_args()
    if args.graph_only and args.binding_only:
        parser.error("--graph-only and --binding-only are mutually exclusive")
    selected = args.tactic or tactic_ids()
    written: list[Path] = []
    if not args.graph_only:
        written.append(write_binding_check())
    if not args.binding_only:
        written.extend(write_graph_artifacts(selected=selected))
    print("Wrote " + ", ".join(str(path.relative_to(ROOT)) for path in written))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
