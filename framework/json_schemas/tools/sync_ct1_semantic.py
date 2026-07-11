#!/usr/bin/env python3
"""Synchronize the general CT1–CT17 catalog with the formal CT1-v1 machine."""
from __future__ import annotations

import csv
import json
from collections import defaultdict
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[1]
REPOSITORY = PACKAGE.parents[1]
FORMAL_ROOT = REPOSITORY / "ct2_formal_reference"
FORMAL_TACTIC = FORMAL_ROOT / "framework/CT1/tactic.json"
FORMAL_NODE_ROOT = FORMAL_TACTIC.parent
MANUSCRIPT = REPOSITORY / "framework/branch_closure_methodology_extended.tex"
DATA_PATH = PACKAGE / "data/ct1-ct17.numbered.json"
NODE_INDEX = PACKAGE / "data/node-index.csv"
SCHEMA_ROOT = PACKAGE / "schemas"
VERSION = "CT1-v1"


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def write(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def typed(item: dict, role: str | None = None) -> dict:
    value_kind = item.get("valueKind")
    inferred = (
        "parameter" if value_kind in {"algorithm", "type"}
        else "certificate" if value_kind in {"certificate", "proof"}
        else "payload" if value_kind == "payload"
        else "consumed"
    )
    return {
        "name": item["slotId"],
        "sort": item["typeExpression"],
        "role": role or inferred,
    }


def successful_status(node: dict) -> tuple[str, str]:
    case = node.get("terminal", {}).get("terminalCase")
    if case == "scope":
        return "scope_candidate", "Required typed scope-candidate completion state."
    if node["runtimeKind"] in {"decision", "certification"}:
        return "proved", "Required successful proof state for this executable machine node."
    return "validated", "Required successful validation state for this entry or terminal node."


def convert_nodes(tactic: dict, formal_nodes: list[dict]) -> tuple[list[dict], dict[str, list[dict]]]:
    manuscript_lines = MANUSCRIPT.read_text(encoding="utf-8").splitlines()
    source_lines = {
        node["nodeId"]: next(
            number for number, line in enumerate(manuscript_lines, 1)
            if node["nodeId"] in line.replace(r"\allowbreak ", "")
        )
        for node in formal_nodes
    }
    incoming: dict[str, list[str]] = defaultdict(list)
    outgoing: dict[str, list[dict]] = defaultdict(list)
    for edge in tactic["transitions"]:
        incoming[edge["toNodeId"]].append(edge["fromNodeId"])
        outgoing[edge["fromNodeId"]].append(edge)
    result: list[dict] = []
    for number, node in enumerate(formal_nodes, 1):
        node_id = node["nodeId"]
        kind = node["nodeKind"]
        terminal = node.get("terminal")
        terminal_case = terminal.get("terminalCase") if terminal else None
        node_type = (
            "input" if kind == "entry"
            else "decision" if kind == "decision"
            else "assertion" if kind == "certification"
            else "scope_audit" if terminal_case == "scope"
            else "certificate" if terminal_case == "c1"
            else "consumer_handoff"
        )
        modality = (
            "validate" if kind == "entry" or terminal_case == "c1"
            else "decide" if kind == "decision"
            else "prove" if kind == "certification"
            else "audit" if terminal_case == "scope"
            else "construct"
        )
        dependencies = list(dict.fromkeys(incoming[node_id]))
        inputs = [typed(item) for item in node["formalContract"]["inputs"]]
        outputs = [typed(item, "produced") for item in node["formalContract"]["outputs"]]
        if terminal_case and terminal_case.startswith("ct"):
            outputs = [{
                "name": f"P_1_to_{terminal_case[2:]}",
                "sort": node["formalContract"]["inputs"][-1]["typeExpression"],
                "role": "payload",
            }]
        old = {
            "artifactType": "nodeSpec",
            "schemaVersion": "1.0.0",
            "nodeNumber": number,
            "nodeId": node_id,
            "localKey": node_id.split(".")[-1],
            "nodeType": node_type,
            "runtimeKind": kind,
            "title": node["title"],
            "labelLatex": node["human"].get("latex") or node["title"],
            "obligation": {
                "obligationId": f"{node_id}.O1",
                "modality": modality,
                "statement": {
                    "informal": node["human"]["informal"],
                    "latex": node["human"].get("latex", ""),
                },
                "contractSchemas": node["contracts"],
                "dependencies": dependencies,
                "dischargeCriteria": node["formalContract"]["dischargeCondition"],
            },
            "inputs": inputs,
            "outputs": outputs,
            "dependsOn": dependencies,
            "outgoingTransitionIds": [edge["transitionId"] for edge in outgoing[node_id]],
            "terminalRole": (
                "none" if not terminal
                else "scope_audit" if terminal_case == "scope"
                else "certificate" if terminal_case == "c1"
                else "consumer_handoff"
            ),
            "source": {
                "file": "branch_closure_methodology_extended.tex",
                "section": tactic["source"]["section"],
                "line": source_lines[node_id],
                "diagramKey": node["source"]["diagramKey"],
            },
        }
        if kind == "decision":
            old["branches"] = [
                {
                    "transitionId": branch["transitionId"],
                    "guard": branch["branchTag"],
                    "targetNodeId": next(
                        edge["toNodeId"]
                        for edge in tactic["transitions"]
                        if edge["transitionId"] == branch["transitionId"]
                    ),
                    "resultConstructor": branch["resultConstructorRef"]["declaration"],
                    "evidenceSlots": [typed(item, "payload" if item["valueKind"] == "payload" else "produced") for item in branch["evidenceSlots"]],
                }
                for branch in node["formalContract"]["branches"]
            ]
        if terminal:
            old["terminalCase"] = terminal_case
            if terminal_case == "scope":
                old["scopeAudit"] = {
                    "classification": "candidate_scope_obstruction",
                    "requiredFinding": "Retain the proof that ScopeReadyAt is false and refer the expressibility limit to the global scope audit.",
                }
            elif terminal_case == "c1":
                old["certificate"] = {
                    "class": "C1",
                    "validationStatement": "The realized test and certified forward equivalence implication establish the exact target proposition.",
                }
            else:
                consumer = terminal_case[2:]
                old["consumer"] = {"tacticId": f"CT{consumer}", "triggerContract": "S-Trig"}
        result.append(old)
    return result, outgoing


def convert_transitions(tactic: dict) -> list[dict]:
    converted = []
    for number, edge in enumerate(tactic["transitions"], 1):
        guard = edge["guard"]
        item = {
            "transitionNumber": number,
            "transitionId": edge["transitionId"],
            "fromNodeId": edge["fromNodeId"],
            "toNodeId": edge["toNodeId"],
            "transitionType": "scope" if edge["kind"] == "scope" else "handoff" if edge["kind"] == "handoff" else "intended",
            "guard": guard["branchTag"],
            "guardLatex": guard["branchTag"],
            "sourceStyle": "bcscopearr" if edge["kind"] == "scope" else "bchandoff" if edge["kind"] == "handoff" else "bcarr",
            "branchTag": guard["branchTag"],
            "transitionConstructor": edge["transitionConstructorRef"]["declaration"],
            "evidenceSlots": [typed(slot, "payload" if slot["valueKind"] == "payload" else "produced") for slot in guard["evidenceSlots"]],
        }
        if constructor := guard.get("resultConstructorRef"):
            item["resultConstructor"] = constructor["declaration"]
        converted.append(item)
    return converted


def build_tactic(formal: dict, formal_nodes: list[dict]) -> dict:
    nodes, _ = convert_nodes(formal, formal_nodes)
    return {
        "artifactType": "tacticSpec",
        "schemaVersion": "1.0.0",
        "graphVersion": VERSION,
        "tacticId": "CT1",
        "name": formal["name"],
        "tacticType": "local_test",
        "signature": {
            "latex": "\\(\\langle\\mathfrak B,T,\\mathcal T,W\\rangle \\to \\ctcert{C1};\\ \\ctint{P_{1\\to2},P_{1\\to3},P_{1\\to4},P_{1\\to5},P_{1\\to6},P_{1\\to17}};\\ \\ctrec{\\ctnone}\\).",
            "inputDescription": "Validated Input(F): an ambient object, branch state, and baseline proof. Static target and test vocabulary, exact consumer frameworks for CT2, CT3, CT4, CT5, CT6, and CT17, and their alignment predicates belong to Framework.",
            "parameterDescription": "Supply four proof-producing node plans—scope, equivalence, realization, and payload—plus Port and HandoffPlan independently.",
        },
        "mechanism": {
            "execution": "Execute scope admission, certify target-test equivalence, decide realization, and classify one target-avoiding state into a typed payload. Equivalence failure is a pre-admission repair obligation, not a runtime branch.",
            "routing": "A realized test closes at C1. Otherwise one indexed payload reaches CT2, CT3, CT4, CT5, CT6, or CT17. Every route carries the actual consumer input and an explicit alignment proof.",
            "limit": "run_total is relative to the supplied node plans. Target avoidance is available only through EquivalenceCertificate and the negative realization constructor.",
        },
        "entryNodeIds": ["CT1.entry"],
        "nodes": nodes,
        "transitions": convert_transitions(formal),
        "allowedCertificates": ["C1"],
        "declaredPayloads": ["P_1_to_2", "P_1_to_3", "P_1_to_4", "P_1_to_5", "P_1_to_6", "P_1_to_17"],
        "scopeCandidateNodeIds": ["CT1.terminal.scope"],
        "auditRejectNodeIds": [],
        "completeness": {
            "numberingPolicy": "nodeNumber and transitionNumber are presentation order; semantic IDs are stable runtime identities",
            "noUnnamedResiduals": True,
            "allSinksTyped": True,
            "uniqueConsumerPerPayload": True,
            "allDecisionBranchesExplicit": True,
        },
        "totality": {
            "relativeToSuppliedPlans": True,
            "terminalCases": formal["terminalCases"],
            "statement": "For every validated input, CorePlan, Port, and HandoffPlan, run_total produces one indexed outcome and one evidence-carrying path. This does not assert automatic witness search.",
        },
        "cyclePolicy": {"hasCycles": False, "cycles": [], "cycleKinds": [], "requiresWellFoundedMeasure": False},
        "source": {
            "file": "branch_closure_methodology_extended.tex",
            "section": formal["source"]["section"],
            "line": next(
                number
                for number, line in enumerate(MANUSCRIPT.read_text(encoding="utf-8").splitlines(), 1)
                if line.startswith(r"\subsection{CT1")
            ),
        },
    }


def contract_hint(contract: str) -> str:
    hints = {
        "S-Def": "defines the validated typed state and its exact fields",
        "S-Dich": "provides the exhaustive proof-carrying alternatives",
        "S-Equiv": "certifies both target-test implications",
        "S-Pers": "retains the exact target-avoiding predecessor state",
        "S-Rout": "constructs the indexed downstream route",
        "S-Trig": "proves the selected consumer accepts the payload",
        "A-Cert": "validates the C1 closure certificate",
        "A-Scope": "records the typed scope obstruction",
    }
    return hints.get(contract, "discharges the declared mathematical contract")


def concrete_node_schema(node: dict) -> dict:
    status, status_description = successful_status(node)
    contracts = node["obligation"]["contractSchemas"]
    properties = {
        "tacticId": {"description": f"Owning tactic discriminator for {node['nodeId']}; it must be CT1.", "const": "CT1"},
        "nodeId": {"description": f"Stable semantic runtime identifier for {node['title']}.", "const": node["nodeId"]},
        "nodeNumber": {"description": f"One-based presentation-order index for {node['nodeId']}.", "const": node["nodeNumber"]},
        "status": {"description": status_description, "const": status},
        "dischargedContracts": {
            "type": "array",
            "uniqueItems": True,
            "minItems": len(contracts),
            "maxItems": len(contracts),
            "description": f"Exact contract families discharged at {node['nodeId']}: {', '.join(contracts)}.",
            "allOf": [
                {"contains": {"description": f"Requires {contract}, which {contract_hint(contract)}.", "const": contract}}
                for contract in contracts
            ],
        },
        "contractInstances": {
            "type": "array",
            "minItems": len(contracts),
            "description": f"Typed contract instances for {node['nodeId']}; every declared family is required.",
            "allOf": [
                {
                    "contains": {
                        "required": ["schema"],
                        "properties": {
                            "schema": {
                                "description": f"Discriminator for {contract} evidence at {node['nodeId']}; it {contract_hint(contract)}.",
                                "const": contract,
                            }
                        },
                    }
                }
                for contract in contracts
            ],
        },
    }
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": f"https://example.org/structural-exhaustion/concrete/nodes/{node['nodeId']}.schema.json",
        "title": f"{node['nodeId']} completed discharge record — {node['title']}",
        "description": f"Concrete completed-discharge schema for semantic {VERSION} node {node['nodeId']}.",
        "allOf": [
            {"$ref": "../../structural-exhaustion.bundle.schema.json#/$defs/nodeProofRecord"},
            {"properties": properties, "required": list(properties)},
        ],
        "x-obligation": node["obligation"],
    }


def concrete_tactic_schema(tactic: dict) -> dict:
    node_items = []
    for node in tactic["nodes"]:
        properties = {
            "nodeId": {"description": f"Exact semantic runtime ID for {node['title']}.", "const": node["nodeId"]},
            "nodeNumber": {"description": f"Presentation-order index for {node['nodeId']}.", "const": node["nodeNumber"]},
            "nodeType": {"description": f"Mathematical role for {node['nodeId']}.", "const": node["nodeType"]},
            "runtimeKind": {"description": f"Control-machine role for {node['nodeId']}.", "const": node["runtimeKind"]},
        }
        if case := node.get("terminalCase"):
            properties["terminalCase"] = {"description": f"Exact terminal case represented by {node['nodeId']}.", "const": case}
        node_items.append({
            "allOf": [
                {"$ref": "../../structural-exhaustion.bundle.schema.json#/$defs/nodeSpec"},
                {"properties": properties, "required": list(properties)},
            ]
        })
    edge_items = []
    for edge in tactic["transitions"]:
        properties = {
            "transitionId": {"description": "Exact semantic transition identity.", "const": edge["transitionId"]},
            "transitionNumber": {"description": "One-based presentation-order transition index.", "const": edge["transitionNumber"]},
            "fromNodeId": {"description": "Exact typed source state.", "const": edge["fromNodeId"]},
            "toNodeId": {"description": "Exact typed target state.", "const": edge["toNodeId"]},
        }
        edge_items.append({"properties": properties, "required": list(properties)})
    properties = {
        "tacticId": {"description": "Required CT1 tactic discriminator.", "const": "CT1"},
        "graphVersion": {"description": "Required semantic graph version.", "const": VERSION},
        "entryNodeIds": {"description": "The unique semantic entry node.", "const": tactic["entryNodeIds"]},
        "nodes": {"description": "Exact thirteen-node CT1-v1 machine in presentation order.", "type": "array", "prefixItems": node_items, "items": False, "minItems": 13, "maxItems": 13},
        "transitions": {"description": "Exact twelve evidence-carrying CT1-v1 edges in presentation order.", "type": "array", "prefixItems": edge_items, "items": False, "minItems": 12, "maxItems": 12},
    }
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://example.org/structural-exhaustion/concrete/tactics/CT1.schema.json",
        "title": "CT1-v1 semantic runtime graph — Target-test alignment and first closure",
        "description": "Concrete static-graph schema for the exact CT1-v1 sequential machine.",
        "allOf": [
            {"$ref": "../../structural-exhaustion.bundle.schema.json#/$defs/tacticSpec"},
            {"properties": properties, "required": list(properties)},
        ],
    }


def concrete_verification_schema(tactic: dict) -> dict:
    refs = [{"$ref": f"../nodes/{node['nodeId']}.schema.json"} for node in tactic["nodes"]]
    properties = {
        "tacticId": {"description": "Required CT1 verification discriminator.", "const": "CT1"},
        "nodeRecords": {"description": "Exactly one completed record for each CT1-v1 semantic node.", "type": "array", "prefixItems": refs, "items": False, "minItems": 13, "maxItems": 13},
    }
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://example.org/structural-exhaustion/concrete/verifications/CT1.verification.schema.json",
        "title": "CT1-v1 structural all-node verification",
        "description": "Requires structural coverage of all thirteen CT1-v1 states; it does not claim witness-search completeness.",
        "allOf": [
            {"$ref": "../../structural-exhaustion.bundle.schema.json#/$defs/tacticVerification"},
            {"properties": properties, "required": list(properties)},
        ],
    }


def concrete_run_schema(tactic: dict) -> dict:
    node_ids = [node["nodeId"] for node in tactic["nodes"]]
    refs = [{"$ref": f"../nodes/{node_id}.schema.json"} for node_id in node_ids]
    properties = {
        "tacticId": {"description": "Required CT1 run discriminator.", "const": "CT1"},
        "visitedNodeIds": {"description": "Execution-order path using only CT1-v1 semantic node IDs.", "type": "array", "items": {"enum": node_ids}, "minItems": 2},
        "nodeRecords": {"description": "Proof records aligned one-for-one with the visited semantic path.", "type": "array", "items": {"oneOf": refs}, "minItems": 2},
        "outcome": {
            "description": "Exact terminal result of the CT1-v1 run.",
            "properties": {
                "terminalCase": {"description": "One of the eight exact CT1-v1 terminal cases.", "enum": tactic["totality"]["terminalCases"]}
            },
            "required": ["terminalCase"],
        },
    }
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://example.org/structural-exhaustion/concrete/runs/CT1.run.schema.json",
        "title": "CT1-v1 legal semantic-machine run",
        "description": "A CT1-v1 path begins at CT1.entry, follows typed edges, and ends at one exact terminal.",
        "allOf": [
            {"$ref": "../../structural-exhaustion.bundle.schema.json#/$defs/tacticRun"},
            {"properties": properties, "required": list(properties)},
        ],
        "x-semanticValidationRules": [
            "validate visitedNodeIds as a path in the CT1-v1 semantic transition graph",
            "require outcome.terminalCase to equal the final terminal node's terminalCase",
        ],
    }


def write_node_index(library: dict) -> None:
    with NODE_INDEX.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(["tactic_id", "node_number", "node_id", "local_key", "node_type", "title", "contracts", "source_line"])
        for tactic in library["tactics"]:
            for node in tactic["nodes"]:
                writer.writerow([
                    tactic["tacticId"], node["nodeNumber"], node["nodeId"], node["localKey"],
                    node["nodeType"], node["title"], "|".join(node["obligation"]["contractSchemas"]), node["source"]["line"],
                ])


def main() -> int:
    formal = load(FORMAL_TACTIC)
    formal_nodes = [load(FORMAL_NODE_ROOT / ref) for ref in formal["nodeRefs"]]
    ct1 = build_tactic(formal, formal_nodes)
    library = load(DATA_PATH)
    library["title"] = "Structural Exhaustion CT1–CT17 semantic tactic specifications"
    library["sourceDocument"] = "branch_closure_methodology_extended.tex"
    library["numberingConvention"] = "CT1-v1, CT2-v2, and CT3-v1 through CT17-v1 use stable semantic node and edge IDs. Numeric fields are one-based presentation order."
    index = next(index for index, tactic in enumerate(library["tactics"]) if tactic["tacticId"] == "CT1")
    library["tactics"][index] = ct1
    write(DATA_PATH, library)
    write_node_index(library)

    concrete_nodes = SCHEMA_ROOT / "concrete/nodes"
    for path in concrete_nodes.glob("CT1.N*.schema.json"):
        path.unlink()
    for node in ct1["nodes"]:
        write(concrete_nodes / f"{node['nodeId']}.schema.json", concrete_node_schema(node))
    write(SCHEMA_ROOT / "concrete/tactics/CT1.schema.json", concrete_tactic_schema(ct1))
    write(SCHEMA_ROOT / "concrete/verifications/CT1.verification.schema.json", concrete_verification_schema(ct1))
    write(SCHEMA_ROOT / "concrete/runs/CT1.run.schema.json", concrete_run_schema(ct1))
    print("Synchronized CT1-v1: 13 nodes, 12 transitions, 8 terminals")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
