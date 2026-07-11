#!/usr/bin/env python3
"""Synchronize the general CT1--CT17 catalog with semantic CT3--CT17 machines."""
from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path

from sync_ct1_semantic import load, write, write_node_index

PACKAGE = Path(__file__).resolve().parents[1]
REPOSITORY = PACKAGE.parents[1]
FORMAL_ROOT = REPOSITORY / "ct2_formal_reference"
MANUSCRIPT = REPOSITORY / "framework/branch_closure_methodology_extended.tex"
DATA_PATH = PACKAGE / "data/ct1-ct17.numbered.json"
SCHEMA_ROOT = PACKAGE / "schemas"

CONFIG = {
    "CT3": {
        "version": "CT3-v1",
        "type": "external_type",
        "signature": r"\(P_{\ast\to3}\to \ctcert{C2,C3,C5};\ \ctint{P_{3\to7},P_{3\to12},P_{3\to8}};\ \ctrec{\ctnone}\).",
        "input": "A validated boundaried piece, certified interface, ambient object, and branch state.",
        "parameters": "Five independent proof-producing plans for scope, equivalence, compression, defect routing, and finite-table classification, plus a separate consumer port.",
        "execution": "Admit the finite interface, certify response equivalence, exhaust smaller replacements, classify a concrete defect, and classify the persistent finite table.",
        "routing": "C2, C3, and C5 are closure terminals. Indexed payloads route exchange data to CT7, measured load to CT12, and repeated types to CT8.",
        "limit": "A finite type index and response-equivalence certificate are preconditions for comparison; totality is relative to the five supplied node plans.",
        "certificates": ["C2", "C3", "C5"],
        "payloads": ["P_3_to_7", "P_3_to_12", "P_3_to_8"],
    },
    "CT4": {
        "version": "CT4-v1",
        "type": "charging",
        "signature": r"\(P_{\ast\to4}\to \ctcert{C4};\ \ctint{P_{4\to9},P_{4\to14}};\ \ctrec{P_{4\to13}}\).",
        "input": "A validated demand--payer ledger with an explicit partial assignment, capacity datum, and lower-bound datum.",
        "parameters": "Five independent proof-producing plans for scope, canonical assignment, payer availability, fibre capacity, and comparison, plus a separate consumer port.",
        "execution": "Admit the demand family, certify the canonical map, prove totality or exhibit a missing payer, prove bounded fibres or exhibit overload, and compare demand with capacity.",
        "routing": "C4 is the closure terminal. Indexed payloads route missing payer data to CT13, overload to CT9, and aggregate residual mass to CT14.",
        "limit": "Canonicality is a certification boundary and cannot be replaced by an unchecked tie-break; totality is relative to the five supplied node plans.",
        "certificates": ["C4"],
        "payloads": ["P_4_to_9", "P_4_to_14", "P_4_to_13"],
    },
    "CT5": {
        "version": "CT5-v1",
        "type": "local_to_global",
        "signature": r"\(P_{1\to5}\to \ctcert{C4};\ \ctint{P_{5\to4},P_{5\to11},P_{5\to14}};\ \ctrec{\ctnone}\).",
        "input": "A validated ambient object, branch state, site family, and dependent local-witness extractor.",
        "parameters": "Five independent proof-producing plans for scope, locality, deficit routing, summation, and comparison, plus a separate consumer port.",
        "execution": "Admit bounded witnesses, certify locality, isolate an additive deficit or local ledger, certify the sum, and classify the global comparison.",
        "routing": "C4 is the closure terminal. Indexed payloads route an exact ledger to CT4, an additive deficit to CT11, and aggregate residual mass to CT14.",
        "limit": "Locality and summation are certification boundaries; the CT4 adapter preserves the ambient object and branch state definitionally.",
        "certificates": ["C4"],
        "payloads": ["P_5_to_4", "P_5_to_11", "P_5_to_14"],
    },
    "CT6": {
        "version": "CT6-v1",
        "type": "activity",
        "signature": r"\(P_{1\to6}\to \ctcert{C1};\ \ctint{P_{6\to4},P_{6\to3},P_{6\to7},P_{6\to9},P_{6\to10}};\ \ctrec{\ctnone}\).",
        "input": "A validated dormant-structure datum, ambient object, branch state, and activity ledger.",
        "parameters": "Five independent proof-producing plans for scope, the active/dormant definition, activity classification, active-ledger certification, and dormant routing, plus a separate consumer port.",
        "execution": "Admit a finite activity description, certify its definition, distinguish active from dormant structure, certify the active ledger, and classify dormant residual data.",
        "routing": "C1 is the closure terminal. Indexed payloads route active demand to CT4 and dormant data to CT3, CT7, CT9, or CT10.",
        "limit": "The activity predicate and ledger are certification boundaries; totality is relative to the five supplied node plans.",
        "certificates": ["C1"],
        "payloads": ["P_6_to_4", "P_6_to_3", "P_6_to_7", "P_6_to_9", "P_6_to_10"],
    },
    "CT7": {
        "version": "CT7-v1",
        "type": "exchange",
        "signature": r"\(P_{\ast\to7}\to \ctcert{C1,C2,C3};\ \ctint{P_{7\to3},P_{7\to12},P_{7\to10},P_{7\to16}};\ \ctrec{\ctnone}\).",
        "input": "A validated exchange site, two local realizations, ambient object, and branch state.",
        "parameters": "Six independent proof-producing plans for scope, exchange-context certification, distinction, realization, defect routing, and neutral routing, plus a separate consumer port.",
        "execution": "Admit the exchange site, certify its common context, distinguish the two realizations, test realization, classify a defect when present, and classify neutral data otherwise.",
        "routing": "C1, C2, and C3 are closure terminals. Indexed payloads route context data to CT3, peelable load to CT12, finite labels to CT10, and whole-object data to CT16.",
        "limit": "Exchange context and realization are explicit proof boundaries; totality is relative to the six supplied node plans.",
        "certificates": ["C1", "C2", "C3"],
        "payloads": ["P_7_to_3", "P_7_to_12", "P_7_to_10", "P_7_to_16"],
    },
    "CT8": {
        "version": "CT8-v1",
        "type": "pumping",
        "signature": r"\(P_{\ast\to8}\to \ctcert{C2,C5};\ \ctint{P_{8\to3},P_{8\to7},P_{8\to10}};\ \ctrec{\ctnone}\).",
        "input": "A validated repeated-state sequence, finite state alphabet, ambient object, and branch state.",
        "parameters": "Five independent proof-producing plans for scope, repetition, pumping equivalence, response classification, and residual routing, plus a separate consumer port.",
        "execution": "Admit a finite-state trace, locate a repetition, certify the pump equivalence, classify its response, and route the non-closing residual.",
        "routing": "C2 and C5 are closure terminals. Indexed payloads route external types to CT3, exchange structure to CT7, and refined labels to CT10.",
        "limit": "Finite state and pumping equivalence are certification boundaries; totality is relative to the five supplied node plans.",
        "certificates": ["C2", "C5"],
        "payloads": ["P_8_to_3", "P_8_to_7", "P_8_to_10"],
    },
    "CT9": {
        "version": "CT9-v1",
        "type": "overload",
        "signature": r"\(P_{4\to9}\to \ctcert{C1};\ \ctint{P_{9\to7},P_{9\to8}};\ \ctrec{P_{9\to4},P_{9\to10}}\).",
        "input": "A validated overloaded payer fibre, capacity datum, ambient object, and branch state.",
        "parameters": "Five independent proof-producing plans for scope, fibre certification, overload classification, witness extraction, and routing, plus a separate consumer port.",
        "execution": "Admit a finite fibre, certify it, separate bounded from overloaded fibres, extract a repeated witness, and classify that witness.",
        "routing": "C1 is the closure terminal. Indexed payloads route bounded demand to CT4, exchange data to CT7, repetition to CT8, and a finite-description gap to CT10.",
        "limit": "The fibre and extraction certificates must retain their source ledger; totality is relative to the five supplied node plans.",
        "certificates": ["C1"],
        "payloads": ["P_9_to_4", "P_9_to_7", "P_9_to_8", "P_9_to_10"],
    },
    "CT10": {
        "version": "CT10-v1",
        "type": "refinement",
        "signature": r"\(P_{\ast\to10}\to \ctcert{C5};\ \ctint{P_{10\to3},P_{10\to7},P_{10\to15}};\ \ctrec{\ctnone}\).",
        "input": "A validated finite-label datum, residual object, ambient object, and branch state.",
        "parameters": "Six independent proof-producing plans for scope, label certification, classification, direct routing, promotion, and promoted routing, plus a separate consumer port.",
        "execution": "Admit finite labels, certify exhaustiveness, classify the current datum, route direct classes, or certify and route a promoted missing invariant.",
        "routing": "C5 is the closure terminal. Indexed payloads route response data to CT3, exchange data to CT7, and promoted rank data to CT15.",
        "limit": "Label exhaustiveness and promotion are separate certification boundaries; totality is relative to the six supplied node plans.",
        "certificates": ["C5"],
        "payloads": ["P_10_to_3", "P_10_to_7", "P_10_to_15"],
    },
    "CT11": {
        "version": "CT11-v1",
        "type": "localization",
        "signature": r"\(P_{5\to11}\to \ctcert{\ctnone};\ \ctint{P_{11\to1},P_{11\to7},P_{11\to14}};\ \ctrec{P_{11\to10}}.\)",
        "input": "A validated additive deficit, admissible decomposition, admissibility class, and bounded local type.",
        "parameters": "Five proof-producing plans for scope, decomposition, admissibility, localization, and routing, plus a separate consumer port.",
        "execution": "Certify the decomposition, decide admissibility closure, certify summation and a localized deficit, and classify the localized object.",
        "routing": "CT11 is route-only. Exact inputs route to CT1, CT7, CT10, or CT14.",
        "limit": "An admissibility gap cannot enter localization; it is an explicit CT10 terminal.",
        "certificates": [],
        "payloads": ["P_11_to_1", "P_11_to_7", "P_11_to_10", "P_11_to_14"],
    },
    "CT12": {
        "version": "CT12-v1",
        "type": "loop",
        "signature": r"\(P_{\ast\to12}\to \ctcert{C4};\ \ctint{\ctnone};\ \ctrec{P_{12\to4},P_{12\to13}}.\)",
        "input": "A validated branch state, routed-load account, peel move, and natural-valued load.",
        "parameters": "Six proof-producing plans for scope, initial measure, saturation, canonical peeling, restoration, and strict decrease, plus a separate consumer port.",
        "execution": "Certify the initial invariant, decide saturation, peel one unit, restore the state, certify strict decrease, and recurse on the smaller load.",
        "routing": "The unsaturated state closes by C4. Restoration demand routes by exact inputs to CT4 or CT13.",
        "limit": "Only DecreasedState licenses the back edge; restoration without strict decrease cannot recurse.",
        "certificates": ["C4"],
        "payloads": ["P_12_to_4", "P_12_to_13"],
        "cycle": {
            "hasCycles": True,
            "cycles": [["CT12.decide.saturation", "CT12.certify.peel", "CT12.decide.restoration", "CT12.certify.decrease", "CT12.decide.saturation"]],
            "cycleKinds": ["execution_loop"],
            "requiresWellFoundedMeasure": True,
        },
    },
    "CT13": {
        "version": "CT13-v1",
        "type": "tiered_charging",
        "signature": r"\(P_{\ast\to13}\to \ctcert{C4};\ \ctint{P_{13\to4},P_{13\to9},P_{13\to14}};\ \ctrec{\ctnone}.\)",
        "input": "A validated tier account, availability datum, measurable resource, and branch state.",
        "parameters": "Eight proof-producing plans separating scope, availability, tier-one payment and routing, fallback, reconciliation, comparison, and overlap routing.",
        "execution": "Decide tier-one availability, certify the selected payment scheme, reconcile payer resources, and close or classify a named overlap.",
        "routing": "Reconciled capacity closes by C4; exact inputs route tier-one accounts to CT4, overlap fibres to CT9, and overlap mass to CT14.",
        "limit": "Fallback requires a minimal canonical obstruction, and overlap routing requires an explicit failed reconciliation state.",
        "certificates": ["C4"],
        "payloads": ["P_13_to_4", "P_13_to_9", "P_13_to_14"],
    },
    "CT14": {
        "version": "CT14-v1",
        "type": "aggregate",
        "signature": r"\(P_{\ast\to14}\to \ctcert{C4};\ \ctint{\ctnone};\ \ctrec{P_{14\to9},P_{14\to10}}.\)",
        "input": "A validated residual class, lower mass, capacity record, multiplicity record, and branch state.",
        "parameters": "Four proof-producing plans for scope, bound certification, multiplicity classification, and aggregate comparison.",
        "execution": "Certify lower and upper bounds, account for carried multiplicity, and compare the estimates in the same units.",
        "routing": "The comparison closes by C4; exact failure inputs route to CT9 or CT10.",
        "limit": "Bounds alone cannot close the branch; a carried-charge multiplicity certificate is mandatory.",
        "certificates": ["C4"],
        "payloads": ["P_14_to_9", "P_14_to_10"],
    },
    "CT15": {
        "version": "CT15-v1",
        "type": "rank",
        "signature": r"\(P_{\ast\to15}\to \ctcert{C4};\ \ctint{P_{15\to3},P_{15\to7},P_{15\to16},P_{15\to4}};\ \ctrec{\ctnone}.\)",
        "input": "A validated test family, target-relative rank map, target datum, capacity datum, and branch state.",
        "parameters": "Six proof-producing plans for scope, rank certification, rank-drop classification, dependence routing, ledger certification, and comparison.",
        "execution": "Certify target meaning, separate structural dependence from full rank, and spend capacity only on certified independent coordinates.",
        "routing": "Rank dependence routes by exact inputs to CT3, CT7, or CT16; full rank closes by C4 or routes a ledger to CT4.",
        "limit": "The dependence branch has no constructor for a rank ledger.",
        "certificates": ["C4"],
        "payloads": ["P_15_to_3", "P_15_to_7", "P_15_to_16", "P_15_to_4"],
    },
    "CT16": {
        "version": "CT16-v1",
        "type": "exact_type",
        "signature": r"\(P_{\ast\to16}\to \ctcert{C2};\ \ctint{P_{16\to3},P_{16\to10}};\ \ctrec{\ctnone}.\)",
        "input": "A validated support, whole-object datum, closed-type datum, and branch state.",
        "parameters": "Four proof-producing plans for support, whole-object scope, closed-type certification, and literal equality.",
        "execution": "Route proper support immediately; for whole support, certify an exact closed type and decide literal equality.",
        "routing": "Literal equality closes by C2; exact inputs route proper pieces to CT3 and distinct closed data to CT10.",
        "limit": "Finite closed-type scope is required only after the support decision proves that the datum is whole-object.",
        "certificates": ["C2"],
        "payloads": ["P_16_to_3", "P_16_to_10"],
    },
    "CT17": {
        "version": "CT17-v1",
        "type": "target_thickening",
        "signature": r"\(P_{1\to17}\to \ctcert{C1,C5};\ \ctint{P_{17\to8},P_{17\to14}};\ \ctrec{P_{17\to3},P_{17\to10}}.\)",
        "input": "A validated sparse target, bounded offsets, completion classes, arithmetic datum, and branch state.",
        "parameters": "Seven proof-producing plans for scope, compatibility, separation, block certification, scale, finite survivors, and arithmetic.",
        "execution": "Separate incompatible completions before block construction, certify a common-state target block, split scale, and classify finite or arithmetic survivors.",
        "routing": "Finite exhaustion closes by C5 and arithmetic forcing closes by C1; exact inputs route to CT3, CT8, CT10, or CT14.",
        "limit": "Incompatible offsets cannot be pooled, and finite-range and repeated-increment residuals have distinct payload types.",
        "certificates": ["C1", "C5"],
        "payloads": ["P_17_to_3", "P_17_to_10", "P_17_to_8", "P_17_to_14"],
    },
}


def typed(item: dict, role: str | None = None) -> dict:
    value_kind = item.get("valueKind")
    inferred = (
        "parameter" if value_kind in {"algorithm", "type"}
        else "certificate" if value_kind in {"certificate", "proof"}
        else "payload" if value_kind == "payload"
        else "consumed"
    )
    return {"name": item["slotId"], "sort": item["typeExpression"], "role": role or inferred}


def is_closure(case: str | None) -> bool:
    return bool(case and len(case) > 1 and case[0] == "c" and case[1].isdigit())


def convert_nodes(tactic: dict, formal_nodes: list[dict]) -> list[dict]:
    manuscript_lines = MANUSCRIPT.read_text(encoding="utf-8").splitlines()
    source_lines = {
        node["nodeId"]: next(
            number
            for number, line in enumerate(manuscript_lines, 1)
            if node["nodeId"] in line.replace(r"\allowbreak ", "")
        )
        for node in formal_nodes
    }
    incoming: dict[str, list[str]] = defaultdict(list)
    outgoing: dict[str, list[dict]] = defaultdict(list)
    for edge in tactic["transitions"]:
        incoming[edge["toNodeId"]].append(edge["fromNodeId"])
        outgoing[edge["fromNodeId"]].append(edge)
    tactic_number = tactic["tacticId"][2:]
    result = []
    for number, node in enumerate(formal_nodes, 1):
        node_id = node["nodeId"]
        kind = node["nodeKind"]
        terminal = node.get("terminal")
        case = terminal.get("terminalCase") if terminal else None
        closure = is_closure(case)
        node_type = (
            "loop_measure" if node_id in {"CT12.certify.measure", "CT12.certify.decrease"}
            else "input" if kind == "entry" else "decision" if kind == "decision"
            else "assertion" if kind == "certification" else "scope_audit" if case == "scope"
            else "certificate" if closure else "consumer_handoff"
        )
        modality = (
            "validate" if kind == "entry" or closure else "decide" if kind == "decision"
            else "prove" if kind == "certification" else "audit" if case == "scope" else "construct"
        )
        dependencies = list(dict.fromkeys(incoming[node_id]))
        inputs = [typed(item) for item in node["formalContract"]["inputs"]]
        outputs = [typed(item, "produced") for item in node["formalContract"]["outputs"]]
        if case and case.startswith("ct"):
            outputs = [{
                "name": f"P_{tactic_number}_to_{case[2:]}",
                "sort": node["formalContract"]["inputs"][-1]["typeExpression"],
                "role": "payload",
            }]
        converted = {
            "artifactType": "nodeSpec", "schemaVersion": "1.0.0",
            "nodeNumber": number, "nodeId": node_id,
            "localKey": node_id.split(".")[-1], "nodeType": node_type,
            "runtimeKind": kind, "title": node["title"],
            "labelLatex": node["human"].get("latex") or node["title"],
            "obligation": {
                "obligationId": f"{node_id}.O1", "modality": modality,
                "statement": {"informal": node["human"]["informal"], "latex": node["human"].get("latex", "")},
                "contractSchemas": node["contracts"], "dependencies": dependencies,
                "dischargeCriteria": node["formalContract"]["dischargeCondition"],
            },
            "inputs": inputs, "outputs": outputs, "dependsOn": dependencies,
            "outgoingTransitionIds": [edge["transitionId"] for edge in outgoing[node_id]],
            "terminalRole": "none" if not terminal else "scope_audit" if case == "scope" else "certificate" if closure else "consumer_handoff",
            "source": {
                "file": "branch_closure_methodology_extended.tex", "section": tactic["source"]["section"],
                "line": source_lines[node_id], "diagramKey": node["source"]["diagramKey"],
            },
        }
        if kind == "decision":
            converted["branches"] = [
                {
                    "transitionId": branch["transitionId"], "guard": branch["branchTag"],
                    "targetNodeId": next(edge["toNodeId"] for edge in tactic["transitions"] if edge["transitionId"] == branch["transitionId"]),
                    "resultConstructor": branch["resultConstructorRef"]["declaration"],
                    "evidenceSlots": [typed(item, "payload" if item["valueKind"] == "payload" else "produced") for item in branch["evidenceSlots"]],
                }
                for branch in node["formalContract"]["branches"]
            ]
        if node_type == "loop_measure":
            converted["measure"] = {
                "name": "recorded routed load",
                "wellFoundedOrder": "Nat with strict order (<)",
                "strictDecreaseRequired": True,
            }
        if terminal:
            converted["terminalCase"] = case
            if case == "scope":
                converted["scopeAudit"] = {
                    "classification": "candidate_scope_obstruction",
                    "requiredFinding": "Retain the typed negative scope proof and refer the expressibility limit to the global scope audit.",
                }
            elif closure:
                converted["certificate"] = {
                    "class": case.upper(),
                    "validationStatement": f"The indexed {case.upper()} certificate proves the exact closure claim declared by the framework.",
                }
            else:
                converted["consumer"] = {"tacticId": case.upper(), "triggerContract": "S-Trig"}
        result.append(converted)
    return result


def convert_transitions(tactic: dict) -> list[dict]:
    result = []
    for number, edge in enumerate(tactic["transitions"], 1):
        guard = edge["guard"]
        is_loop = edge["transitionId"] == "CT12.edge.decrease.loop"
        converted = {
            "transitionNumber": number, "transitionId": edge["transitionId"],
            "fromNodeId": edge["fromNodeId"], "toNodeId": edge["toNodeId"],
            "transitionType": "loop" if is_loop else "scope" if edge["kind"] == "scope" else "handoff" if edge["kind"] == "handoff" else "intended",
            "guard": guard["branchTag"], "guardLatex": guard["branchTag"],
            "sourceStyle": "bcloop" if is_loop else "bcscopearr" if edge["kind"] == "scope" else "bchandoff" if edge["kind"] == "handoff" else "bcarr",
            "branchTag": guard["branchTag"],
            "transitionConstructor": edge["transitionConstructorRef"]["declaration"],
            "evidenceSlots": [typed(item, "payload" if item["valueKind"] == "payload" else "produced") for item in guard["evidenceSlots"]],
        }
        if constructor := guard.get("resultConstructorRef"):
            converted["resultConstructor"] = constructor["declaration"]
        result.append(converted)
    return result


def build_tactic(formal: dict, formal_nodes: list[dict], cfg: dict) -> dict:
    nodes = convert_nodes(formal, formal_nodes)
    return {
        "artifactType": "tacticSpec", "schemaVersion": "1.0.0",
        "graphVersion": cfg["version"], "tacticId": formal["tacticId"],
        "name": formal["name"], "tacticType": cfg["type"],
        "signature": {"latex": cfg["signature"], "inputDescription": cfg["input"], "parameterDescription": cfg["parameters"]},
        "mechanism": {"execution": cfg["execution"], "routing": cfg["routing"], "limit": cfg["limit"]},
        "entryNodeIds": [formal["entryNodeId"]], "nodes": nodes,
        "transitions": convert_transitions(formal),
        "allowedCertificates": cfg["certificates"], "declaredPayloads": cfg["payloads"],
        "scopeCandidateNodeIds": [node["nodeId"] for node in nodes if node.get("terminalCase") == "scope"],
        "auditRejectNodeIds": [],
        "completeness": {
            "numberingPolicy": "Numeric fields are presentation order; semantic IDs are stable runtime identities.",
            "noUnnamedResiduals": True, "allSinksTyped": True,
            "uniqueConsumerPerPayload": True, "allDecisionBranchesExplicit": True,
        },
        "totality": {
            "relativeToSuppliedPlans": True, "terminalCases": formal["terminalCases"],
            "statement": f"For every validated input, CorePlan, Port, and HandoffPlan, run_total produces one indexed {formal['tacticId']} outcome and one evidence-carrying path.",
        },
        "cyclePolicy": cfg.get("cycle", {
            "hasCycles": False,
            "cycles": [],
            "cycleKinds": [],
            "requiresWellFoundedMeasure": False,
        }),
        "source": {
            "file": "branch_closure_methodology_extended.tex", "section": formal["source"]["section"],
            "line": next(number for number, line in enumerate(MANUSCRIPT.read_text(encoding="utf-8").splitlines(), 1) if line.startswith(fr"\subsection{{{formal['tacticId']}")),
        },
    }


def status(node: dict) -> tuple[str, str]:
    if node.get("terminalCase") == "scope":
        return "scope_candidate", "Required typed scope-candidate completion state."
    if node["runtimeKind"] in {"decision", "certification"}:
        return "proved", "Required successful proof state for this executable machine node."
    return "validated", "Required successful validation state for this entry or terminal node."


def node_schema(tactic: dict, node: dict) -> dict:
    state, state_description = status(node)
    contracts = node["obligation"]["contractSchemas"]
    properties = {
        "tacticId": {"description": f"Owning tactic discriminator for {node['nodeId']}.", "const": tactic["tacticId"]},
        "nodeId": {"description": f"Stable semantic runtime identifier for {node['title']}.", "const": node["nodeId"]},
        "nodeNumber": {"description": f"One-based presentation index for {node['nodeId']}.", "const": node["nodeNumber"]},
        "status": {"description": state_description, "const": state},
        "dischargedContracts": {
            "description": f"Exact contract families discharged at {node['nodeId']}.", "type": "array",
            "uniqueItems": True, "minItems": len(contracts), "maxItems": len(contracts),
            "allOf": [{"contains": {"description": f"Required {contract} evidence.", "const": contract}} for contract in contracts],
        },
        "contractInstances": {
            "description": f"Typed contract instances for every family declared at {node['nodeId']}.",
            "type": "array", "minItems": len(contracts),
            "allOf": [
                {"contains": {"required": ["schema"], "properties": {"schema": {"description": f"Required {contract} discriminator.", "const": contract}}}}
                for contract in contracts
            ],
        },
    }
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": f"https://example.org/structural-exhaustion/concrete/nodes/{node['nodeId']}.schema.json",
        "title": f"{node['nodeId']} completed discharge record — {node['title']}",
        "description": f"Concrete completed-discharge schema for semantic {tactic['graphVersion']} node {node['nodeId']}.",
        "allOf": [
            {"$ref": "../../structural-exhaustion.bundle.schema.json#/$defs/nodeProofRecord"},
            {"properties": properties, "required": list(properties)},
        ],
        "x-obligation": node["obligation"],
    }


def tactic_schema(tactic: dict) -> dict:
    node_items = []
    for node in tactic["nodes"]:
        props = {
            "nodeId": {"description": f"Exact runtime identity for {node['title']}.", "const": node["nodeId"]},
            "nodeNumber": {"description": f"Presentation index for {node['nodeId']}.", "const": node["nodeNumber"]},
            "nodeType": {"description": f"Mathematical role of {node['nodeId']}.", "const": node["nodeType"]},
            "runtimeKind": {"description": f"Machine role of {node['nodeId']}.", "const": node["runtimeKind"]},
        }
        if case := node.get("terminalCase"):
            props["terminalCase"] = {"description": f"Exact terminal case for {node['nodeId']}.", "const": case}
        node_items.append({"allOf": [{"$ref": "../../structural-exhaustion.bundle.schema.json#/$defs/nodeSpec"}, {"properties": props, "required": list(props)}]})
    edge_items = []
    for edge in tactic["transitions"]:
        props = {
            "transitionId": {"description": "Exact semantic transition identity.", "const": edge["transitionId"]},
            "transitionNumber": {"description": "One-based presentation transition index.", "const": edge["transitionNumber"]},
            "fromNodeId": {"description": "Exact typed source state.", "const": edge["fromNodeId"]},
            "toNodeId": {"description": "Exact typed target state.", "const": edge["toNodeId"]},
        }
        edge_items.append({"properties": props, "required": list(props)})
    count, edge_count = len(node_items), len(edge_items)
    props = {
        "tacticId": {"description": f"Required {tactic['tacticId']} discriminator.", "const": tactic["tacticId"]},
        "graphVersion": {"description": "Required semantic graph version.", "const": tactic["graphVersion"]},
        "entryNodeIds": {"description": "The unique semantic entry node.", "const": tactic["entryNodeIds"]},
        "nodes": {"description": f"Exact {count}-node machine in presentation order.", "type": "array", "prefixItems": node_items, "items": False, "minItems": count, "maxItems": count},
        "transitions": {"description": f"Exact {edge_count} typed edges in presentation order.", "type": "array", "prefixItems": edge_items, "items": False, "minItems": edge_count, "maxItems": edge_count},
    }
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": f"https://example.org/structural-exhaustion/concrete/tactics/{tactic['tacticId']}.schema.json",
        "title": f"{tactic['graphVersion']} semantic runtime graph — {tactic['name']}",
        "description": f"Concrete static-graph schema for the exact {tactic['graphVersion']} sequential machine.",
        "allOf": [{"$ref": "../../structural-exhaustion.bundle.schema.json#/$defs/tacticSpec"}, {"properties": props, "required": list(props)}],
    }


def verification_schema(tactic: dict) -> dict:
    refs = [{"$ref": f"../nodes/{node['nodeId']}.schema.json"} for node in tactic["nodes"]]
    count = len(refs)
    props = {
        "tacticId": {"description": f"Required {tactic['tacticId']} verification discriminator.", "const": tactic["tacticId"]},
        "nodeRecords": {"description": f"Exactly one completed record for each {tactic['graphVersion']} node.", "type": "array", "prefixItems": refs, "items": False, "minItems": count, "maxItems": count},
    }
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": f"https://example.org/structural-exhaustion/concrete/verifications/{tactic['tacticId']}.verification.schema.json",
        "title": f"{tactic['graphVersion']} structural all-node verification",
        "description": f"Requires structural coverage of all {count} semantic states; it does not claim automatic witness search.",
        "allOf": [{"$ref": "../../structural-exhaustion.bundle.schema.json#/$defs/tacticVerification"}, {"properties": props, "required": list(props)}],
    }


def run_schema(tactic: dict) -> dict:
    ids = [node["nodeId"] for node in tactic["nodes"]]
    refs = [{"$ref": f"../nodes/{node_id}.schema.json"} for node_id in ids]
    props = {
        "tacticId": {"description": f"Required {tactic['tacticId']} run discriminator.", "const": tactic["tacticId"]},
        "visitedNodeIds": {"description": f"Execution path using only {tactic['graphVersion']} semantic IDs.", "type": "array", "items": {"enum": ids}, "minItems": 2},
        "nodeRecords": {"description": "Proof records aligned with the visited path.", "type": "array", "items": {"oneOf": refs}, "minItems": 2},
        "outcome": {"description": f"Exact terminal result of the {tactic['graphVersion']} run.", "properties": {"terminalCase": {"description": "Exact terminal-case discriminator.", "enum": tactic["totality"]["terminalCases"]}}, "required": ["terminalCase"]},
    }
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": f"https://example.org/structural-exhaustion/concrete/runs/{tactic['tacticId']}.run.schema.json",
        "title": f"{tactic['graphVersion']} legal semantic-machine run",
        "description": f"A legal path begins at {tactic['entryNodeIds'][0]}, follows typed edges, and ends at one exact terminal.",
        "allOf": [{"$ref": "../../structural-exhaustion.bundle.schema.json#/$defs/tacticRun"}, {"properties": props, "required": list(props)}],
        "x-semanticValidationRules": ["validate visitedNodeIds against the semantic transition graph", "require the final node and outcome terminalCase to agree"],
    }


def main() -> int:
    library = load(DATA_PATH)
    concrete_nodes = SCHEMA_ROOT / "concrete/nodes"
    summaries = []
    for tactic_id, cfg in CONFIG.items():
        formal_path = FORMAL_ROOT / f"framework/{tactic_id}/tactic.json"
        formal = load(formal_path)
        formal_nodes = [load(formal_path.parent / ref) for ref in formal["nodeRefs"]]
        tactic = build_tactic(formal, formal_nodes, cfg)
        index = next(index for index, old in enumerate(library["tactics"]) if old["tacticId"] == tactic_id)
        library["tactics"][index] = tactic
        for path in concrete_nodes.glob(f"{tactic_id}.N*.schema.json"):
            path.unlink()
        for path in concrete_nodes.glob(f"{tactic_id}.*.schema.json"):
            path.unlink()
        for item in tactic["nodes"]:
            write(concrete_nodes / f"{item['nodeId']}.schema.json", node_schema(tactic, item))
        write(SCHEMA_ROOT / f"concrete/tactics/{tactic_id}.schema.json", tactic_schema(tactic))
        write(SCHEMA_ROOT / f"concrete/verifications/{tactic_id}.verification.schema.json", verification_schema(tactic))
        write(SCHEMA_ROOT / f"concrete/runs/{tactic_id}.run.schema.json", run_schema(tactic))
        summaries.append(f"{tactic_id}: {len(tactic['nodes'])} nodes, {len(tactic['transitions'])} transitions, {len(tactic['totality']['terminalCases'])} terminals")
    library["title"] = "Structural Exhaustion CT1–CT17 semantic tactic specifications"
    library["numberingConvention"] = "CT1-v1, CT2-v2, and CT3-v1 through CT17-v1 use stable semantic node and edge IDs. Numeric fields are one-based presentation order."
    write(DATA_PATH, library)
    write_node_index(library)
    print("Synchronized " + "; ".join(summaries))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
