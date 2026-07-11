#!/usr/bin/env python3
"""Generate the CT3-v1, CT4-v1, and CT5-v1 semantic specifications."""
from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def write(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def ref(declaration: str, source: str, kind: str, module: str) -> dict:
    return {
        "module": module,
        "declaration": declaration,
        "sourceFile": source,
        "declarationKind": kind,
    }


def slot(slot_id: str, value_kind: str, expression: str) -> dict:
    return {"slotId": slot_id, "valueKind": value_kind, "typeExpression": expression}


def bind(role: str, local: str, declaration: dict) -> dict:
    return {"role": role, "localName": local, "ref": declaration}


def node(node_id: str, kind: str, title: str, module: str | None = None,
         output: tuple[str, str, str] | None = None,
         terminal: dict | None = None) -> dict:
    return {
        "id": node_id,
        "kind": kind,
        "title": title,
        "module": module,
        "output": output,
        "terminal": terminal,
    }


def terminal(case: str, node_ctor: str, evidence: list[dict], claim: str) -> dict:
    return {"case": case, "nodeCtor": node_ctor, "evidence": evidence, "claim": claim}


def edge(edge_id: str, source: str, target: str, kind: str, ctor: str,
         tag: str, result_module: str | None = None,
         result_ctor: str | None = None, evidence: list[dict] | None = None) -> dict:
    return {
        "id": edge_id,
        "source": source,
        "target": target,
        "kind": kind,
        "ctor": ctor,
        "tag": tag,
        "resultModule": result_module,
        "resultCtor": result_ctor,
        "evidence": evidence or [],
    }


def ct3_config() -> dict:
    ns = "StructuralExhaustion.CT3"
    entry, scope, scope_t = "CT3.entry", "CT3.decide.scope", "CT3.terminal.scope"
    equiv, comp, c2 = "CT3.certify.equivalence", "CT3.decide.compression", "CT3.terminal.c2"
    defect, c3, ct7, ct12 = "CT3.decide.defect", "CT3.terminal.c3", "CT3.terminal.ct7", "CT3.terminal.ct12"
    table, c5, ct8 = "CT3.decide.table", "CT3.terminal.c5", "CT3.terminal.ct8"
    nodes = [
        node(entry, "entry", "Validated CT3 entry", "Entry"),
        node(scope, "decision", "Finite external-type scope", "Scope"),
        node(scope_t, "terminal", "Infinite-index scope terminal", terminal=terminal(
            "scope", "scopeTerminal", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")],
            f"¬ {ns}.TypeIndexFiniteAt framework input")),
        node(equiv, "certification", "External-type equivalence certification", "Equivalence",
             ("equivalence", "certificate", f"{ns}.EquivalenceState framework input")),
        node(comp, "decision", "Replacement compression decision", "Compression"),
        node(c2, "terminal", "C2 replacement terminal", terminal=terminal(
            "c2", "c2Terminal", [slot("certificate", "certificate", f"{ns}.C2Certificate framework input equivalence")],
            "framework.C2Claim input.G input.branch")),
        node(defect, "decision", "External-type defect classification", "Defect"),
        node(c3, "terminal", "C3 routed-account terminal", terminal=terminal(
            "c3", "c3Terminal", [slot("certificate", "certificate", f"{ns}.C3Certificate framework input state")],
            "framework.C3Claim input.G input.branch")),
        node(ct7, "terminal", "CT7 exchange handoff", terminal=terminal(
            "ct7", "ct7Terminal", [slot("payload", "payload", f"{ns}.CT7Payload framework input state")],
            "port.accepts (.ct7 payload)")),
        node(ct12, "terminal", "CT12 peeling handoff", terminal=terminal(
            "ct12", "ct12Terminal", [slot("payload", "payload", f"{ns}.CT12Payload framework input state")],
            "port.accepts (.ct12 payload)")),
        node(table, "decision", "Finite-table classification", "Table"),
        node(c5, "terminal", "C5 finite-table terminal", terminal=terminal(
            "c5", "c5Terminal", [slot("certificate", "certificate", f"{ns}.C5Certificate framework input persistent")],
            "framework.C5Claim input.G input.branch")),
        node(ct8, "terminal", "CT8 repeated-type handoff", terminal=terminal(
            "ct8", "ct8Terminal", [slot("payload", "payload", f"{ns}.CT8Payload framework input persistent")],
            "port.accepts (.ct8 payload)")),
    ]
    edges = [
        edge("CT3.edge.begin", entry, scope, "advance", "beginScope", "begin"),
        edge("CT3.edge.scope.exit", scope, scope_t, "scope", "scopeExit", "exit", "Scope", "exit",
             [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")]),
        edge("CT3.edge.scope.ready", scope, equiv, "advance", "scopeReady", "ready", "Scope", "ready",
             [slot("scopeState", "state", f"{ns}.ScopedState framework input")]),
        edge("CT3.edge.equivalence.certified", equiv, comp, "advance", "equivalenceCertified", "certified",
             evidence=[slot("equivalence", "state", f"{ns}.EquivalenceState framework input")]),
        edge("CT3.edge.compression.close", comp, c2, "close", "compressionClose", "close", "Compression", "close",
             [slot("certificate", "certificate", f"{ns}.C2Certificate framework input equivalence")]),
        edge("CT3.edge.compression.residual", comp, defect, "advance", "compressionResidual", "residual", "Compression", "residual",
             [slot("state", "state", f"{ns}.UncompressibleState framework input equivalence")]),
        edge("CT3.edge.defect.close", defect, c3, "close", "defectClose", "close", "Defect", "close",
             [slot("certificate", "certificate", f"{ns}.C3Certificate framework input state")]),
        edge("CT3.edge.defect.ct7", defect, ct7, "handoff", "defectToCT7", "toCT7", "Defect", "toCT7",
             [slot("payload", "payload", f"{ns}.CT7Payload framework input state")]),
        edge("CT3.edge.defect.ct12", defect, ct12, "handoff", "defectToCT12", "toCT12", "Defect", "toCT12",
             [slot("payload", "payload", f"{ns}.CT12Payload framework input state")]),
        edge("CT3.edge.defect.persistent", defect, table, "advance", "defectPersistent", "persistent", "Defect", "persistent",
             [slot("persistent", "state", f"{ns}.PersistentState framework input state")]),
        edge("CT3.edge.table.close", table, c5, "close", "tableClose", "close", "Table", "close",
             [slot("certificate", "certificate", f"{ns}.C5Certificate framework input persistent")]),
        edge("CT3.edge.table.ct8", table, ct8, "handoff", "tableToCT8", "toCT8", "Table", "toCT8",
             [slot("payload", "payload", f"{ns}.CT8Payload framework input persistent")]),
    ]
    contracts = {
        entry: ["S-Def"], scope: ["S-Dich", "A-Scope"], scope_t: ["A-Scope"],
        equiv: ["S-Equiv"], comp: ["S-Dich", "S-Equiv", "S-Comp"], c2: ["S-Comp", "A-Cert"],
        defect: ["S-Dich", "S-Pers", "S-Rout"], c3: ["S-Rout", "A-Cert"],
        ct7: ["S-Pers", "S-Rout", "S-Trig"], ct12: ["S-Pers", "S-Rout", "S-Trig"],
        table: ["S-Dich", "S-Pers", "S-Comp"], c5: ["S-Comp", "A-Cert"],
        ct8: ["S-Pers", "S-Rout", "S-Trig"],
    }
    common = [entry, scope, equiv, comp]
    instances = [
        instance("scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff", "scopeResult", "scope_terminal", "scope_trace", [entry, scope, scope_t], ["CT3.edge.begin", "CT3.edge.scope.exit"]),
        instance("c2", "compressionFramework", "compressionInput", "compressionPlan", "compressionPort", "compressionHandoff", "c2Result", "c2_terminal", "c2_trace", common + [c2], ["CT3.edge.begin", "CT3.edge.scope.ready", "CT3.edge.equivalence.certified", "CT3.edge.compression.close"]),
        instance("c3", "framework", "input", "c3Plan", "port", "handoff", "c3Result", "c3_terminal", "c3_trace", common + [defect, c3], ["CT3.edge.begin", "CT3.edge.scope.ready", "CT3.edge.equivalence.certified", "CT3.edge.compression.residual", "CT3.edge.defect.close"]),
        instance("ct7", "framework", "input", "ct7Plan", "port", "handoff", "ct7Result", "ct7_terminal", "ct7_trace", common + [defect, ct7], ["CT3.edge.begin", "CT3.edge.scope.ready", "CT3.edge.equivalence.certified", "CT3.edge.compression.residual", "CT3.edge.defect.ct7"]),
        instance("ct12", "framework", "input", "ct12Plan", "port", "handoff", "ct12Result", "ct12_terminal", "ct12_trace", common + [defect, ct12], ["CT3.edge.begin", "CT3.edge.scope.ready", "CT3.edge.equivalence.certified", "CT3.edge.compression.residual", "CT3.edge.defect.ct12"]),
        instance("c5", "framework", "input", "c5Plan", "port", "handoff", "c5Result", "c5_terminal", "c5_trace", common + [defect, table, c5], ["CT3.edge.begin", "CT3.edge.scope.ready", "CT3.edge.equivalence.certified", "CT3.edge.compression.residual", "CT3.edge.defect.persistent", "CT3.edge.table.close"]),
        instance("ct8", "framework", "input", "ct8Plan", "port", "handoff", "ct8Result", "ct8_terminal", "ct8_trace", common + [defect, table, ct8], ["CT3.edge.begin", "CT3.edge.scope.ready", "CT3.edge.equivalence.certified", "CT3.edge.compression.residual", "CT3.edge.defect.persistent", "CT3.edge.table.ct8"]),
    ]
    return config("CT3", "External-type compression", "CT3 — External-type compression", nodes, edges, contracts, instances,
                  {"close": ["C2", "C3", "C5"], "handoff": ["P_3_to_7", "P_3_to_12", "P_3_to_8"]},
                  ["EquivalenceState", "UncompressibleState", "PersistentState", "C2Certificate", "C3Certificate", "C5Certificate"])


def ct4_config() -> dict:
    ns = "StructuralExhaustion.CT4"
    entry, scope, scope_t = "CT4.entry", "CT4.decide.scope", "CT4.terminal.scope"
    assign, avail, ct13 = "CT4.certify.assignment", "CT4.decide.availability", "CT4.terminal.ct13"
    fibres, ct9 = "CT4.decide.fibres", "CT4.terminal.ct9"
    compare, c4, ct14 = "CT4.decide.comparison", "CT4.terminal.c4", "CT4.terminal.ct14"
    nodes = [
        node(entry, "entry", "Validated CT4 ledger entry", "Entry"),
        node(scope, "decision", "Demand-family scope", "Scope"),
        node(scope_t, "terminal", "Missing-demand scope terminal", terminal=terminal("scope", "scopeTerminal", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")], f"¬ {ns}.ScopeReadyAt framework input")),
        node(assign, "certification", "Canonical assignment certification", "Assignment", ("assignment", "certificate", f"{ns}.AssignmentState framework input")),
        node(avail, "decision", "Payer availability decision", "Availability"),
        node(ct13, "terminal", "CT13 missing-tier handoff", terminal=terminal("ct13", "ct13Terminal", [slot("payload", "payload", f"{ns}.CT13Payload framework input assignment")], "port.accepts (.ct13 payload)")),
        node(fibres, "decision", "Fibre-capacity decision", "Fibres"),
        node(ct9, "terminal", "CT9 overload handoff", terminal=terminal("ct9", "ct9Terminal", [slot("payload", "payload", f"{ns}.CT9Payload framework input total")], "port.accepts (.ct9 payload)")),
        node(compare, "decision", "Capacity comparison", "Comparison"),
        node(c4, "terminal", "C4 capacity terminal", terminal=terminal("c4", "c4Terminal", [slot("certificate", "certificate", f"{ns}.C4Certificate framework input bounded")], "framework.C4Claim input.G input.branch")),
        node(ct14, "terminal", "CT14 aggregate handoff", terminal=terminal("ct14", "ct14Terminal", [slot("payload", "payload", f"{ns}.CT14Payload framework input bounded")], "port.accepts (.ct14 payload)")),
    ]
    edges = [
        edge("CT4.edge.begin", entry, scope, "advance", "beginScope", "begin"),
        edge("CT4.edge.scope.exit", scope, scope_t, "scope", "scopeExit", "exit", "Scope", "exit", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")]),
        edge("CT4.edge.scope.ready", scope, assign, "advance", "scopeReady", "ready", "Scope", "ready", [slot("scopeState", "state", f"{ns}.ScopedState framework input")]),
        edge("CT4.edge.assignment.certified", assign, avail, "advance", "assignmentCertified", "certified", evidence=[slot("assignment", "state", f"{ns}.AssignmentState framework input")]),
        edge("CT4.edge.availability.missing", avail, ct13, "handoff", "availabilityMissing", "missing", "Availability", "missing", [slot("payload", "payload", f"{ns}.CT13Payload framework input assignment")]),
        edge("CT4.edge.availability.total", avail, fibres, "advance", "availabilityTotal", "total", "Availability", "total", [slot("total", "state", f"{ns}.TotalAssignmentState framework input assignment")]),
        edge("CT4.edge.fibres.overloaded", fibres, ct9, "handoff", "fibresOverloaded", "overloaded", "Fibres", "overloaded", [slot("payload", "payload", f"{ns}.CT9Payload framework input total")]),
        edge("CT4.edge.fibres.bounded", fibres, compare, "advance", "fibresBounded", "bounded", "Fibres", "bounded", [slot("bounded", "state", f"{ns}.BoundedFibreState framework input total")]),
        edge("CT4.edge.comparison.close", compare, c4, "close", "comparisonClose", "close", "Comparison", "close", [slot("certificate", "certificate", f"{ns}.C4Certificate framework input bounded")]),
        edge("CT4.edge.comparison.residual", compare, ct14, "handoff", "comparisonResidual", "residual", "Comparison", "residual", [slot("payload", "payload", f"{ns}.CT14Payload framework input bounded")]),
    ]
    contracts = {
        entry: ["S-Def"], scope: ["S-Dich", "A-Scope"], scope_t: ["A-Scope"],
        assign: ["S-Det"], avail: ["S-Dich", "S-Det", "S-Rout"], ct13: ["S-Rout", "S-Trig"],
        fibres: ["S-Dich", "S-Comp", "S-Rout"], ct9: ["S-Rout", "S-Trig"],
        compare: ["S-Dich", "S-Comp"], c4: ["S-Comp", "A-Cert"], ct14: ["S-Rout", "S-Trig"],
    }
    prefix = [entry, scope, assign, avail]
    instances = [
        instance("scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff", "scopeResult", "scope_terminal", "scope_trace", [entry, scope, scope_t], ["CT4.edge.begin", "CT4.edge.scope.exit"]),
        instance("ct13", "missingFramework", "missingInput", "missingPlan", "missingPort", "missingHandoff", "ct13Result", "ct13_terminal", "ct13_trace", prefix + [ct13], ["CT4.edge.begin", "CT4.edge.scope.ready", "CT4.edge.assignment.certified", "CT4.edge.availability.missing"]),
        instance("ct9", "framework", "input", "ct9Plan", "port", "handoff", "ct9Result", "ct9_terminal", "ct9_trace", prefix + [fibres, ct9], ["CT4.edge.begin", "CT4.edge.scope.ready", "CT4.edge.assignment.certified", "CT4.edge.availability.total", "CT4.edge.fibres.overloaded"]),
        instance("c4", "framework", "input", "c4Plan", "port", "handoff", "c4Result", "c4_terminal", "c4_trace", prefix + [fibres, compare, c4], ["CT4.edge.begin", "CT4.edge.scope.ready", "CT4.edge.assignment.certified", "CT4.edge.availability.total", "CT4.edge.fibres.bounded", "CT4.edge.comparison.close"]),
        instance("ct14", "framework", "input", "ct14Plan", "port", "handoff", "ct14Result", "ct14_terminal", "ct14_trace", prefix + [fibres, compare, ct14], ["CT4.edge.begin", "CT4.edge.scope.ready", "CT4.edge.assignment.certified", "CT4.edge.availability.total", "CT4.edge.fibres.bounded", "CT4.edge.comparison.residual"]),
    ]
    return config("CT4", "Deterministic charging schemes", "CT4 — Charging schemes", nodes, edges, contracts, instances,
                  {"close": ["C4"], "handoff": ["P_4_to_9", "P_4_to_14", "P_4_to_13"]},
                  ["AssignmentState", "TotalAssignmentState", "BoundedFibreState", "C4Certificate"])


def ct5_config() -> dict:
    ns = "StructuralExhaustion.CT5"
    entry, scope, scope_t = "CT5.entry", "CT5.decide.scope", "CT5.terminal.scope"
    locality, deficit, ct11 = "CT5.certify.locality", "CT5.decide.deficit", "CT5.terminal.ct11"
    summation, compare = "CT5.certify.summation", "CT5.decide.comparison"
    c4, ct4, ct14 = "CT5.terminal.c4", "CT5.terminal.ct4", "CT5.terminal.ct14"
    nodes = [
        node(entry, "entry", "Validated CT5 local-family entry", "Entry"),
        node(scope, "decision", "Bounded-witness scope", "Scope"),
        node(scope_t, "terminal", "Missing-local-witness scope terminal", terminal=terminal("scope", "scopeTerminal", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")], f"¬ {ns}.ScopeReadyAt framework input")),
        node(locality, "certification", "Locality certification", "Locality", ("locality", "certificate", f"{ns}.LocalityState framework input")),
        node(deficit, "decision", "Local-deficit classification", "Deficit"),
        node(ct11, "terminal", "CT11 additive-deficit handoff", terminal=terminal("ct11", "ct11Terminal", [slot("payload", "payload", f"{ns}.CT11Payload framework input locality")], "port.accepts (.ct11 payload)")),
        node(summation, "certification", "Local-to-global summation certification", "Summation", ("summation", "certificate", f"{ns}.SummationState framework input ledger")),
        node(compare, "decision", "Global comparison classification", "Comparison"),
        node(c4, "terminal", "C4 local-to-global terminal", terminal=terminal("c4", "c4Terminal", [slot("certificate", "certificate", f"{ns}.C4Certificate framework input summation")], "framework.ct4.C4Claim input.G input.branch")),
        node(ct4, "terminal", "CT4 ledger handoff", terminal=terminal("ct4", "ct4Terminal", [slot("payload", "payload", f"{ns}.CT4Payload framework input summation")], "port.accepts (.ct4 payload)")),
        node(ct14, "terminal", "CT14 aggregate handoff", terminal=terminal("ct14", "ct14Terminal", [slot("payload", "payload", f"{ns}.CT14Payload framework input summation")], "port.accepts (.ct14 payload)")),
    ]
    edges = [
        edge("CT5.edge.begin", entry, scope, "advance", "beginScope", "begin"),
        edge("CT5.edge.scope.exit", scope, scope_t, "scope", "scopeExit", "exit", "Scope", "exit", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")]),
        edge("CT5.edge.scope.ready", scope, locality, "advance", "scopeReady", "ready", "Scope", "ready", [slot("scopeState", "state", f"{ns}.ScopedState framework input")]),
        edge("CT5.edge.locality.certified", locality, deficit, "advance", "localityCertified", "certified", evidence=[slot("locality", "state", f"{ns}.LocalityState framework input")]),
        edge("CT5.edge.deficit.ct11", deficit, ct11, "handoff", "deficitToCT11", "toCT11", "Deficit", "toCT11", [slot("payload", "payload", f"{ns}.CT11Payload framework input locality")]),
        edge("CT5.edge.deficit.ledger", deficit, summation, "advance", "deficitLedger", "ledger", "Deficit", "ledger", [slot("ledger", "state", f"{ns}.LocalLedgerState framework input locality")]),
        edge("CT5.edge.summation.certified", summation, compare, "advance", "summationCertified", "certified", evidence=[slot("summation", "state", f"{ns}.SummationState framework input ledger")]),
        edge("CT5.edge.comparison.close", compare, c4, "close", "comparisonClose", "close", "Comparison", "close", [slot("certificate", "certificate", f"{ns}.C4Certificate framework input summation")]),
        edge("CT5.edge.comparison.ct4", compare, ct4, "handoff", "comparisonToCT4", "toCT4", "Comparison", "toCT4", [slot("payload", "payload", f"{ns}.CT4Payload framework input summation")]),
        edge("CT5.edge.comparison.ct14", compare, ct14, "handoff", "comparisonToCT14", "toCT14", "Comparison", "toCT14", [slot("payload", "payload", f"{ns}.CT14Payload framework input summation")]),
    ]
    contracts = {
        entry: ["S-Def"], scope: ["S-Dich", "A-Scope"], scope_t: ["A-Scope"],
        locality: ["S-Def", "S-Equiv"], deficit: ["S-Dich", "S-Rout"], ct11: ["S-Rout", "S-Trig"],
        summation: ["S-Comp", "S-Pers"], compare: ["S-Dich", "S-Comp", "S-Rout"],
        c4: ["S-Comp", "A-Cert"], ct4: ["S-Pers", "S-Rout", "S-Trig"], ct14: ["S-Pers", "S-Rout", "S-Trig"],
    }
    prefix = [entry, scope, locality, deficit]
    instances = [
        instance("scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff", "scopeResult", "scope_terminal", "scope_trace", [entry, scope, scope_t], ["CT5.edge.begin", "CT5.edge.scope.exit"]),
        instance("ct11", "framework", "input", "ct11Plan", "port", "handoff", "ct11Result", "ct11_terminal", "ct11_trace", prefix + [ct11], ["CT5.edge.begin", "CT5.edge.scope.ready", "CT5.edge.locality.certified", "CT5.edge.deficit.ct11"]),
        instance("c4", "framework", "input", "c4Plan", "port", "handoff", "c4Result", "c4_terminal", "c4_trace", prefix + [summation, compare, c4], ["CT5.edge.begin", "CT5.edge.scope.ready", "CT5.edge.locality.certified", "CT5.edge.deficit.ledger", "CT5.edge.summation.certified", "CT5.edge.comparison.close"]),
        instance("ct4", "framework", "input", "ct4Plan", "port", "handoff", "ct4Result", "ct4_terminal", "ct4_trace", prefix + [summation, compare, ct4], ["CT5.edge.begin", "CT5.edge.scope.ready", "CT5.edge.locality.certified", "CT5.edge.deficit.ledger", "CT5.edge.summation.certified", "CT5.edge.comparison.ct4"]),
        instance("ct14", "framework", "input", "ct14Plan", "port", "handoff", "ct14Result", "ct14_terminal", "ct14_trace", prefix + [summation, compare, ct14], ["CT5.edge.begin", "CT5.edge.scope.ready", "CT5.edge.locality.certified", "CT5.edge.deficit.ledger", "CT5.edge.summation.certified", "CT5.edge.comparison.ct14"]),
    ]
    return config("CT5", "Local-to-global bookkeeping", "CT5 — Local-to-global bookkeeping", nodes, edges, contracts, instances,
                  {"close": ["C4"], "handoff": ["P_5_to_4", "P_5_to_11", "P_5_to_14"]},
                  ["LocalityState", "LocalLedgerState", "SummationState", "C4Certificate", "CT4Payload"])


def instance(case: str, framework: str, input_name: str, plan: str, port: str,
             handoff: str, result: str, theorem: str, trace: str,
             node_path: list[str], edge_path: list[str]) -> dict:
    return {
        "case": case, "framework": framework, "input": input_name,
        "plan": plan, "port": port, "handoff": handoff, "result": result,
        "theorem": theorem, "trace": trace, "nodePath": node_path,
        "edgePath": edge_path,
    }


def config(tactic_id: str, name: str, section: str, nodes: list[dict],
           edges: list[dict], contracts: dict[str, list[str]], instances: list[dict],
           signature: dict, api_types: list[str]) -> dict:
    return {
        "id": tactic_id, "version": f"{tactic_id}-v1", "name": name,
        "section": section, "nodes": nodes, "edges": edges,
        "contracts": contracts, "instances": instances,
        "signature": signature, "apiTypes": api_types,
    }


def declaration(cfg: dict, name: str, source_leaf: str, kind: str,
                module_suffix: str = "") -> dict:
    ns = f"StructuralExhaustion.{cfg['id']}"
    module = ns + module_suffix
    return ref(f"{module}.{name}", f"StructuralExhaustion/{cfg['id']}/{source_leaf}.lean", kind, module)


def node_declaration(cfg: dict, module_name: str, name: str, kind: str) -> dict:
    ns = f"StructuralExhaustion.{cfg['id']}.Nodes.{module_name}"
    source = f"StructuralExhaustion/{cfg['id']}/Nodes/{module_name}.lean"
    return ref(f"{ns}.{name}", source, kind, ns)


def graph_declaration(cfg: dict, name: str, kind: str) -> dict:
    return declaration(cfg, name, "Graph", kind, ".Graph")


def build_transition(cfg: dict, item: dict) -> dict:
    guard = {"kind": "branch" if item["resultCtor"] else "unconditional",
             "branchTag": item["tag"], "evidenceSlots": item["evidence"]}
    if item["resultCtor"]:
        guard["resultConstructorRef"] = node_declaration(
            cfg, item["resultModule"], f"Decision.{item['resultCtor']}", "constructor")
    return {
        "transitionId": item["id"], "fromNodeId": item["source"],
        "toNodeId": item["target"], "kind": item["kind"],
        "transitionConstructorRef": graph_declaration(cfg, f"Edge.{item['ctor']}", "constructor"),
        "guard": guard,
    }


def implementation(namespace: str, source: str, declarations: list[tuple[str, str, str]]) -> dict:
    return {
        "namespace": namespace,
        "sourceFile": source,
        "requiredRoles": sorted({role for role, _, _ in declarations}),
        "declarations": [
            bind(role, name, ref(f"{namespace}.{name}", source, kind, namespace))
            for role, name, kind in declarations
        ],
    }


def build_node(cfg: dict, item: dict, transitions: list[dict]) -> dict:
    tactic_id = cfg["id"]
    ns = f"StructuralExhaustion.{tactic_id}"
    node_id = item["id"]
    common = {
        "artifactType": "formalNodeSpec", "schemaVersion": "2.0.0",
        "graphVersion": cfg["version"], "nodeId": node_id,
        "nodeKind": item["kind"], "title": item["title"],
        "human": {
            "informal": f"Execute the proof-carrying {item['title'].lower()} contract.",
            "latex": "", "whyNeeded": "The successor receives exactly the evidence produced at this boundary.",
            "failureMeaning": "The machine cannot cross this boundary without constructing the declared indexed result.",
            "proofHints": ["Implement this node using only its immediate typed predecessor state."],
        },
        "contracts": cfg["contracts"][node_id],
        "source": {"document": "branch_closure_methodology_extended.tex", "section": cfg["section"], "diagramKey": node_id.split(".")[-1]},
    }
    if item["kind"] == "terminal":
        term = item["terminal"]
        graph_ns = f"{ns}.Graph"
        graph_source = f"StructuralExhaustion/{tactic_id}/Graph.lean"
        execution_source = f"StructuralExhaustion/{tactic_id}/Execution.lean"
        terminal_ref = graph_declaration(cfg, f"Terminal.{term['case']}", "constructor")
        outcome_ref = ref(f"{ns}.Outcome.{term['case']}", execution_source, "constructor", ns)
        declarations = [
            bind("state", "Terminal", graph_declaration(cfg, "Terminal", "inductive")),
            bind("constructor", term["case"], terminal_ref),
            bind("constructor", term["nodeCtor"], graph_declaration(cfg, f"NodeId.{term['nodeCtor']}", "constructor")),
            bind("constructor", term["case"], ref(f"{ns}.RawOutcome.{term['case']}", execution_source, "constructor", ns)),
            bind("constructor", term["case"], outcome_ref),
        ]
        common["formalContract"] = {
            "contractId": f"{node_id}.contract", "executionMode": "proof_only",
            "leanContractRef": ref(f"{ns}.RawOutcome", execution_source, "inductive", ns),
            "inputs": [slot("framework", "data", f"{ns}.Framework"), slot("input", "state", f"{ns}.Input framework"), *term["evidence"]],
            "outputs": [slot("rawOutcome", "payload", f"{ns}.RawOutcome framework input .{term['case']}")],
            "dischargeCondition": "The terminal index, incoming edge, raw outcome, and certified outcome agree definitionally.",
        }
        common["leanImplementation"] = {
            "namespace": graph_ns, "sourceFile": graph_source,
            "requiredRoles": ["state", "constructor"], "declarations": declarations,
        }
        common["terminal"] = {
            "terminalCase": term["case"], "terminalConstructorRef": terminal_ref,
            "outcomeConstructorRef": outcome_ref, "claimTypeExpression": term["claim"],
            "evidenceSlots": term["evidence"],
        }
        return common

    module_name = item["module"]
    node_ns = f"{ns}.Nodes.{module_name}"
    source = f"StructuralExhaustion/{tactic_id}/Nodes/{module_name}.lean"
    contract_ref = node_declaration(cfg, module_name, "Contract", "abbrev")
    if item["kind"] == "entry":
        declarations = [("contract", "Contract", "abbrev"), ("implementation", "run", "definition")]
        outputs = [slot("entry", "state", f"{ns}.Input framework")]
        execution_mode = "declarative"
    elif item["kind"] == "certification":
        declarations = [("contract", "Contract", "abbrev"), ("plan", "Plan", "structure"), ("implementation", "run", "definition")]
        out_id, out_kind, out_type = item["output"]
        outputs = [slot(out_id, out_kind, out_type)]
        execution_mode = "external_certificate"
    else:
        declarations = [("contract", "Contract", "abbrev"), ("decision", "Decision", "inductive"), ("plan", "Plan", "structure"), ("implementation", "run", "definition")]
        outputs = [slot("decision", "data", f"{node_ns}.Contract framework input")]
        execution_mode = "computable"
    formal = {
        "contractId": f"{node_id}.contract", "executionMode": execution_mode,
        "leanContractRef": contract_ref,
        "inputs": [slot("input", "state", f"{ns}.Input framework")],
        "outputs": outputs,
        "dischargeCondition": "The node implementation constructs its indexed output contract without inspecting any later node.",
    }
    if item["kind"] == "decision":
        formal["branches"] = []
        for transition in (edge for edge in transitions if edge["fromNodeId"] == node_id):
            formal["branches"].append({
                "branchTag": transition["guard"]["branchTag"],
                "meaning": f"Return the proof-carrying {transition['guard']['branchTag']} constructor.",
                "resultConstructorRef": transition["guard"]["resultConstructorRef"],
                "evidenceSlots": transition["guard"]["evidenceSlots"],
                "transitionId": transition["transitionId"],
            })
    common["formalContract"] = formal
    common["leanImplementation"] = implementation(node_ns, source, declarations)
    return common


def api(cfg: dict) -> dict:
    tactic_id = cfg["id"]
    ns = f"StructuralExhaustion.{tactic_id}"
    types = f"StructuralExhaustion/{tactic_id}/Types.lean"
    graph = f"StructuralExhaustion/{tactic_id}/Graph.lean"
    execution = f"StructuralExhaustion/{tactic_id}/Execution.lean"
    theorems = f"StructuralExhaustion/{tactic_id}/Theorems.lean"
    result = {
        "framework": ref(f"{ns}.Framework", types, "structure", ns),
        "input": ref(f"{ns}.Input", types, "structure", ns),
        "port": ref(f"{ns}.Port", types, "structure", ns),
        "handoffPlan": ref(f"{ns}.HandoffPlan", types, "structure", ns),
        "nodeId": ref(f"{ns}.Graph.NodeId", graph, "inductive", f"{ns}.Graph"),
        "terminal": ref(f"{ns}.Graph.Terminal", graph, "inductive", f"{ns}.Graph"),
        "edge": ref(f"{ns}.Graph.Edge", graph, "inductive", f"{ns}.Graph"),
        "path": ref(f"{ns}.Graph.Path", graph, "inductive", f"{ns}.Graph"),
        "validTrace": ref(f"{ns}.Graph.ValidTrace", graph, "definition", f"{ns}.Graph"),
        "corePlan": ref(f"{ns}.CorePlan", execution, "structure", ns),
        "rawOutcome": ref(f"{ns}.RawOutcome", execution, "inductive", ns),
        "coreResult": ref(f"{ns}.CoreResult", execution, "structure", ns),
        "runCore": ref(f"{ns}.runCore", execution, "definition", ns),
        "outcome": ref(f"{ns}.Outcome", execution, "inductive", ns),
        "outcomeClaim": ref(f"{ns}.OutcomeClaim", execution, "definition", ns),
        "executionResult": ref(f"{ns}.ExecutionResult", execution, "structure", ns),
        "run": ref(f"{ns}.run", execution, "definition", ns),
        "runTraced": ref(f"{ns}.runTraced", execution, "definition", ns),
        "soundness": ref(f"{ns}.run_verified", theorems, "theorem", ns),
        "totality": ref(f"{ns}.run_total", theorems, "theorem", ns),
        "traceValidity": ref(f"{ns}.run_trace_valid", theorems, "theorem", ns),
        "exhaustiveness": ref(f"{ns}.outcome_exhaustive", theorems, "theorem", ns),
    }
    for type_name in cfg["apiTypes"]:
        result[type_name[0].lower() + type_name[1:]] = ref(f"{ns}.{type_name}", types, "structure", ns)
    if tactic_id == "CT5":
        result["ct4Adapter"] = ref(f"{ns}.CT4Payload.toInput", types, "definition", f"{ns}.CT4Payload")
        result["adapterAmbient"] = ref(f"{ns}.ct4_payload_same_ambient", theorems, "theorem", ns)
        result["adapterBranch"] = ref(f"{ns}.ct4_payload_same_branch", theorems, "theorem", ns)
    if tactic_id == "CT12":
        result["runLoop"] = ref(f"{ns}.runLoop", execution, "definition", ns)
        result["loopDecrease"] = ref(
            f"{ns}.Graph.Edge.loop_decreases", graph, "theorem", f"{ns}.Graph.Edge"
        )
    return result


def example_ref(cfg: dict, name: str, kind: str = "definition") -> dict:
    namespace = f"StructuralExhaustion.Examples.{cfg['id']}Toy"
    source = f"StructuralExhaustion/Examples/{cfg['id']}Toy.lean"
    return ref(f"{namespace}.{name}", source, kind, namespace)


def build_instance(cfg: dict, item: dict) -> dict:
    case = item.get("terminalCase", item["case"])
    instance_id = item.get("instanceId", item["case"])
    return {
        "artifactType": "tacticInstantiation", "schemaVersion": "2.0.0",
        "graphVersion": cfg["version"], "instanceId": f"toy-{instance_id}",
        "tacticId": cfg["id"],
        "bindings": [
            {"slotId": "framework", "leanRef": example_ref(cfg, item["framework"])},
            {"slotId": "input", "leanRef": example_ref(cfg, item["input"])},
            {"slotId": "corePlan", "leanRef": example_ref(cfg, item["plan"])},
            {"slotId": "port", "leanRef": example_ref(cfg, item["port"])},
            {"slotId": "handoffPlan", "leanRef": example_ref(cfg, item["handoff"])},
        ],
        "expectedTerminalCase": case,
        "expectedNodePath": item["nodePath"], "expectedEdgePath": item["edgePath"],
        "executionResultRef": example_ref(cfg, item["result"]),
        "terminalTheoremRef": example_ref(cfg, item["theorem"], "theorem"),
        "traceTheoremRef": example_ref(cfg, item["trace"], "theorem"),
    }


def build_contracts(cfg: dict, formal_api: dict) -> dict:
    membership: dict[str, list[str]] = defaultdict(list)
    for node_id, schemas in cfg["contracts"].items():
        for schema in schemas:
            membership[schema].append(node_id)
    evidence = [formal_api["edge"], formal_api["soundness"]]
    return {
        "artifactType": "tacticContractInventory", "schemaVersion": "2.0.0",
        "graphVersion": cfg["version"], "tacticId": cfg["id"],
        "contracts": [
            {
                "contractInstanceId": f"{cfg['id']}.{schema}.1",
                "contractSchema": schema,
                "statement": {"informal": f"{schema} is discharged by the indexed states and typed edges of {cfg['id']}.", "latex": ""},
                "nodeIds": node_ids, "leanEvidence": evidence,
                "dischargePolicy": "Lean checks the declaration types; repository validation checks exact node membership and edge coverage.",
            }
            for schema, node_ids in membership.items()
        ],
    }


def generate(cfg: dict) -> tuple[int, int, int]:
    transitions = [build_transition(cfg, item) for item in cfg["edges"]]
    nodes = [build_node(cfg, item, transitions) for item in cfg["nodes"]]
    formal_api = api(cfg)
    tactic = {
        "artifactType": "formalTacticSpec", "schemaVersion": "2.0.0",
        "graphVersion": cfg["version"], "tacticId": cfg["id"], "name": cfg["name"],
        "signature": {"input": "validated_typed_state", **cfg["signature"], "scope": ["typed_scope_exit"]},
        "entryNodeId": cfg["nodes"][0]["id"],
        "nodeRefs": [f"nodes/{item['id']}.json" for item in cfg["nodes"]],
        "transitions": transitions,
        "terminalCases": [item["terminal"]["case"] for item in cfg["nodes"] if item["kind"] == "terminal"],
        "terminalCoverage": [
            {"terminalCase": item.get("terminalCase", item["case"]), "mode": "executable_instance", "instanceRef": f"instances/{cfg['id'].lower()}/toy-{item.get('instanceId', item['case'])}.json"}
            for item in cfg["instances"]
        ],
        "formalApi": formal_api,
        "totalityPolicy": {
            "allNodesBound": True, "allTransitionsDeclared": True,
            "allDecisionBranchesMapped": True, "allTracesKernelCertified": True,
            "allTerminalOutcomesTyped": True, "allConsumerTriggersCarried": True,
        },
        "source": {"document": "branch_closure_methodology_extended.tex", "section": cfg["section"]},
        "contractInventoryRef": "contracts.json",
    }
    root = ROOT / f"framework/{cfg['id']}"
    write(root / "tactic.json", tactic)
    contracts = build_contracts(cfg, formal_api)
    write(root / "contracts.json", contracts)
    formalization = {
        "artifactType": "tacticFormalizationIndex", "schemaVersion": "2.0.0",
        "graphVersion": cfg["version"], "tacticId": cfg["id"],
        "toolchain": "leanprover/lean4:v4.31.0", "rootModule": "StructuralExhaustion",
        "nodeBindings": [
            {
                "nodeId": item["nodeId"], "nodeSpecRef": node_ref,
                "contractDeclaration": item["formalContract"]["leanContractRef"]["declaration"],
                "requiredDeclarations": [binding["ref"]["declaration"] for binding in item["leanImplementation"]["declarations"]],
            }
            for node_ref, item in zip(tactic["nodeRefs"], nodes)
        ],
        "aggregateDeclarations": {name: value["declaration"] for name, value in formal_api.items()},
        "generatedBindingCheck": "StructuralExhaustion/Generated/BindingCheck.lean",
    }
    write(root / "formalization.json", formalization)
    for item in nodes:
        write(root / f"nodes/{item['nodeId']}.json", item)
        write(ROOT / f"schemas/concrete/nodes/{item['nodeId']}.schema.json", {
            "$schema": "https://json-schema.org/draft/2020-12/schema",
            "$id": f"https://example.org/structural-exhaustion/{cfg['id'].lower()}/nodes/{item['nodeId']}.schema.json",
            "allOf": [
                {"$ref": "../../formalization.bundle.schema.json#/$defs/formalNodeSpec"},
                {"properties": {"nodeId": {"const": item["nodeId"]}, "nodeKind": {"const": item["nodeKind"]}}, "required": ["nodeId", "nodeKind"]},
            ],
        })
    for item in cfg["instances"]:
        write(ROOT / f"instances/{cfg['id'].lower()}/toy-{item.get('instanceId', item['case'])}.json", build_instance(cfg, item))
    return len(nodes), len(transitions), len(cfg["instances"])


def main() -> int:
    total = [0, 0, 0]
    for cfg in (ct3_config(), ct4_config(), ct5_config()):
        counts = generate(cfg)
        total = [left + right for left, right in zip(total, counts)]
        print(f"Wrote {cfg['version']}: {counts[0]} nodes, {counts[1]} edges, {counts[2]} instances")
    print(f"Total CT3-CT5: {total[0]} nodes, {total[1]} edges, {total[2]} instances")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
