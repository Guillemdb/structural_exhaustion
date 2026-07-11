#!/usr/bin/env python3
"""Generate the CT6-v1 through CT10-v1 semantic formal specifications."""
from __future__ import annotations

from generate_ct3_ct5_spec import (
    config,
    edge,
    generate,
    instance,
    node,
    slot,
    terminal,
)


def ct6_config() -> dict:
    ns = "StructuralExhaustion.CT6"
    entry, scope, scope_t = "CT6.entry", "CT6.decide.scope", "CT6.terminal.scope"
    define, activity, active = "CT6.certify.definition", "CT6.decide.activity", "CT6.certify.activeLedger"
    ct4, dormant = "CT6.terminal.ct4", "CT6.decide.dormant"
    c1, ct3, ct7, ct9, ct10 = ("CT6.terminal.c1", "CT6.terminal.ct3", "CT6.terminal.ct7", "CT6.terminal.ct9", "CT6.terminal.ct10")
    nodes = [
        node(entry, "entry", "Validated CT6 monitored-family entry", "Entry"),
        node(scope, "decision", "Bounded first-failure scope", "Scope"),
        node(scope_t, "terminal", "Missing first-failure scope terminal", terminal=terminal("scope", "scopeTerminal", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")], f"¬ {ns}.ScopeReadyAt framework input")),
        node(define, "certification", "Activity and first-failure definition certification", "Definition", ("definition", "state", f"{ns}.DefinitionState framework input")),
        node(activity, "decision", "Active/dormant dichotomy", "Activity"),
        node(active, "certification", "Active ledger construction", "ActiveLedger", ("payload", "payload", f"{ns}.CT4Payload framework input active")),
        node(ct4, "terminal", "CT4 active-ledger handoff", terminal=terminal("ct4", "ct4Terminal", [slot("payload", "payload", f"{ns}.CT4Payload framework input active")], "port.accepts (.ct4 payload)")),
        node(dormant, "decision", "Dormant first-failure routing", "Dormant"),
        node(c1, "terminal", "C1 first-failure target terminal", terminal=terminal("c1", "c1Terminal", [slot("certificate", "certificate", f"{ns}.C1Certificate framework input dormant")], "framework.entry.C1Claim input.G input.branch")),
        node(ct3, "terminal", "CT3 boundary-response handoff", terminal=terminal("ct3", "ct3Terminal", [slot("payload", "payload", f"{ns}.CT3Payload framework input dormant")], "port.accepts (.ct3 payload)")),
        node(ct7, "terminal", "CT7 exchange handoff", terminal=terminal("ct7", "ct7Terminal", [slot("payload", "payload", f"{ns}.CT7Payload framework input dormant")], "port.accepts (.ct7 payload)")),
        node(ct9, "terminal", "CT9 saturation handoff", terminal=terminal("ct9", "ct9Terminal", [slot("payload", "payload", f"{ns}.CT9Payload framework input dormant")], "port.accepts (.ct9 payload)")),
        node(ct10, "terminal", "CT10 refinement handoff", terminal=terminal("ct10", "ct10Terminal", [slot("payload", "payload", f"{ns}.CT10Payload framework input dormant")], "port.accepts (.ct10 payload)")),
    ]
    edges = [
        edge("CT6.edge.begin", entry, scope, "advance", "beginScope", "begin"),
        edge("CT6.edge.scope.exit", scope, scope_t, "scope", "scopeExit", "exit", "Scope", "exit", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")]),
        edge("CT6.edge.scope.ready", scope, define, "advance", "scopeReady", "ready", "Scope", "ready", [slot("scopeState", "state", f"{ns}.ScopedState framework input")]),
        edge("CT6.edge.definition.certified", define, activity, "advance", "definitionCertified", "certified", evidence=[slot("definition", "state", f"{ns}.DefinitionState framework input")]),
        edge("CT6.edge.activity.active", activity, active, "advance", "activityActive", "active", "Activity", "active", [slot("active", "state", f"{ns}.ActiveState framework input definition")]),
        edge("CT6.edge.activity.dormant", activity, dormant, "advance", "activityDormant", "dormant", "Activity", "dormant", [slot("dormant", "state", f"{ns}.DormantState framework input definition")]),
        edge("CT6.edge.active.ct4", active, ct4, "handoff", "activeLedgerToCT4", "toCT4", evidence=[slot("payload", "payload", f"{ns}.CT4Payload framework input active")]),
        edge("CT6.edge.dormant.c1", dormant, c1, "close", "dormantClose", "close", "Dormant", "close", [slot("certificate", "certificate", f"{ns}.C1Certificate framework input dormant")]),
        edge("CT6.edge.dormant.ct3", dormant, ct3, "handoff", "dormantToCT3", "toCT3", "Dormant", "toCT3", [slot("payload", "payload", f"{ns}.CT3Payload framework input dormant")]),
        edge("CT6.edge.dormant.ct7", dormant, ct7, "handoff", "dormantToCT7", "toCT7", "Dormant", "toCT7", [slot("payload", "payload", f"{ns}.CT7Payload framework input dormant")]),
        edge("CT6.edge.dormant.ct9", dormant, ct9, "handoff", "dormantToCT9", "toCT9", "Dormant", "toCT9", [slot("payload", "payload", f"{ns}.CT9Payload framework input dormant")]),
        edge("CT6.edge.dormant.ct10", dormant, ct10, "handoff", "dormantToCT10", "toCT10", "Dormant", "toCT10", [slot("payload", "payload", f"{ns}.CT10Payload framework input dormant")]),
    ]
    contracts = {
        entry: ["S-Def"], scope: ["S-Dich", "A-Scope"], scope_t: ["A-Scope"],
        define: ["S-Def", "S-Equiv"], activity: ["S-Dich"], active: ["S-Rout"],
        ct4: ["S-Rout", "S-Trig"], dormant: ["S-Dich", "S-Rout"],
        c1: ["S-Equiv", "A-Cert"], ct3: ["S-Rout", "S-Trig"],
        ct7: ["S-Rout", "S-Trig"], ct9: ["S-Rout", "S-Trig"], ct10: ["S-Rout", "S-Trig"],
    }
    common = [entry, scope, define, activity]
    common_edges = ["CT6.edge.begin", "CT6.edge.scope.ready", "CT6.edge.definition.certified"]
    instances = [
        instance("scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff", "scopeResult", "scope_terminal", "scope_trace", [entry, scope, scope_t], ["CT6.edge.begin", "CT6.edge.scope.exit"]),
        instance("ct4", "framework", "input", "ct4Plan", "port", "handoff", "ct4Result", "ct4_terminal", "ct4_trace", common + [active, ct4], common_edges + ["CT6.edge.activity.active", "CT6.edge.active.ct4"]),
        instance("c1", "framework", "input", "c1Plan", "port", "handoff", "c1Result", "c1_terminal", "c1_trace", common + [dormant, c1], common_edges + ["CT6.edge.activity.dormant", "CT6.edge.dormant.c1"]),
        instance("ct3", "framework", "input", "ct3Plan", "port", "handoff", "ct3Result", "ct3_terminal", "ct3_trace", common + [dormant, ct3], common_edges + ["CT6.edge.activity.dormant", "CT6.edge.dormant.ct3"]),
        instance("ct7", "framework", "input", "ct7Plan", "port", "handoff", "ct7Result", "ct7_terminal", "ct7_trace", common + [dormant, ct7], common_edges + ["CT6.edge.activity.dormant", "CT6.edge.dormant.ct7"]),
        instance("ct9", "framework", "input", "ct9Plan", "port", "handoff", "ct9Result", "ct9_terminal", "ct9_trace", common + [dormant, ct9], common_edges + ["CT6.edge.activity.dormant", "CT6.edge.dormant.ct9"]),
        instance("ct10", "framework", "input", "ct10Plan", "port", "handoff", "ct10Result", "ct10_terminal", "ct10_trace", common + [dormant, ct10], common_edges + ["CT6.edge.activity.dormant", "CT6.edge.dormant.ct10"]),
    ]
    return config("CT6", "Active/dormant dichotomy", "CT6 — Active/dormant dichotomy", nodes, edges, contracts, instances,
                  {"close": ["C1"], "handoff": ["P_6_to_4", "P_6_to_3", "P_6_to_7", "P_6_to_9", "P_6_to_10"]},
                  ["DefinitionState", "ActiveState", "DormantState", "C1Certificate"])


def ct7_config() -> dict:
    ns = "StructuralExhaustion.CT7"
    entry, scope, scope_t = "CT7.entry", "CT7.decide.scope", "CT7.terminal.scope"
    context, realize, c1 = "CT7.certify.context", "CT7.decide.realization", "CT7.terminal.c1"
    distinction, defect = "CT7.decide.distinction", "CT7.decide.defect"
    c3, ct3, ct12 = "CT7.terminal.c3", "CT7.terminal.ct3", "CT7.terminal.ct12"
    neutral, c2, ct10, ct16 = "CT7.decide.neutral", "CT7.terminal.c2", "CT7.terminal.ct10", "CT7.terminal.ct16"
    nodes = [
        node(entry, "entry", "Validated CT7 exchange entry", "Entry"),
        node(scope, "decision", "Finite context-generator scope", "Scope"),
        node(scope_t, "terminal", "Missing context-generator scope terminal", terminal=terminal("scope", "scopeTerminal", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")], f"¬ {ns}.ScopeReadyAt framework input")),
        node(context, "certification", "Context completeness certification", "Context", ("context", "state", f"{ns}.ContextState framework input")),
        node(realize, "decision", "Target realization decision", "Realization"),
        node(c1, "terminal", "C1 target realization terminal", terminal=terminal("c1", "c1Terminal", [slot("certificate", "certificate", f"{ns}.C1Certificate framework input context")], "framework.entry.C1Claim input.G input.branch")),
        node(distinction, "decision", "Distinguishing/neutral decision", "Distinction"),
        node(defect, "decision", "Distinguishing defect routing", "Defect"),
        node(c3, "terminal", "C3 routed-defect terminal", terminal=terminal("c3", "c3Terminal", [slot("certificate", "certificate", f"{ns}.C3Certificate framework input defect")], "framework.entry.C3Claim input.G input.branch")),
        node(ct3, "terminal", "CT3 external-type handoff", terminal=terminal("ct3", "ct3Terminal", [slot("payload", "payload", f"{ns}.CT3Payload framework input defect")], "port.accepts (.ct3 payload)")),
        node(ct12, "terminal", "CT12 peeling handoff", terminal=terminal("ct12", "ct12Terminal", [slot("payload", "payload", f"{ns}.CT12Payload framework input defect")], "port.accepts (.ct12 payload)")),
        node(neutral, "decision", "Neutral compression routing", "Neutral"),
        node(c2, "terminal", "C2 neutral-compression terminal", terminal=terminal("c2", "c2Terminal", [slot("certificate", "certificate", f"{ns}.C2Certificate framework input neutral")], "framework.entry.C2Claim input.G input.branch")),
        node(ct10, "terminal", "CT10 neutral-label handoff", terminal=terminal("ct10", "ct10Terminal", [slot("payload", "payload", f"{ns}.CT10Payload framework input neutral")], "port.accepts (.ct10 payload)")),
        node(ct16, "terminal", "CT16 whole-object handoff", terminal=terminal("ct16", "ct16Terminal", [slot("payload", "payload", f"{ns}.CT16Payload framework input neutral")], "port.accepts (.ct16 payload)")),
    ]
    edges = [
        edge("CT7.edge.begin", entry, scope, "advance", "beginScope", "begin"),
        edge("CT7.edge.scope.exit", scope, scope_t, "scope", "scopeExit", "exit", "Scope", "exit", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")]),
        edge("CT7.edge.scope.ready", scope, context, "advance", "scopeReady", "ready", "Scope", "ready", [slot("scopeState", "state", f"{ns}.ScopedState framework input")]),
        edge("CT7.edge.context.certified", context, realize, "advance", "contextCertified", "certified", evidence=[slot("context", "state", f"{ns}.ContextState framework input")]),
        edge("CT7.edge.realization.close", realize, c1, "close", "realizationClose", "close", "Realization", "close", [slot("certificate", "certificate", f"{ns}.C1Certificate framework input context")]),
        edge("CT7.edge.realization.none", realize, distinction, "advance", "realizationUnrealized", "unrealized", "Realization", "unrealized", [slot("unrealized", "state", f"{ns}.UnrealizedState framework input context")]),
        edge("CT7.edge.distinction.defect", distinction, defect, "advance", "distinctionDefect", "defect", "Distinction", "defect", [slot("defect", "state", f"{ns}.DefectState framework input unrealized")]),
        edge("CT7.edge.distinction.neutral", distinction, neutral, "advance", "distinctionNeutral", "neutral", "Distinction", "neutral", [slot("neutral", "state", f"{ns}.NeutralState framework input unrealized")]),
        edge("CT7.edge.defect.c3", defect, c3, "close", "defectClose", "close", "Defect", "close", [slot("certificate", "certificate", f"{ns}.C3Certificate framework input defect")]),
        edge("CT7.edge.defect.ct3", defect, ct3, "handoff", "defectToCT3", "toCT3", "Defect", "toCT3", [slot("payload", "payload", f"{ns}.CT3Payload framework input defect")]),
        edge("CT7.edge.defect.ct12", defect, ct12, "handoff", "defectToCT12", "toCT12", "Defect", "toCT12", [slot("payload", "payload", f"{ns}.CT12Payload framework input defect")]),
        edge("CT7.edge.neutral.c2", neutral, c2, "close", "neutralClose", "close", "Neutral", "close", [slot("certificate", "certificate", f"{ns}.C2Certificate framework input neutral")]),
        edge("CT7.edge.neutral.ct10", neutral, ct10, "handoff", "neutralToCT10", "toCT10", "Neutral", "toCT10", [slot("payload", "payload", f"{ns}.CT10Payload framework input neutral")]),
        edge("CT7.edge.neutral.ct16", neutral, ct16, "handoff", "neutralToCT16", "toCT16", "Neutral", "toCT16", [slot("payload", "payload", f"{ns}.CT16Payload framework input neutral")]),
    ]
    contracts = {entry: ["S-Def"], scope: ["S-Dich", "A-Scope"], scope_t: ["A-Scope"], context: ["S-Equiv"], realize: ["S-Dich"], c1: ["A-Cert"], distinction: ["S-Dich", "S-Equiv"], defect: ["S-Rout"], c3: ["S-Rout", "A-Cert"], ct3: ["S-Rout", "S-Trig"], ct12: ["S-Rout", "S-Trig"], neutral: ["S-Comp", "S-Rout"], c2: ["S-Comp", "A-Cert"], ct10: ["S-Rout", "S-Trig"], ct16: ["S-Rout", "S-Trig"]}
    prefix = [entry, scope, context, realize]
    ep = ["CT7.edge.begin", "CT7.edge.scope.ready", "CT7.edge.context.certified"]
    instances = [
        instance("scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff", "scopeResult", "scope_terminal", "scope_trace", [entry, scope, scope_t], ["CT7.edge.begin", "CT7.edge.scope.exit"]),
        instance("c1", "framework", "input", "c1Plan", "port", "handoff", "c1Result", "c1_terminal", "c1_trace", prefix + [c1], ep + ["CT7.edge.realization.close"]),
        instance("c3", "framework", "input", "c3Plan", "port", "handoff", "c3Result", "c3_terminal", "c3_trace", prefix + [distinction, defect, c3], ep + ["CT7.edge.realization.none", "CT7.edge.distinction.defect", "CT7.edge.defect.c3"]),
        instance("ct3", "framework", "input", "ct3Plan", "port", "handoff", "ct3Result", "ct3_terminal", "ct3_trace", prefix + [distinction, defect, ct3], ep + ["CT7.edge.realization.none", "CT7.edge.distinction.defect", "CT7.edge.defect.ct3"]),
        instance("ct12", "framework", "input", "ct12Plan", "port", "handoff", "ct12Result", "ct12_terminal", "ct12_trace", prefix + [distinction, defect, ct12], ep + ["CT7.edge.realization.none", "CT7.edge.distinction.defect", "CT7.edge.defect.ct12"]),
        instance("c2", "framework", "input", "c2Plan", "port", "handoff", "c2Result", "c2_terminal", "c2_trace", prefix + [distinction, neutral, c2], ep + ["CT7.edge.realization.none", "CT7.edge.distinction.neutral", "CT7.edge.neutral.c2"]),
        instance("ct10", "framework", "input", "ct10Plan", "port", "handoff", "ct10Result", "ct10_terminal", "ct10_trace", prefix + [distinction, neutral, ct10], ep + ["CT7.edge.realization.none", "CT7.edge.distinction.neutral", "CT7.edge.neutral.ct10"]),
        instance("ct16", "framework", "input", "ct16Plan", "port", "handoff", "ct16Result", "ct16_terminal", "ct16_trace", prefix + [distinction, neutral, ct16], ep + ["CT7.edge.realization.none", "CT7.edge.distinction.neutral", "CT7.edge.neutral.ct16"]),
    ]
    return config("CT7", "Exchange trichotomy", "CT7 — Exchange trichotomy", nodes, edges, contracts, instances,
                  {"close": ["C1", "C2", "C3"], "handoff": ["P_7_to_3", "P_7_to_12", "P_7_to_10", "P_7_to_16"]},
                  ["ContextState", "UnrealizedState", "DefectState", "NeutralState", "C1Certificate", "C2Certificate", "C3Certificate"])


def ct8_config() -> dict:
    ns = "StructuralExhaustion.CT8"
    entry, scope, scope_t, ct10 = "CT8.entry", "CT8.decide.scope", "CT8.terminal.scope", "CT8.terminal.ct10"
    equiv, repetition, c5 = "CT8.certify.equivalence", "CT8.decide.repetition", "CT8.terminal.c5"
    response, c2, routing, ct3, ct7 = "CT8.decide.response", "CT8.terminal.c2", "CT8.decide.routing", "CT8.terminal.ct3", "CT8.terminal.ct7"
    nodes = [
        node(entry, "entry", "Validated CT8 sequence entry", "Entry"), node(scope, "decision", "Finite exact-type scope", "Scope"),
        node(scope_t, "terminal", "Missing finite-type scope terminal", terminal=terminal("scope", "scopeTerminal", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")], f"¬ {ns}.ScopeReadyAt framework input")),
        node(ct10, "terminal", "CT10 coarse-label handoff", terminal=terminal("ct10", "ct10Terminal", [slot("payload", "payload", f"{ns}.CT10Payload framework input")], "port.accepts (.ct10 payload)")),
        node(equiv, "certification", "Exact-type equivalence certification", "Equivalence", ("equality", "state", f"{ns}.EqualityState framework input")),
        node(repetition, "decision", "Short/repeated-type decision", "Repetition"),
        node(c5, "terminal", "C5 finite-enumeration terminal", terminal=terminal("c5", "c5Terminal", [slot("certificate", "certificate", f"{ns}.C5Certificate framework input equality")], "framework.entry.C5Claim input.G input.branch")),
        node(response, "decision", "Repeated-type response decision", "Response"),
        node(c2, "terminal", "C2 repeated-type compression terminal", terminal=terminal("c2", "c2Terminal", [slot("certificate", "certificate", f"{ns}.C2Certificate framework input repeated")], "framework.entry.C2Claim input.G input.branch")),
        node(routing, "decision", "Separating-witness routing", "Routing"),
        node(ct3, "terminal", "CT3 separating-type handoff", terminal=terminal("ct3", "ct3Terminal", [slot("payload", "payload", f"{ns}.CT3Payload framework input separating")], "port.accepts (.ct3 payload)")),
        node(ct7, "terminal", "CT7 chain-exchange handoff", terminal=terminal("ct7", "ct7Terminal", [slot("payload", "payload", f"{ns}.CT7Payload framework input separating")], "port.accepts (.ct7 payload)")),
    ]
    edges = [
        edge("CT8.edge.begin", entry, scope, "advance", "beginScope", "begin"),
        edge("CT8.edge.scope.exit", scope, scope_t, "scope", "scopeExit", "exit", "Scope", "exit", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")]),
        edge("CT8.edge.scope.refine", scope, ct10, "handoff", "scopeRefine", "refine", "Scope", "refine", [slot("payload", "payload", f"{ns}.CT10Payload framework input")]),
        edge("CT8.edge.scope.ready", scope, equiv, "advance", "scopeReady", "ready", "Scope", "ready", [slot("scopeState", "state", f"{ns}.ScopedState framework input")]),
        edge("CT8.edge.equivalence.certified", equiv, repetition, "advance", "equivalenceCertified", "certified", evidence=[slot("equality", "state", f"{ns}.EqualityState framework input")]),
        edge("CT8.edge.repetition.short", repetition, c5, "close", "repetitionShort", "short", "Repetition", "short", [slot("certificate", "certificate", f"{ns}.C5Certificate framework input equality")]),
        edge("CT8.edge.repetition.repeated", repetition, response, "advance", "repetitionRepeated", "repeated", "Repetition", "repeated", [slot("repeated", "state", f"{ns}.RepeatedState framework input equality")]),
        edge("CT8.edge.response.close", response, c2, "close", "responseClose", "close", "Response", "close", [slot("certificate", "certificate", f"{ns}.C2Certificate framework input repeated")]),
        edge("CT8.edge.response.separating", response, routing, "advance", "responseSeparating", "separating", "Response", "separating", [slot("separating", "state", f"{ns}.SeparatingState framework input repeated")]),
        edge("CT8.edge.routing.ct3", routing, ct3, "handoff", "routingToCT3", "toCT3", "Routing", "toCT3", [slot("payload", "payload", f"{ns}.CT3Payload framework input separating")]),
        edge("CT8.edge.routing.ct7", routing, ct7, "handoff", "routingToCT7", "toCT7", "Routing", "toCT7", [slot("payload", "payload", f"{ns}.CT7Payload framework input separating")]),
    ]
    contracts = {entry: ["S-Def"], scope: ["S-Dich", "A-Scope", "S-Rout"], scope_t: ["A-Scope"], ct10: ["S-Rout", "S-Trig"], equiv: ["S-Equiv"], repetition: ["S-Dich", "S-Comp"], c5: ["S-Comp", "A-Cert"], response: ["S-Dich", "S-Equiv", "S-Comp"], c2: ["S-Equiv", "S-Comp", "A-Cert"], routing: ["S-Rout"], ct3: ["S-Rout", "S-Trig"], ct7: ["S-Rout", "S-Trig"]}
    base = [entry, scope, equiv, repetition]
    eb = ["CT8.edge.begin", "CT8.edge.scope.ready", "CT8.edge.equivalence.certified"]
    instances = [
        instance("scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff", "scopeResult", "scope_terminal", "scope_trace", [entry, scope, scope_t], ["CT8.edge.begin", "CT8.edge.scope.exit"]),
        instance("ct10", "framework", "input", "ct10Plan", "port", "handoff", "ct10Result", "ct10_terminal", "ct10_trace", [entry, scope, ct10], ["CT8.edge.begin", "CT8.edge.scope.refine"]),
        instance("c5", "framework", "input", "c5Plan", "port", "handoff", "c5Result", "c5_terminal", "c5_trace", base + [c5], eb + ["CT8.edge.repetition.short"]),
        instance("c2", "framework", "input", "c2Plan", "port", "handoff", "c2Result", "c2_terminal", "c2_trace", base + [response, c2], eb + ["CT8.edge.repetition.repeated", "CT8.edge.response.close"]),
        instance("ct3", "framework", "input", "ct3Plan", "port", "handoff", "ct3Result", "ct3_terminal", "ct3_trace", base + [response, routing, ct3], eb + ["CT8.edge.repetition.repeated", "CT8.edge.response.separating", "CT8.edge.routing.ct3"]),
        instance("ct7", "framework", "input", "ct7Plan", "port", "handoff", "ct7Result", "ct7_terminal", "ct7_trace", base + [response, routing, ct7], eb + ["CT8.edge.repetition.repeated", "CT8.edge.response.separating", "CT8.edge.routing.ct7"]),
    ]
    return config("CT8", "Finite-state pumping", "CT8 — Finite-state pumping", nodes, edges, contracts, instances,
                  {"close": ["C2", "C5"], "handoff": ["P_8_to_3", "P_8_to_7", "P_8_to_10"]},
                  ["EqualityState", "RepeatedState", "SeparatingState", "C2Certificate", "C5Certificate"])


def ct9_config() -> dict:
    ns = "StructuralExhaustion.CT9"
    entry, scope, scope_t, ct10 = "CT9.entry", "CT9.decide.scope", "CT9.terminal.scope", "CT9.terminal.ct10"
    fibre, overload, ct4 = "CT9.certify.fibre", "CT9.decide.overload", "CT9.terminal.ct4"
    extraction, routing, c1, ct7, ct8 = "CT9.certify.extraction", "CT9.decide.routing", "CT9.terminal.c1", "CT9.terminal.ct7", "CT9.terminal.ct8"
    nodes = [
        node(entry, "entry", "Validated CT9 payer-fibre entry", "Entry"), node(scope, "decision", "Finite fibre-labelling scope", "Scope"),
        node(scope_t, "terminal", "Missing finite-labelling scope terminal", terminal=terminal("scope", "scopeTerminal", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")], f"¬ {ns}.ScopeReadyAt framework input")),
        node(ct10, "terminal", "CT10 label-refinement handoff", terminal=terminal("ct10", "ct10Terminal", [slot("payload", "payload", f"{ns}.CT10Payload framework input")], "port.accepts (.ct10 payload)")),
        node(fibre, "certification", "Payer-fibre certification", "Fibre", ("fibre", "state", f"{ns}.FibreState framework input")),
        node(overload, "decision", "Bounded/overloaded fibre decision", "Overload"),
        node(ct4, "terminal", "CT4 bounded-multiplicity handoff", terminal=terminal("ct4", "ct4Terminal", [slot("payload", "payload", f"{ns}.CT4Payload framework input fibre")], "port.accepts (.ct4 payload)")),
        node(extraction, "certification", "Homogeneous extraction certification", "Extraction", ("extraction", "state", f"{ns}.ExtractionState framework input overloaded")),
        node(routing, "decision", "Extracted-object routing", "Routing"),
        node(c1, "terminal", "C1 overload target terminal", terminal=terminal("c1", "c1Terminal", [slot("certificate", "certificate", f"{ns}.C1Certificate framework input extraction")], "framework.entry.C1Claim input.G input.branch")),
        node(ct7, "terminal", "CT7 homogeneous-exchange handoff", terminal=terminal("ct7", "ct7Terminal", [slot("payload", "payload", f"{ns}.CT7Payload framework input extraction")], "port.accepts (.ct7 payload)")),
        node(ct8, "terminal", "CT8 long-chain handoff", terminal=terminal("ct8", "ct8Terminal", [slot("payload", "payload", f"{ns}.CT8Payload framework input extraction")], "port.accepts (.ct8 payload)")),
    ]
    edges = [
        edge("CT9.edge.begin", entry, scope, "advance", "beginScope", "begin"),
        edge("CT9.edge.scope.exit", scope, scope_t, "scope", "scopeExit", "exit", "Scope", "exit", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")]),
        edge("CT9.edge.scope.refine", scope, ct10, "handoff", "scopeRefine", "refine", "Scope", "refine", [slot("payload", "payload", f"{ns}.CT10Payload framework input")]),
        edge("CT9.edge.scope.ready", scope, fibre, "advance", "scopeReady", "ready", "Scope", "ready", [slot("scopeState", "state", f"{ns}.ScopedState framework input")]),
        edge("CT9.edge.fibre.certified", fibre, overload, "advance", "fibreCertified", "certified", evidence=[slot("fibre", "state", f"{ns}.FibreState framework input")]),
        edge("CT9.edge.overload.bounded", overload, ct4, "handoff", "overloadBounded", "bounded", "Overload", "bounded", [slot("payload", "payload", f"{ns}.CT4Payload framework input fibre")]),
        edge("CT9.edge.overload.present", overload, extraction, "advance", "overloadPresent", "overloaded", "Overload", "overloaded", [slot("overloaded", "state", f"{ns}.OverloadedState framework input fibre")]),
        edge("CT9.edge.extraction.certified", extraction, routing, "advance", "extractionCertified", "certified", evidence=[slot("extraction", "state", f"{ns}.ExtractionState framework input overloaded")]),
        edge("CT9.edge.routing.c1", routing, c1, "close", "routingClose", "close", "Routing", "close", [slot("certificate", "certificate", f"{ns}.C1Certificate framework input extraction")]),
        edge("CT9.edge.routing.ct7", routing, ct7, "handoff", "routingToCT7", "toCT7", "Routing", "toCT7", [slot("payload", "payload", f"{ns}.CT7Payload framework input extraction")]),
        edge("CT9.edge.routing.ct8", routing, ct8, "handoff", "routingToCT8", "toCT8", "Routing", "toCT8", [slot("payload", "payload", f"{ns}.CT8Payload framework input extraction")]),
    ]
    contracts = {entry: ["S-Def"], scope: ["S-Dich", "A-Scope", "S-Rout"], scope_t: ["A-Scope"], ct10: ["S-Rout", "S-Trig"], fibre: ["S-Def"], overload: ["S-Dich", "S-Comp", "S-Rout"], ct4: ["S-Rout", "S-Trig"], extraction: ["S-Comp"], routing: ["S-Dich", "S-Rout"], c1: ["A-Cert"], ct7: ["S-Rout", "S-Trig"], ct8: ["S-Rout", "S-Trig"]}
    base = [entry, scope, fibre, overload]
    eb = ["CT9.edge.begin", "CT9.edge.scope.ready", "CT9.edge.fibre.certified"]
    instances = [
        instance("scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff", "scopeResult", "scope_terminal", "scope_trace", [entry, scope, scope_t], ["CT9.edge.begin", "CT9.edge.scope.exit"]),
        instance("ct10", "framework", "input", "ct10Plan", "port", "handoff", "ct10Result", "ct10_terminal", "ct10_trace", [entry, scope, ct10], ["CT9.edge.begin", "CT9.edge.scope.refine"]),
        instance("ct4", "framework", "input", "ct4Plan", "port", "handoff", "ct4Result", "ct4_terminal", "ct4_trace", base + [ct4], eb + ["CT9.edge.overload.bounded"]),
        instance("c1", "framework", "input", "c1Plan", "port", "handoff", "c1Result", "c1_terminal", "c1_trace", base + [extraction, routing, c1], eb + ["CT9.edge.overload.present", "CT9.edge.extraction.certified", "CT9.edge.routing.c1"]),
        instance("ct7", "framework", "input", "ct7Plan", "port", "handoff", "ct7Result", "ct7_terminal", "ct7_trace", base + [extraction, routing, ct7], eb + ["CT9.edge.overload.present", "CT9.edge.extraction.certified", "CT9.edge.routing.ct7"]),
        instance("ct8", "framework", "input", "ct8Plan", "port", "handoff", "ct8Result", "ct8_terminal", "ct8_trace", base + [extraction, routing, ct8], eb + ["CT9.edge.overload.present", "CT9.edge.extraction.certified", "CT9.edge.routing.ct8"]),
    ]
    return config("CT9", "Overload exhaustion", "CT9 — Overload exhaustion", nodes, edges, contracts, instances,
                  {"close": ["C1"], "handoff": ["P_9_to_4", "P_9_to_7", "P_9_to_8", "P_9_to_10"]},
                  ["FibreState", "OverloadedState", "ExtractionState", "C1Certificate"])


def ct10_config() -> dict:
    ns = "StructuralExhaustion.CT10"
    entry, scope, scope_t = "CT10.entry", "CT10.decide.scope", "CT10.terminal.scope"
    labels, classify, c5 = "CT10.certify.labels", "CT10.decide.classification", "CT10.terminal.c5"
    direct, ct3, ct7 = "CT10.decide.direct", "CT10.terminal.ct3", "CT10.terminal.ct7"
    promote, promoted, ct15 = "CT10.certify.promotion", "CT10.decide.promotedRouting", "CT10.terminal.ct15"
    nodes = [
        node(entry, "entry", "Validated CT10 residual-class entry", "Entry"), node(scope, "decision", "Finite refinement-alphabet scope", "Scope"),
        node(scope_t, "terminal", "Infinite-alphabet scope terminal", terminal=terminal("scope", "scopeTerminal", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")], f"¬ {ns}.ScopeReadyAt framework input")),
        node(labels, "certification", "Label-class exhaustion certification", "Labels", ("labels", "state", f"{ns}.LabelState framework input")),
        node(classify, "decision", "Refined-class classification", "Classification"),
        node(c5, "terminal", "C5 finite-class exhaustion terminal", terminal=terminal("c5", "c5Terminal", [slot("certificate", "certificate", f"{ns}.C5Certificate framework input labels")], "framework.entry.C5Claim input.G input.branch")),
        node(direct, "decision", "Direct class-result routing", "Direct"),
        node(ct3, "terminal", "CT3 promoted-response handoff", terminal=terminal("ct3", "ct3Terminal", [slot("payload", "payload", f"{ns}.CT3Payload framework input")], "port.accepts (.ct3 payload)")),
        node(ct7, "terminal", "CT7 class-exchange handoff", terminal=terminal("ct7", "ct7Terminal", [slot("payload", "payload", f"{ns}.CT7Payload framework input direct")], "port.accepts (.ct7 payload)")),
        node(promote, "certification", "Missing-datum promotion certification", "Promotion", ("promoted", "state", f"{ns}.PromotedState framework input missing")),
        node(promoted, "decision", "Promoted-invariant routing", "PromotedRouting"),
        node(ct15, "terminal", "CT15 rank-datum handoff", terminal=terminal("ct15", "ct15Terminal", [slot("payload", "payload", f"{ns}.CT15Payload framework input promoted")], "port.accepts (.ct15 payload)")),
    ]
    edges = [
        edge("CT10.edge.begin", entry, scope, "advance", "beginScope", "begin"),
        edge("CT10.edge.scope.exit", scope, scope_t, "scope", "scopeExit", "exit", "Scope", "exit", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")]),
        edge("CT10.edge.scope.ready", scope, labels, "advance", "scopeReady", "ready", "Scope", "ready", [slot("scopeState", "state", f"{ns}.ScopedState framework input")]),
        edge("CT10.edge.labels.certified", labels, classify, "advance", "labelsCertified", "certified", evidence=[slot("labels", "state", f"{ns}.LabelState framework input")]),
        edge("CT10.edge.classification.close", classify, c5, "close", "classificationClose", "close", "Classification", "close", [slot("certificate", "certificate", f"{ns}.C5Certificate framework input labels")]),
        edge("CT10.edge.classification.direct", classify, direct, "advance", "classificationDirect", "direct", "Classification", "direct", [slot("direct", "state", f"{ns}.DirectState framework input labels")]),
        edge("CT10.edge.classification.missing", classify, promote, "advance", "classificationMissing", "missing", "Classification", "missing", [slot("missing", "state", f"{ns}.MissingState framework input labels")]),
        edge("CT10.edge.direct.ct3", direct, ct3, "handoff", "directToCT3", "toCT3", "Direct", "toCT3", [slot("payload", "payload", f"{ns}.DirectCT3Payload framework input direct")]),
        edge("CT10.edge.direct.ct7", direct, ct7, "handoff", "directToCT7", "toCT7", "Direct", "toCT7", [slot("payload", "payload", f"{ns}.CT7Payload framework input direct")]),
        edge("CT10.edge.promotion.certified", promote, promoted, "advance", "promotionCertified", "certified", evidence=[slot("promoted", "state", f"{ns}.PromotedState framework input missing")]),
        edge("CT10.edge.promoted.ct3", promoted, ct3, "handoff", "promotedToCT3", "toCT3", "PromotedRouting", "toCT3", [slot("payload", "payload", f"{ns}.PromotedCT3Payload framework input promoted")]),
        edge("CT10.edge.promoted.ct15", promoted, ct15, "handoff", "promotedToCT15", "toCT15", "PromotedRouting", "toCT15", [slot("payload", "payload", f"{ns}.CT15Payload framework input promoted")]),
    ]
    contracts = {entry: ["S-Def"], scope: ["S-Dich", "A-Scope"], scope_t: ["A-Scope"], labels: ["S-Def", "S-Comp"], classify: ["S-Dich", "S-Comp", "S-Rout"], c5: ["S-Comp", "A-Cert"], direct: ["S-Rout"], ct3: ["S-Rout", "S-Trig"], ct7: ["S-Rout", "S-Trig"], promote: ["S-Def"], promoted: ["S-Rout"], ct15: ["S-Rout", "S-Trig"]}
    base = [entry, scope, labels, classify]
    eb = ["CT10.edge.begin", "CT10.edge.scope.ready", "CT10.edge.labels.certified"]
    instances = [
        instance("scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff", "scopeResult", "scope_terminal", "scope_trace", [entry, scope, scope_t], ["CT10.edge.begin", "CT10.edge.scope.exit"]),
        instance("c5", "framework", "input", "c5Plan", "port", "handoff", "c5Result", "c5_terminal", "c5_trace", base + [c5], eb + ["CT10.edge.classification.close"]),
        instance("ct3", "framework", "input", "ct3DirectPlan", "port", "handoff", "ct3DirectResult", "ct3_direct_terminal", "ct3_direct_trace", base + [direct, ct3], eb + ["CT10.edge.classification.direct", "CT10.edge.direct.ct3"]),
        instance("ct7", "framework", "input", "ct7Plan", "port", "handoff", "ct7Result", "ct7_terminal", "ct7_trace", base + [direct, ct7], eb + ["CT10.edge.classification.direct", "CT10.edge.direct.ct7"]),
        instance("ct15", "framework", "input", "ct15Plan", "port", "handoff", "ct15Result", "ct15_terminal", "ct15_trace", base + [promote, promoted, ct15], eb + ["CT10.edge.classification.missing", "CT10.edge.promotion.certified", "CT10.edge.promoted.ct15"]),
    ]
    return config("CT10", "Default refinement", "CT10 — Default refinement", nodes, edges, contracts, instances,
                  {"close": ["C5"], "handoff": ["P_10_to_3", "P_10_to_7", "P_10_to_15"]},
                  ["LabelState", "DirectState", "MissingState", "PromotedState", "C5Certificate", "CT3Payload"])


def main() -> int:
    total = [0, 0, 0]
    for cfg in (ct6_config(), ct7_config(), ct8_config(), ct9_config(), ct10_config()):
        counts = generate(cfg)
        total = [left + right for left, right in zip(total, counts)]
        print(f"Wrote {cfg['version']}: {counts[0]} nodes, {counts[1]} edges, {counts[2]} instances")
    print(f"Total CT6-CT10: {total[0]} nodes, {total[1]} edges, {total[2]} instances")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
