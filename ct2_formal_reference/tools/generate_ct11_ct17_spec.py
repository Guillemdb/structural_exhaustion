#!/usr/bin/env python3
"""Generate the CT11-v1 through CT17-v1 semantic formal specifications."""
from __future__ import annotations

from generate_ct3_ct5_spec import config, edge, generate, instance, node, slot, terminal


def ct11_config() -> dict:
    ns = "StructuralExhaustion.CT11"
    entry, scope, scope_t = "CT11.entry", "CT11.decide.scope", "CT11.terminal.scope"
    decomp, admission, ct10 = "CT11.certify.decomposition", "CT11.decide.admissibility", "CT11.terminal.ct10"
    localization, routing = "CT11.certify.localization", "CT11.decide.routing"
    ct1, ct7, ct14 = "CT11.terminal.ct1", "CT11.terminal.ct7", "CT11.terminal.ct14"
    nodes = [
        node(entry, "entry", "Validated CT11 additive-deficit entry", "Entry"),
        node(scope, "decision", "Finite local-type scope", "Scope"),
        node(scope_t, "terminal", "Missing local-type scope terminal", terminal=terminal("scope", "scopeTerminal", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")], f"¬ {ns}.ScopeReadyAt framework input")),
        node(decomp, "certification", "Admissible decomposition certification", "Decomposition", ("decomposition", "state", f"{ns}.DecompositionState framework input")),
        node(admission, "decision", "Admissibility-closure decision", "Admissibility"),
        node(ct10, "terminal", "CT10 admissibility-gap handoff", terminal=terminal("ct10", "ct10Terminal", [slot("payload", "payload", f"{ns}.CT10Payload framework input decomposition")], "port.accepts (.ct10 payload)")),
        node(localization, "certification", "Summation and localization certification", "Localization", ("localized", "state", f"{ns}.LocalizationState framework input admissible")),
        node(routing, "decision", "Localized-object routing", "Routing"),
        node(ct1, "terminal", "CT1 target-test handoff", terminal=terminal("ct1", "ct1Terminal", [slot("payload", "payload", f"{ns}.CT1Payload framework input localized")], "port.accepts (.ct1 payload)")),
        node(ct7, "terminal", "CT7 localized-exchange handoff", terminal=terminal("ct7", "ct7Terminal", [slot("payload", "payload", f"{ns}.CT7Payload framework input localized")], "port.accepts (.ct7 payload)")),
        node(ct14, "terminal", "CT14 carried-mass handoff", terminal=terminal("ct14", "ct14Terminal", [slot("payload", "payload", f"{ns}.CT14Payload framework input localized")], "port.accepts (.ct14 payload)")),
    ]
    edges = [
        edge("CT11.edge.begin", entry, scope, "advance", "beginScope", "begin"),
        edge("CT11.edge.scope.exit", scope, scope_t, "scope", "scopeExit", "exit", "Scope", "exit", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")]),
        edge("CT11.edge.scope.ready", scope, decomp, "advance", "scopeReady", "ready", "Scope", "ready", [slot("scope", "state", f"{ns}.ScopedState framework input")]),
        edge("CT11.edge.decomposition.certified", decomp, admission, "advance", "decompositionCertified", "certified", evidence=[slot("decomposition", "state", f"{ns}.DecompositionState framework input")]),
        edge("CT11.edge.admissibility.refine", admission, ct10, "handoff", "admissibilityRefine", "refine", "Admissibility", "refine", [slot("payload", "payload", f"{ns}.CT10Payload framework input decomposition")]),
        edge("CT11.edge.admissibility.closed", admission, localization, "advance", "admissibilityClosed", "closed", "Admissibility", "closed", [slot("admissible", "state", f"{ns}.AdmissibleState framework input decomposition")]),
        edge("CT11.edge.localization.certified", localization, routing, "advance", "localizationCertified", "certified", evidence=[slot("localized", "state", f"{ns}.LocalizationState framework input admissible")]),
        edge("CT11.edge.routing.ct1", routing, ct1, "handoff", "routingToCT1", "toCT1", "Routing", "toCT1", [slot("payload", "payload", f"{ns}.CT1Payload framework input localized")]),
        edge("CT11.edge.routing.ct7", routing, ct7, "handoff", "routingToCT7", "toCT7", "Routing", "toCT7", [slot("payload", "payload", f"{ns}.CT7Payload framework input localized")]),
        edge("CT11.edge.routing.ct14", routing, ct14, "handoff", "routingToCT14", "toCT14", "Routing", "toCT14", [slot("payload", "payload", f"{ns}.CT14Payload framework input localized")]),
    ]
    contracts = {entry: ["S-Def"], scope: ["A-Scope"], scope_t: ["A-Scope"], decomp: ["S-Def"], admission: ["S-Dich", "S-Rout"], ct10: ["S-Rout", "S-Trig"], localization: ["S-Comp"], routing: ["S-Rout"], ct1: ["S-Rout", "S-Trig"], ct7: ["S-Rout", "S-Trig"], ct14: ["S-Rout", "S-Trig"]}
    prefix = [entry, scope, decomp, admission]
    ep = ["CT11.edge.begin", "CT11.edge.scope.ready", "CT11.edge.decomposition.certified"]
    instances = [
        instance("scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff", "scopeResult", "scope_terminal", "scope_trace", [entry, scope, scope_t], ["CT11.edge.begin", "CT11.edge.scope.exit"]),
        instance("ct10", "framework", "input", "ct10Plan", "port", "handoff", "ct10Result", "ct10_terminal", "ct10_trace", prefix + [ct10], ep + ["CT11.edge.admissibility.refine"]),
        instance("ct1", "framework", "input", "ct1Plan", "port", "handoff", "ct1Result", "ct1_terminal", "ct1_trace", prefix + [localization, routing, ct1], ep + ["CT11.edge.admissibility.closed", "CT11.edge.localization.certified", "CT11.edge.routing.ct1"]),
        instance("ct7", "framework", "input", "ct7Plan", "port", "handoff", "ct7Result", "ct7_terminal", "ct7_trace", prefix + [localization, routing, ct7], ep + ["CT11.edge.admissibility.closed", "CT11.edge.localization.certified", "CT11.edge.routing.ct7"]),
        instance("ct14", "framework", "input", "ct14Plan", "port", "handoff", "ct14Result", "ct14_terminal", "ct14_trace", prefix + [localization, routing, ct14], ep + ["CT11.edge.admissibility.closed", "CT11.edge.localization.certified", "CT11.edge.routing.ct14"]),
    ]
    return config("CT11", "Localization", "CT11 — Localization", nodes, edges, contracts, instances,
                  {"close": [], "handoff": ["P_11_to_1", "P_11_to_7", "P_11_to_10", "P_11_to_14"]},
                  ["DecompositionState", "AdmissibleState", "LocalizationState"])


def ct12_config() -> dict:
    ns = "StructuralExhaustion.CT12"
    entry, scope, scope_t = "CT12.entry", "CT12.decide.scope", "CT12.terminal.scope"
    measure, saturation, c4 = "CT12.certify.measure", "CT12.decide.saturation", "CT12.terminal.c4"
    peel, restoration = "CT12.certify.peel", "CT12.decide.restoration"
    ct4, ct13, decrease = "CT12.terminal.ct4", "CT12.terminal.ct13", "CT12.certify.decrease"
    nodes = [
        node(entry, "entry", "Validated CT12 routed-load entry", "Entry"),
        node(scope, "decision", "Recorded natural-valued load scope", "Scope"),
        node(scope_t, "terminal", "Unmeasurable-load scope terminal", terminal=terminal("scope", "scopeTerminal", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")], f"¬ {ns}.ScopeReadyAt framework input")),
        node(measure, "certification", "Initial loop-measure certification", "Measure", ("state", "state", f"{ns}.LoopState framework input input.load")),
        node(saturation, "decision", "Unsaturated/peelable decision", "Saturation"),
        node(c4, "terminal", "C4 unsaturated discharge terminal", terminal=terminal("c4", "c4Terminal", [slot("certificate", "certificate", f"{ns}.C4Certificate framework input state")], "framework.entry.C4Claim input.G input.branch")),
        node(peel, "certification", "Canonical single-unit peel certification", "Peel", ("peeled", "state", f"{ns}.PeeledState framework input peelable")),
        node(restoration, "decision", "Invariant-restoration decision", "Restoration"),
        node(ct4, "terminal", "CT4 ordinary-demand handoff", terminal=terminal("ct4", "ct4Terminal", [slot("payload", "payload", f"{ns}.CT4Payload framework input peeled")], "port.accepts (.ct4 payload)")),
        node(ct13, "terminal", "CT13 tier-interaction handoff", terminal=terminal("ct13", "ct13Terminal", [slot("payload", "payload", f"{ns}.CT13Payload framework input peeled")], "port.accepts (.ct13 payload)")),
        node(decrease, "certification", "Strict loop-measure decrease certification", "Decrease", ("decreased", "certificate", f"{ns}.DecreasedState framework input restored")),
    ]
    edges = [
        edge("CT12.edge.begin", entry, scope, "advance", "beginScope", "begin"),
        edge("CT12.edge.scope.exit", scope, scope_t, "scope", "scopeExit", "exit", "Scope", "exit", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")]),
        edge("CT12.edge.scope.ready", scope, measure, "advance", "scopeReady", "ready", "Scope", "ready", [slot("scope", "state", f"{ns}.ScopedState framework input")]),
        edge("CT12.edge.measure.certified", measure, saturation, "advance", "measureCertified", "certified", evidence=[slot("state", "state", f"{ns}.LoopState framework input input.load")]),
        edge("CT12.edge.saturation.close", saturation, c4, "close", "saturationClose", "close", "Saturation", "close", [slot("certificate", "certificate", f"{ns}.C4Certificate framework input state")]),
        edge("CT12.edge.saturation.peel", saturation, peel, "advance", "saturationPeel", "peel", "Saturation", "peel", [slot("peelable", "state", f"{ns}.PeelableState framework input state")]),
        edge("CT12.edge.peel.certified", peel, restoration, "advance", "peelCertified", "certified", evidence=[slot("peeled", "state", f"{ns}.PeeledState framework input peelable")]),
        edge("CT12.edge.restoration.ct4", restoration, ct4, "handoff", "restorationToCT4", "toCT4", "Restoration", "toCT4", [slot("payload", "payload", f"{ns}.CT4Payload framework input peeled")]),
        edge("CT12.edge.restoration.ct13", restoration, ct13, "handoff", "restorationToCT13", "toCT13", "Restoration", "toCT13", [slot("payload", "payload", f"{ns}.CT13Payload framework input peeled")]),
        edge("CT12.edge.restoration.continue", restoration, decrease, "advance", "restorationContinue", "continue", "Restoration", "continue", [slot("restored", "state", f"{ns}.RestoredState framework input peeled next")]),
        edge("CT12.edge.decrease.loop", decrease, saturation, "advance", "decreaseLoop", "repeat", evidence=[slot("decreased", "certificate", f"{ns}.DecreasedState framework input restored")]),
    ]
    contracts = {entry: ["S-Def"], scope: ["S-Meas", "A-Scope"], scope_t: ["A-Scope"], measure: ["S-Meas"], saturation: ["S-Dich"], c4: ["S-Comp", "A-Cert"], peel: ["S-Det"], restoration: ["S-Rest", "S-Rout"], ct4: ["S-Rout", "S-Trig"], ct13: ["S-Rout", "S-Trig"], decrease: ["S-Meas"]}
    instances = [
        instance("scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff", "scopeResult", "scope_terminal", "scope_trace", [entry, scope, scope_t], ["CT12.edge.begin", "CT12.edge.scope.exit"]),
        instance("c4", "framework", "input", "c4Plan", "port", "handoff", "c4Result", "c4_terminal", "c4_trace", [entry, scope, measure, saturation, peel, restoration, decrease, saturation, c4], ["CT12.edge.begin", "CT12.edge.scope.ready", "CT12.edge.measure.certified", "CT12.edge.saturation.peel", "CT12.edge.peel.certified", "CT12.edge.restoration.continue", "CT12.edge.decrease.loop", "CT12.edge.saturation.close"]),
        instance("ct4", "framework", "input", "ct4Plan", "port", "handoff", "ct4Result", "ct4_terminal", "ct4_trace", [entry, scope, measure, saturation, peel, restoration, ct4], ["CT12.edge.begin", "CT12.edge.scope.ready", "CT12.edge.measure.certified", "CT12.edge.saturation.peel", "CT12.edge.peel.certified", "CT12.edge.restoration.ct4"]),
        instance("ct13", "framework", "input", "ct13Plan", "port", "handoff", "ct13Result", "ct13_terminal", "ct13_trace", [entry, scope, measure, saturation, peel, restoration, ct13], ["CT12.edge.begin", "CT12.edge.scope.ready", "CT12.edge.measure.certified", "CT12.edge.saturation.peel", "CT12.edge.peel.certified", "CT12.edge.restoration.ct13"]),
    ]
    return config("CT12", "Well-founded peeling", "CT12 — Peeling loop", nodes, edges, contracts, instances,
                  {"close": ["C4"], "handoff": ["P_12_to_4", "P_12_to_13"]},
                  ["LoopState", "PeelableState", "PeeledState", "RestoredState", "DecreasedState", "C4Certificate"])


def ct13_config() -> dict:
    ns = "StructuralExhaustion.CT13"
    entry, scope, scope_t = "CT13.entry", "CT13.decide.scope", "CT13.terminal.scope"
    availability = "CT13.decide.availability"
    tier, tier_route, ct4 = "CT13.certify.tierOne", "CT13.certify.tierOneRouting", "CT13.terminal.ct4"
    fallback, reconcile = "CT13.certify.fallback", "CT13.decide.reconciliation"
    compare, c4, routing = "CT13.certify.comparison", "CT13.terminal.c4", "CT13.decide.overlapRouting"
    ct9, ct14 = "CT13.terminal.ct9", "CT13.terminal.ct14"
    nodes = [
        node(entry, "entry", "Validated CT13 tier-account entry", "Entry"), node(scope, "decision", "Measurable tier-resource scope", "Scope"),
        node(scope_t, "terminal", "Missing tier-resource scope terminal", terminal=terminal("scope", "scopeTerminal", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")], f"¬ {ns}.ScopeReadyAt framework input")),
        node(availability, "decision", "Tier-one availability decision", "Availability"),
        node(tier, "certification", "Tier-one canonical payment certification", "TierOne", ("tierOne", "state", f"{ns}.TierOneState framework input available")),
        node(tier_route, "certification", "Tier-one account routing certification", "TierOneRouting", ("payload", "payload", f"{ns}.CT4Payload framework input tierOne")),
        node(ct4, "terminal", "CT4 tier-one account handoff", terminal=terminal("ct4", "ct4Terminal", [slot("payload", "payload", f"{ns}.CT4Payload framework input tierOne")], "port.accepts (.ct4 payload)")),
        node(fallback, "certification", "Minimal-obstruction fallback certification", "Fallback", ("fallback", "state", f"{ns}.FallbackState framework input unavailable")),
        node(reconcile, "decision", "Tier-resource reconciliation decision", "Reconciliation"),
        node(compare, "certification", "Combined-capacity certification", "Comparison", ("certificate", "certificate", f"{ns}.C4Certificate framework input reconciled")),
        node(c4, "terminal", "C4 reconciled-tier terminal", terminal=terminal("c4", "c4Terminal", [slot("certificate", "certificate", f"{ns}.C4Certificate framework input reconciled")], "framework.entry.C4Claim input.G input.branch")),
        node(routing, "decision", "Overlap-residual routing", "Routing"),
        node(ct9, "terminal", "CT9 overlap-fibre handoff", terminal=terminal("ct9", "ct9Terminal", [slot("payload", "payload", f"{ns}.CT9Payload framework input overlap")], "port.accepts (.ct9 payload)")),
        node(ct14, "terminal", "CT14 overlap-mass handoff", terminal=terminal("ct14", "ct14Terminal", [slot("payload", "payload", f"{ns}.CT14Payload framework input overlap")], "port.accepts (.ct14 payload)")),
    ]
    edges = [
        edge("CT13.edge.begin", entry, scope, "advance", "beginScope", "begin"), edge("CT13.edge.scope.exit", scope, scope_t, "scope", "scopeExit", "exit", "Scope", "exit", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")]),
        edge("CT13.edge.scope.ready", scope, availability, "advance", "scopeReady", "ready", "Scope", "ready", [slot("scope", "state", f"{ns}.ScopedState framework input")]),
        edge("CT13.edge.availability.yes", availability, tier, "advance", "availabilityYes", "available", "Availability", "available", [slot("available", "state", f"{ns}.AvailableState framework input scope")]),
        edge("CT13.edge.availability.no", availability, fallback, "advance", "availabilityNo", "unavailable", "Availability", "unavailable", [slot("unavailable", "state", f"{ns}.UnavailableState framework input scope")]),
        edge("CT13.edge.tierOne.certified", tier, tier_route, "advance", "tierOneCertified", "certified", evidence=[slot("tierOne", "state", f"{ns}.TierOneState framework input available")]),
        edge("CT13.edge.tierOne.ct4", tier_route, ct4, "handoff", "tierOneToCT4", "toCT4", evidence=[slot("payload", "payload", f"{ns}.CT4Payload framework input tierOne")]),
        edge("CT13.edge.fallback.certified", fallback, reconcile, "advance", "fallbackCertified", "certified", evidence=[slot("fallback", "state", f"{ns}.FallbackState framework input unavailable")]),
        edge("CT13.edge.reconciliation.yes", reconcile, compare, "advance", "reconciliationYes", "reconciled", "Reconciliation", "reconciled", [slot("reconciled", "state", f"{ns}.ReconciledState framework input fallback")]),
        edge("CT13.edge.reconciliation.overlap", reconcile, routing, "advance", "reconciliationOverlap", "overlap", "Reconciliation", "overlap", [slot("overlap", "state", f"{ns}.OverlapState framework input fallback")]),
        edge("CT13.edge.comparison.close", compare, c4, "close", "comparisonClose", "close", evidence=[slot("certificate", "certificate", f"{ns}.C4Certificate framework input reconciled")]),
        edge("CT13.edge.overlap.ct9", routing, ct9, "handoff", "overlapToCT9", "toCT9", "Routing", "toCT9", [slot("payload", "payload", f"{ns}.CT9Payload framework input overlap")]),
        edge("CT13.edge.overlap.ct14", routing, ct14, "handoff", "overlapToCT14", "toCT14", "Routing", "toCT14", [slot("payload", "payload", f"{ns}.CT14Payload framework input overlap")]),
    ]
    contracts = {entry: ["S-Def"], scope: ["A-Scope"], scope_t: ["A-Scope"], availability: ["S-Dich"], tier: ["S-Det"], tier_route: ["S-Rout"], ct4: ["S-Rout", "S-Trig"], fallback: ["S-Def", "S-Det"], reconcile: ["S-Dich", "S-Comp"], compare: ["S-Comp"], c4: ["A-Cert"], routing: ["S-Rout"], ct9: ["S-Rout", "S-Trig"], ct14: ["S-Rout", "S-Trig"]}
    instances = [
        instance("scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff", "scopeResult", "scope_terminal", "scope_trace", [entry, scope, scope_t], ["CT13.edge.begin", "CT13.edge.scope.exit"]),
        instance("ct4", "framework", "input", "ct4Plan", "port", "handoff", "ct4Result", "ct4_terminal", "ct4_trace", [entry, scope, availability, tier, tier_route, ct4], ["CT13.edge.begin", "CT13.edge.scope.ready", "CT13.edge.availability.yes", "CT13.edge.tierOne.certified", "CT13.edge.tierOne.ct4"]),
        instance("c4", "fallbackFramework", "fallbackInput", "c4Plan", "fallbackPort", "fallbackHandoff", "c4Result", "c4_terminal", "c4_trace", [entry, scope, availability, fallback, reconcile, compare, c4], ["CT13.edge.begin", "CT13.edge.scope.ready", "CT13.edge.availability.no", "CT13.edge.fallback.certified", "CT13.edge.reconciliation.yes", "CT13.edge.comparison.close"]),
        instance("ct9", "overlapFramework", "overlapInput", "ct9Plan", "overlapPort", "overlapHandoff", "ct9Result", "ct9_terminal", "ct9_trace", [entry, scope, availability, fallback, reconcile, routing, ct9], ["CT13.edge.begin", "CT13.edge.scope.ready", "CT13.edge.availability.no", "CT13.edge.fallback.certified", "CT13.edge.reconciliation.overlap", "CT13.edge.overlap.ct9"]),
        instance("ct14", "overlapFramework", "overlapInput", "ct14Plan", "overlapPort", "overlapHandoff", "ct14Result", "ct14_terminal", "ct14_trace", [entry, scope, availability, fallback, reconcile, routing, ct14], ["CT13.edge.begin", "CT13.edge.scope.ready", "CT13.edge.availability.no", "CT13.edge.fallback.certified", "CT13.edge.reconciliation.overlap", "CT13.edge.overlap.ct14"]),
    ]
    return config("CT13", "Tiered charging", "CT13 — Tiered charging", nodes, edges, contracts, instances,
                  {"close": ["C4"], "handoff": ["P_13_to_4", "P_13_to_9", "P_13_to_14"]},
                  ["AvailableState", "UnavailableState", "TierOneState", "FallbackState", "ReconciledState", "OverlapState", "C4Certificate"])


def ct14_config() -> dict:
    ns = "StructuralExhaustion.CT14"
    entry, scope, scope_t = "CT14.entry", "CT14.decide.scope", "CT14.terminal.scope"
    bounds, multiplicity = "CT14.certify.bounds", "CT14.decide.multiplicity"
    ct9, ct10, compare, c4 = "CT14.terminal.ct9", "CT14.terminal.ct10", "CT14.certify.comparison", "CT14.terminal.c4"
    nodes = [node(entry, "entry", "Validated CT14 residual-class entry", "Entry"), node(scope, "decision", "Finite capacity-description scope", "Scope"),
        node(scope_t, "terminal", "Missing capacity-description scope terminal", terminal=terminal("scope", "scopeTerminal", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")], f"¬ {ns}.ScopeReadyAt framework input")),
        node(bounds, "certification", "Lower and upper aggregate-bound certification", "Bounds", ("bounds", "state", f"{ns}.BoundsState framework input")),
        node(multiplicity, "decision", "Carried-charge multiplicity decision", "Multiplicity"),
        node(ct9, "terminal", "CT9 unbounded-member handoff", terminal=terminal("ct9", "ct9Terminal", [slot("payload", "payload", f"{ns}.CT9Payload framework input bounds")], "port.accepts (.ct9 payload)")),
        node(ct10, "terminal", "CT10 missing-capacity-label handoff", terminal=terminal("ct10", "ct10Terminal", [slot("payload", "payload", f"{ns}.CT10Payload framework input bounds")], "port.accepts (.ct10 payload)")),
        node(compare, "certification", "Aggregate comparison certification", "Comparison", ("certificate", "certificate", f"{ns}.C4Certificate framework input multiplicity")),
        node(c4, "terminal", "C4 aggregate-capacity terminal", terminal=terminal("c4", "c4Terminal", [slot("certificate", "certificate", f"{ns}.C4Certificate framework input multiplicity")], "framework.entry.C4Claim input.G input.branch"))]
    edges = [edge("CT14.edge.begin", entry, scope, "advance", "beginScope", "begin"), edge("CT14.edge.scope.exit", scope, scope_t, "scope", "scopeExit", "exit", "Scope", "exit", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")]), edge("CT14.edge.scope.ready", scope, bounds, "advance", "scopeReady", "ready", "Scope", "ready", [slot("scope", "state", f"{ns}.ScopedState framework input")]), edge("CT14.edge.bounds.certified", bounds, multiplicity, "advance", "boundsCertified", "certified", evidence=[slot("bounds", "state", f"{ns}.BoundsState framework input")]), edge("CT14.edge.multiplicity.unbounded", multiplicity, ct9, "handoff", "multiplicityUnbounded", "unbounded", "Multiplicity", "unbounded", [slot("payload", "payload", f"{ns}.CT9Payload framework input bounds")]), edge("CT14.edge.multiplicity.missing", multiplicity, ct10, "handoff", "multiplicityMissing", "missingLabel", "Multiplicity", "missingLabel", [slot("payload", "payload", f"{ns}.CT10Payload framework input bounds")]), edge("CT14.edge.multiplicity.counted", multiplicity, compare, "advance", "multiplicityCounted", "counted", "Multiplicity", "counted", [slot("multiplicity", "state", f"{ns}.MultiplicityState framework input bounds")]), edge("CT14.edge.comparison.close", compare, c4, "close", "comparisonClose", "close", evidence=[slot("certificate", "certificate", f"{ns}.C4Certificate framework input multiplicity")])]
    contracts = {entry: ["S-Def"], scope: ["A-Scope"], scope_t: ["A-Scope"], bounds: ["S-Comp"], multiplicity: ["S-Dich", "S-Comp", "S-Rout"], ct9: ["S-Rout", "S-Trig"], ct10: ["S-Rout", "S-Trig"], compare: ["S-Comp"], c4: ["A-Cert"]}
    base = [entry, scope, bounds, multiplicity]; eb = ["CT14.edge.begin", "CT14.edge.scope.ready", "CT14.edge.bounds.certified"]
    instances = [instance("scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff", "scopeResult", "scope_terminal", "scope_trace", [entry, scope, scope_t], ["CT14.edge.begin", "CT14.edge.scope.exit"]), instance("ct9", "framework", "input", "ct9Plan", "port", "handoff", "ct9Result", "ct9_terminal", "ct9_trace", base + [ct9], eb + ["CT14.edge.multiplicity.unbounded"]), instance("ct10", "framework", "input", "ct10Plan", "port", "handoff", "ct10Result", "ct10_terminal", "ct10_trace", base + [ct10], eb + ["CT14.edge.multiplicity.missing"]), instance("c4", "framework", "input", "c4Plan", "port", "handoff", "c4Result", "c4_terminal", "c4_trace", base + [compare, c4], eb + ["CT14.edge.multiplicity.counted", "CT14.edge.comparison.close"])]
    return config("CT14", "Aggregate closure", "CT14 — Aggregate closure", nodes, edges, contracts, instances, {"close": ["C4"], "handoff": ["P_14_to_9", "P_14_to_10"]}, ["BoundsState", "MultiplicityState", "C4Certificate"])


def ct15_config() -> dict:
    ns = "StructuralExhaustion.CT15"
    entry, scope, scope_t = "CT15.entry", "CT15.decide.scope", "CT15.terminal.scope"
    rank, drop, route = "CT15.certify.rank", "CT15.decide.rankDrop", "CT15.decide.dependenceRouting"
    ct3, ct7, ct16 = "CT15.terminal.ct3", "CT15.terminal.ct7", "CT15.terminal.ct16"
    ledger, compare, c4, ct4 = "CT15.certify.ledger", "CT15.decide.comparison", "CT15.terminal.c4", "CT15.terminal.ct4"
    nodes = [node(entry, "entry", "Validated CT15 rank-data entry", "Entry"), node(scope, "decision", "Finite target-relative-rank scope", "Scope"), node(scope_t, "terminal", "Missing finite-rank scope terminal", terminal=terminal("scope", "scopeTerminal", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")], f"¬ {ns}.ScopeReadyAt framework input")), node(rank, "certification", "Target-relative rank certification", "Rank", ("rank", "state", f"{ns}.RankState framework input")), node(drop, "decision", "Rank-drop decision", "RankDrop"), node(route, "decision", "Structural-dependence routing", "DependenceRouting"), node(ct3, "terminal", "CT3 rank-defect handoff", terminal=terminal("ct3", "ct3Terminal", [slot("payload", "payload", f"{ns}.CT3Payload framework input dependence")], "port.accepts (.ct3 payload)")), node(ct7, "terminal", "CT7 rank-exchange handoff", terminal=terminal("ct7", "ct7Terminal", [slot("payload", "payload", f"{ns}.CT7Payload framework input dependence")], "port.accepts (.ct7 payload)")), node(ct16, "terminal", "CT16 rank-delocalization handoff", terminal=terminal("ct16", "ct16Terminal", [slot("payload", "payload", f"{ns}.CT16Payload framework input dependence")], "port.accepts (.ct16 payload)")), node(ledger, "certification", "Full-rank ledger certification", "Ledger", ("ledger", "state", f"{ns}.LedgerState framework input full")), node(compare, "decision", "Rank-budget comparison", "Comparison"), node(c4, "terminal", "C4 rank-budget terminal", terminal=terminal("c4", "c4Terminal", [slot("certificate", "certificate", f"{ns}.C4Certificate framework input ledger")], "framework.entry.C4Claim input.G input.branch")), node(ct4, "terminal", "CT4 rank-ledger handoff", terminal=terminal("ct4", "ct4Terminal", [slot("payload", "payload", f"{ns}.CT4Payload framework input ledger")], "port.accepts (.ct4 payload)"))]
    edges = [edge("CT15.edge.begin", entry, scope, "advance", "beginScope", "begin"), edge("CT15.edge.scope.exit", scope, scope_t, "scope", "scopeExit", "exit", "Scope", "exit", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")]), edge("CT15.edge.scope.ready", scope, rank, "advance", "scopeReady", "ready", "Scope", "ready", [slot("scope", "state", f"{ns}.ScopedState framework input")]), edge("CT15.edge.rank.certified", rank, drop, "advance", "rankCertified", "certified", evidence=[slot("rank", "state", f"{ns}.RankState framework input")]), edge("CT15.edge.rank.dependent", drop, route, "advance", "rankDependent", "dependent", "RankDrop", "dependent", [slot("dependence", "state", f"{ns}.DependenceState framework input rank")]), edge("CT15.edge.rank.full", drop, ledger, "advance", "rankFull", "full", "RankDrop", "full", [slot("full", "state", f"{ns}.FullRankState framework input rank")]), edge("CT15.edge.dependence.ct3", route, ct3, "handoff", "dependenceToCT3", "toCT3", "DependenceRouting", "toCT3", [slot("payload", "payload", f"{ns}.CT3Payload framework input dependence")]), edge("CT15.edge.dependence.ct7", route, ct7, "handoff", "dependenceToCT7", "toCT7", "DependenceRouting", "toCT7", [slot("payload", "payload", f"{ns}.CT7Payload framework input dependence")]), edge("CT15.edge.dependence.ct16", route, ct16, "handoff", "dependenceToCT16", "toCT16", "DependenceRouting", "toCT16", [slot("payload", "payload", f"{ns}.CT16Payload framework input dependence")]), edge("CT15.edge.ledger.certified", ledger, compare, "advance", "ledgerCertified", "certified", evidence=[slot("ledger", "state", f"{ns}.LedgerState framework input full")]), edge("CT15.edge.comparison.close", compare, c4, "close", "comparisonClose", "close", "Comparison", "close", [slot("certificate", "certificate", f"{ns}.C4Certificate framework input ledger")]), edge("CT15.edge.comparison.ct4", compare, ct4, "handoff", "comparisonToCT4", "toCT4", "Comparison", "toCT4", [slot("payload", "payload", f"{ns}.CT4Payload framework input ledger")])]
    contracts = {entry: ["S-Def"], scope: ["A-Scope"], scope_t: ["A-Scope"], rank: ["S-Def"], drop: ["S-Dich"], route: ["S-Rout"], ct3: ["S-Rout", "S-Trig"], ct7: ["S-Rout", "S-Trig"], ct16: ["S-Rout", "S-Trig"], ledger: ["S-Comp"], compare: ["S-Dich", "S-Comp", "S-Rout"], c4: ["A-Cert"], ct4: ["S-Rout", "S-Trig"]}
    base = [entry, scope, rank, drop]; eb = ["CT15.edge.begin", "CT15.edge.scope.ready", "CT15.edge.rank.certified"]
    instances = [instance("scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff", "scopeResult", "scope_terminal", "scope_trace", [entry, scope, scope_t], ["CT15.edge.begin", "CT15.edge.scope.exit"]), instance("ct3", "framework", "input", "ct3Plan", "port", "handoff", "ct3Result", "ct3_terminal", "ct3_trace", base + [route, ct3], eb + ["CT15.edge.rank.dependent", "CT15.edge.dependence.ct3"]), instance("ct7", "framework", "input", "ct7Plan", "port", "handoff", "ct7Result", "ct7_terminal", "ct7_trace", base + [route, ct7], eb + ["CT15.edge.rank.dependent", "CT15.edge.dependence.ct7"]), instance("ct16", "framework", "input", "ct16Plan", "port", "handoff", "ct16Result", "ct16_terminal", "ct16_trace", base + [route, ct16], eb + ["CT15.edge.rank.dependent", "CT15.edge.dependence.ct16"]), instance("c4", "framework", "input", "c4Plan", "port", "handoff", "c4Result", "c4_terminal", "c4_trace", base + [ledger, compare, c4], eb + ["CT15.edge.rank.full", "CT15.edge.ledger.certified", "CT15.edge.comparison.close"]), instance("ct4", "framework", "input", "ct4Plan", "port", "handoff", "ct4Result", "ct4_terminal", "ct4_trace", base + [ledger, compare, ct4], eb + ["CT15.edge.rank.full", "CT15.edge.ledger.certified", "CT15.edge.comparison.ct4"])]
    return config("CT15", "Rank forcing", "CT15 — Rank forcing", nodes, edges, contracts, instances, {"close": ["C4"], "handoff": ["P_15_to_3", "P_15_to_7", "P_15_to_16", "P_15_to_4"]}, ["RankState", "DependenceState", "FullRankState", "LedgerState", "C4Certificate"])


def ct16_config() -> dict:
    ns = "StructuralExhaustion.CT16"
    entry, support, ct3 = "CT16.entry", "CT16.decide.support", "CT16.terminal.ct3"
    scope, scope_t, closed, equality = "CT16.decide.scope", "CT16.terminal.scope", "CT16.certify.closedType", "CT16.decide.equality"
    c2, ct10 = "CT16.terminal.c2", "CT16.terminal.ct10"
    nodes = [node(entry, "entry", "Validated CT16 support datum", "Entry"), node(support, "decision", "Proper/whole support decision", "Support"), node(ct3, "terminal", "CT3 proper-piece handoff", terminal=terminal("ct3", "ct3Terminal", [slot("payload", "payload", f"{ns}.CT3Payload framework input proper")], "port.accepts (.ct3 payload)")), node(scope, "decision", "Finite closed-type scope", "Scope"), node(scope_t, "terminal", "Noncomputable closed-type scope terminal", terminal=terminal("scope", "scopeTerminal", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")], f"¬ {ns}.ScopeReadyAt framework input")), node(closed, "certification", "Exact closed-type certification", "ClosedType", ("closed", "state", f"{ns}.ClosedTypeState framework input scope")), node(equality, "decision", "Literal closed-type equality decision", "Equality"), node(c2, "terminal", "C2 whole-object identification terminal", terminal=terminal("c2", "c2Terminal", [slot("certificate", "certificate", f"{ns}.C2Certificate framework input closed")], "framework.entry.C2Claim input.G input.branch")), node(ct10, "terminal", "CT10 distinct-closed-type handoff", terminal=terminal("ct10", "ct10Terminal", [slot("payload", "payload", f"{ns}.CT10Payload framework input closed")], "port.accepts (.ct10 payload)"))]
    edges = [edge("CT16.edge.begin", entry, support, "advance", "beginSupport", "begin"), edge("CT16.edge.support.proper", support, ct3, "handoff", "supportProper", "proper", "Support", "proper", [slot("payload", "payload", f"{ns}.CT3Payload framework input proper")]), edge("CT16.edge.support.whole", support, scope, "advance", "supportWhole", "whole", "Support", "whole", [slot("whole", "state", f"{ns}.WholeState framework input")]), edge("CT16.edge.scope.exit", scope, scope_t, "scope", "scopeExit", "exit", "Scope", "exit", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")]), edge("CT16.edge.scope.ready", scope, closed, "advance", "scopeReady", "ready", "Scope", "ready", [slot("scope", "state", f"{ns}.ScopedState framework input whole")]), edge("CT16.edge.closedType.certified", closed, equality, "advance", "closedTypeCertified", "certified", evidence=[slot("closed", "state", f"{ns}.ClosedTypeState framework input scope")]), edge("CT16.edge.equality.close", equality, c2, "close", "equalityClose", "equal", "Equality", "equal", [slot("certificate", "certificate", f"{ns}.C2Certificate framework input closed")]), edge("CT16.edge.equality.distinct", equality, ct10, "handoff", "equalityDistinct", "distinct", "Equality", "distinct", [slot("payload", "payload", f"{ns}.CT10Payload framework input closed")])]
    contracts = {entry: ["S-Def"], support: ["S-Dich", "S-Rout"], ct3: ["S-Rout", "S-Trig"], scope: ["A-Scope"], scope_t: ["A-Scope"], closed: ["S-Equiv"], equality: ["S-Dich", "S-Equiv", "S-Rout"], c2: ["A-Cert"], ct10: ["S-Rout", "S-Trig"]}
    instances = [instance("ct3", "framework", "input", "ct3Plan", "port", "handoff", "ct3Result", "ct3_terminal", "ct3_trace", [entry, support, ct3], ["CT16.edge.begin", "CT16.edge.support.proper"]), instance("scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff", "scopeResult", "scope_terminal", "scope_trace", [entry, support, scope, scope_t], ["CT16.edge.begin", "CT16.edge.support.whole", "CT16.edge.scope.exit"]), instance("c2", "framework", "input", "c2Plan", "port", "handoff", "c2Result", "c2_terminal", "c2_trace", [entry, support, scope, closed, equality, c2], ["CT16.edge.begin", "CT16.edge.support.whole", "CT16.edge.scope.ready", "CT16.edge.closedType.certified", "CT16.edge.equality.close"]), instance("ct10", "framework", "input", "ct10Plan", "port", "handoff", "ct10Result", "ct10_terminal", "ct10_trace", [entry, support, scope, closed, equality, ct10], ["CT16.edge.begin", "CT16.edge.support.whole", "CT16.edge.scope.ready", "CT16.edge.closedType.certified", "CT16.edge.equality.distinct"])]
    return config("CT16", "Whole-object exact types", "CT16 — Whole-object exact types", nodes, edges, contracts, instances, {"close": ["C2"], "handoff": ["P_16_to_3", "P_16_to_10"]}, ["ProperState", "WholeState", "ScopedState", "ClosedTypeState", "C2Certificate"])


def ct17_config() -> dict:
    ns = "StructuralExhaustion.CT17"
    entry, scope, scope_t = "CT17.entry", "CT17.decide.scope", "CT17.terminal.scope"
    compatibility, separation, ct3, ct10 = "CT17.decide.compatibility", "CT17.decide.separation", "CT17.terminal.ct3", "CT17.terminal.ct10"
    block, scale, survivors, c5, ct8 = "CT17.certify.block", "CT17.decide.scale", "CT17.decide.survivors", "CT17.terminal.c5", "CT17.terminal.ct8"
    arithmetic, c1, ct14 = "CT17.decide.arithmetic", "CT17.terminal.c1", "CT17.terminal.ct14"
    nodes = [node(entry, "entry", "Validated CT17 sparse-target entry", "Entry"), node(scope, "decision", "Bounded-offset arithmetic scope", "Scope"), node(scope_t, "terminal", "Missing bounded-offset scope terminal", terminal=terminal("scope", "scopeTerminal", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")], f"¬ {ns}.ScopeReadyAt framework input")), node(compatibility, "decision", "Common-branch offset compatibility decision", "Compatibility"), node(separation, "decision", "Incompatible-completion separation", "Separation"), node(ct3, "terminal", "CT3 completion-type handoff", terminal=terminal("ct3", "ct3Terminal", [slot("payload", "payload", f"{ns}.CT3Payload framework input state")], "port.accepts (.ct3 payload)")), node(ct10, "terminal", "CT10 completion-label handoff", terminal=terminal("ct10", "ct10Terminal", [slot("payload", "payload", f"{ns}.CT10Payload framework input state")], "port.accepts (.ct10 payload)")), node(block, "certification", "Target-thickened block certification", "Block", ("block", "state", f"{ns}.BlockState framework input compatible")), node(scale, "decision", "Finite/repeated scale decision", "Scale"), node(survivors, "decision", "Finite-survivor decision", "Survivors"), node(c5, "terminal", "C5 finite-survivor exhaustion terminal", terminal=terminal("c5", "c5Terminal", [slot("certificate", "certificate", f"{ns}.C5Certificate framework input finite")], "framework.entry.C5Claim input.G input.branch")), node(ct8, "terminal", "CT8 finite-survivor handoff", terminal=terminal("ct8", "ct8Terminal", [slot("payload", "payload", f"{ns}.CT8Payload framework input finite")], "port.accepts (.ct8 payload)")), node(arithmetic, "decision", "Large-scale arithmetic decision", "Arithmetic"), node(c1, "terminal", "C1 arithmetic target-hit terminal", terminal=terminal("c1", "c1Terminal", [slot("certificate", "certificate", f"{ns}.C1Certificate framework input repeated")], "framework.entry.C1Claim input.G input.branch")), node(ct14, "terminal", "CT14 arithmetic-mass handoff", terminal=terminal("ct14", "ct14Terminal", [slot("payload", "payload", f"{ns}.CT14Payload framework input repeated")], "port.accepts (.ct14 payload)"))]
    edges = [edge("CT17.edge.begin", entry, scope, "advance", "beginScope", "begin"), edge("CT17.edge.scope.exit", scope, scope_t, "scope", "scopeExit", "exit", "Scope", "exit", [slot("candidate", "state", f"{ns}.ScopeCandidate framework input")]), edge("CT17.edge.scope.ready", scope, compatibility, "advance", "scopeReady", "ready", "Scope", "ready", [slot("scope", "state", f"{ns}.ScopedState framework input")]), edge("CT17.edge.compatibility.yes", compatibility, block, "advance", "compatibilityYes", "compatible", "Compatibility", "compatible", [slot("compatible", "state", f"{ns}.CompatibleState framework input scope")]), edge("CT17.edge.compatibility.no", compatibility, separation, "advance", "compatibilityNo", "incompatible", "Compatibility", "incompatible", [slot("state", "state", f"{ns}.IncompatibleState framework input scope")]), edge("CT17.edge.separation.ct3", separation, ct3, "handoff", "separationToCT3", "toCT3", "Separation", "toCT3", [slot("payload", "payload", f"{ns}.CT3Payload framework input state")]), edge("CT17.edge.separation.ct10", separation, ct10, "handoff", "separationToCT10", "toCT10", "Separation", "toCT10", [slot("payload", "payload", f"{ns}.CT10Payload framework input state")]), edge("CT17.edge.block.certified", block, scale, "advance", "blockCertified", "certified", evidence=[slot("block", "state", f"{ns}.BlockState framework input compatible")]), edge("CT17.edge.scale.finite", scale, survivors, "advance", "scaleFinite", "finite", "Scale", "finite", [slot("finite", "state", f"{ns}.FiniteState framework input block")]), edge("CT17.edge.scale.repeated", scale, arithmetic, "advance", "scaleRepeated", "repeated", "Scale", "repeated", [slot("repeated", "state", f"{ns}.RepeatedState framework input block")]), edge("CT17.edge.survivors.exhausted", survivors, c5, "close", "survivorsExhausted", "exhausted", "Survivors", "exhausted", [slot("certificate", "certificate", f"{ns}.C5Certificate framework input finite")]), edge("CT17.edge.survivors.ct8", survivors, ct8, "handoff", "survivorsToCT8", "persist", "Survivors", "persist", [slot("payload", "payload", f"{ns}.CT8Payload framework input finite")]), edge("CT17.edge.arithmetic.close", arithmetic, c1, "close", "arithmeticClose", "close", "Arithmetic", "close", [slot("certificate", "certificate", f"{ns}.C1Certificate framework input repeated")]), edge("CT17.edge.arithmetic.ct14", arithmetic, ct14, "handoff", "arithmeticToCT14", "residual", "Arithmetic", "residual", [slot("payload", "payload", f"{ns}.CT14Payload framework input repeated")])]
    contracts = {entry: ["S-Def"], scope: ["A-Scope"], scope_t: ["A-Scope"], compatibility: ["S-Dich", "S-Rout"], separation: ["S-Rout"], ct3: ["S-Rout", "S-Trig"], ct10: ["S-Rout", "S-Trig"], block: ["S-Comp"], scale: ["S-Dich"], survivors: ["S-Dich", "S-Comp", "S-Rout"], c5: ["A-Cert"], ct8: ["S-Rout", "S-Trig"], arithmetic: ["S-Dich", "S-Comp", "S-Rout"], c1: ["A-Cert"], ct14: ["S-Rout", "S-Trig"]}
    base = [entry, scope, compatibility]; eb = ["CT17.edge.begin", "CT17.edge.scope.ready"]
    instances = [instance("scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff", "scopeResult", "scope_terminal", "scope_trace", [entry, scope, scope_t], ["CT17.edge.begin", "CT17.edge.scope.exit"]), instance("ct3", "separationFramework", "separationInput", "ct3Plan", "separationPort", "separationHandoff", "ct3Result", "ct3_terminal", "ct3_trace", base + [separation, ct3], eb + ["CT17.edge.compatibility.no", "CT17.edge.separation.ct3"]), instance("ct10", "separationFramework", "separationInput", "ct10Plan", "separationPort", "separationHandoff", "ct10Result", "ct10_terminal", "ct10_trace", base + [separation, ct10], eb + ["CT17.edge.compatibility.no", "CT17.edge.separation.ct10"]), instance("c5", "framework", "input", "c5Plan", "port", "handoff", "c5Result", "c5_terminal", "c5_trace", base + [block, scale, survivors, c5], eb + ["CT17.edge.compatibility.yes", "CT17.edge.block.certified", "CT17.edge.scale.finite", "CT17.edge.survivors.exhausted"]), instance("ct8", "framework", "input", "ct8Plan", "port", "handoff", "ct8Result", "ct8_terminal", "ct8_trace", base + [block, scale, survivors, ct8], eb + ["CT17.edge.compatibility.yes", "CT17.edge.block.certified", "CT17.edge.scale.finite", "CT17.edge.survivors.ct8"]), instance("c1", "framework", "input", "c1Plan", "port", "handoff", "c1Result", "c1_terminal", "c1_trace", base + [block, scale, arithmetic, c1], eb + ["CT17.edge.compatibility.yes", "CT17.edge.block.certified", "CT17.edge.scale.repeated", "CT17.edge.arithmetic.close"]), instance("ct14", "framework", "input", "ct14Plan", "port", "handoff", "ct14Result", "ct14_terminal", "ct14_trace", base + [block, scale, arithmetic, ct14], eb + ["CT17.edge.compatibility.yes", "CT17.edge.block.certified", "CT17.edge.scale.repeated", "CT17.edge.arithmetic.ct14"])]
    return config("CT17", "Target thickening", "CT17 — Target thickening", nodes, edges, contracts, instances, {"close": ["C1", "C5"], "handoff": ["P_17_to_3", "P_17_to_10", "P_17_to_8", "P_17_to_14"]}, ["CompatibleState", "IncompatibleState", "BlockState", "FiniteState", "RepeatedState", "C1Certificate", "C5Certificate"])


def main() -> int:
    total = [0, 0, 0]
    for cfg in (ct11_config(), ct12_config(), ct13_config(), ct14_config(),
                ct15_config(), ct16_config(), ct17_config()):
        counts = generate(cfg)
        total = [left + right for left, right in zip(total, counts)]
        print(f"Wrote {cfg['version']}: {counts[0]} nodes, {counts[1]} edges, {counts[2]} instances")
    print(f"Total CT11-CT17: {total[0]} nodes, {total[1]} edges, {total[2]} instances")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
