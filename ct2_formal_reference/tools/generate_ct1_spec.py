#!/usr/bin/env python3
"""Generate the CT1-v1 semantic specification from one typed graph table."""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TACTIC_ROOT = ROOT / "framework/CT1"
NODE_ROOT = TACTIC_ROOT / "nodes"
SCHEMA_ROOT = ROOT / "schemas/concrete/nodes"
INSTANCE_ROOT = ROOT / "instances/ct1"
VERSION = "CT1-v1"
SECTION = "CT1 — Target-test alignment and first closure"
NS = "StructuralExhaustion.CT1"


def write(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def ref(declaration: str, source: str, kind: str, module: str | None = None) -> dict:
    return {
        "module": module or declaration.rsplit(".", 1)[0],
        "declaration": declaration,
        "sourceFile": source,
        "declarationKind": kind,
    }


def slot(slot_id: str, value_kind: str, type_expression: str) -> dict:
    return {
        "slotId": slot_id,
        "valueKind": value_kind,
        "typeExpression": type_expression,
    }


def binding(role: str, local_name: str, declaration_ref: dict) -> dict:
    return {"role": role, "localName": local_name, "ref": declaration_ref}


def node_ref(namespace: str, name: str, source: str, kind: str) -> dict:
    return ref(f"{namespace}.{name}", source, kind, namespace)


ENTRY = "CT1.entry"
SCOPE = "CT1.decide.scope"
SCOPE_TERM = "CT1.terminal.scope"
EQUIV = "CT1.certify.equivalence"
REALIZATION = "CT1.decide.realization"
C1_TERM = "CT1.terminal.c1"
PAYLOAD = "CT1.decide.payload"
ROUTE_TERMINALS = {
    "ct2": "CT1.terminal.ct2",
    "ct3": "CT1.terminal.ct3",
    "ct4": "CT1.terminal.ct4",
    "ct5": "CT1.terminal.ct5",
    "ct6": "CT1.terminal.ct6",
    "ct17": "CT1.terminal.ct17",
}

EDGE_DATA = [
    ("CT1.edge.begin", ENTRY, SCOPE, "advance", "beginScope", "begin", None, []),
    (
        "CT1.edge.scope.exit", SCOPE, SCOPE_TERM, "scope", "scopeExit", "exit",
        ("Scope", "Decision.exit", "StructuralExhaustion.CT1.ScopeCandidate framework input", "candidate"),
        [],
    ),
    (
        "CT1.edge.scope.ready", SCOPE, EQUIV, "advance", "scopeReady", "ready",
        ("Scope", "Decision.ready", "StructuralExhaustion.CT1.ScopedState framework input", "scopeState"),
        [],
    ),
    (
        "CT1.edge.equivalence.certified", EQUIV, REALIZATION, "advance",
        "equivalenceCertified", "certified", None,
        [slot("equivalence", "state", "StructuralExhaustion.CT1.EquivalenceState framework input")],
    ),
    (
        "CT1.edge.realization.hit", REALIZATION, C1_TERM, "close", "realizationHit", "hit",
        ("Realization", "Decision.hit", "StructuralExhaustion.CT1.C1Certificate framework input", "certificate"),
        [],
    ),
    (
        "CT1.edge.realization.avoiding", REALIZATION, PAYLOAD, "advance",
        "realizationAvoiding", "avoiding",
        ("Realization", "Decision.avoiding", "StructuralExhaustion.CT1.AvoidingState framework input", "avoiding"),
        [],
    ),
]
for consumer, terminal in ROUTE_TERMINALS.items():
    upper = consumer.upper()
    EDGE_DATA.append(
        (
            f"CT1.edge.payload.{consumer}", PAYLOAD, terminal, "handoff",
            f"payloadTo{upper}", f"to{upper}",
            (
                "Payload", f"Decision.to{upper}",
                f"StructuralExhaustion.CT1.{upper}Payload framework input avoiding",
                "payload",
            ),
            [slot("avoiding", "state", "StructuralExhaustion.CT1.AvoidingState framework input")],
        )
    )


def graph_edge_ref(name: str) -> dict:
    return ref(
        f"{NS}.Graph.Edge.{name}",
        "StructuralExhaustion/CT1/Graph.lean",
        "constructor",
        f"{NS}.Graph",
    )


def decision_ref(node_name: str, suffix: str) -> dict:
    namespace = f"{NS}.Nodes.{node_name}"
    return ref(
        f"{namespace}.{suffix}",
        f"StructuralExhaustion/CT1/Nodes/{node_name}.lean",
        "constructor",
        namespace,
    )


TRANSITIONS: list[dict] = []
BRANCHES: dict[str, list[dict]] = {SCOPE: [], REALIZATION: [], PAYLOAD: []}
for edge_id, source, target, kind, edge_ctor, tag, decision, prefix_slots in EDGE_DATA:
    evidence = list(prefix_slots)
    result_ref = None
    if decision is not None:
        node_name, suffix, type_expression, slot_id = decision
        result_ref = decision_ref(node_name, suffix)
        evidence.append(slot(slot_id, "payload" if slot_id == "payload" else "state", type_expression))
    guard = {"kind": "branch" if result_ref else "unconditional", "branchTag": tag, "evidenceSlots": evidence}
    if result_ref:
        guard["resultConstructorRef"] = result_ref
        BRANCHES[source].append(
            {
                "branchTag": tag,
                "meaning": f"The node returns the proof-carrying {tag} constructor.",
                "resultConstructorRef": result_ref,
                "evidenceSlots": evidence,
                "transitionId": edge_id,
            }
        )
    TRANSITIONS.append(
        {
            "transitionId": edge_id,
            "fromNodeId": source,
            "toNodeId": target,
            "kind": kind,
            "transitionConstructorRef": graph_edge_ref(edge_ctor),
            "guard": guard,
        }
    )


CONTRACTS_BY_NODE = {
    ENTRY: ["S-Def"],
    SCOPE: ["S-Dich", "A-Scope"],
    SCOPE_TERM: ["A-Scope"],
    EQUIV: ["S-Equiv"],
    REALIZATION: ["S-Dich", "S-Equiv", "S-Pers"],
    C1_TERM: ["S-Equiv", "A-Cert"],
    PAYLOAD: ["S-Dich", "S-Pers", "S-Rout"],
    **{terminal: ["S-Pers", "S-Rout", "S-Trig"] for terminal in ROUTE_TERMINALS.values()},
}


def implementation(namespace: str, source: str, declarations: list[tuple[str, str, str, str]]) -> dict:
    return {
        "namespace": namespace,
        "sourceFile": source,
        "requiredRoles": sorted({role for role, _, _, _ in declarations}),
        "declarations": [
            binding(role, local, node_ref(namespace, local, source, kind))
            for role, local, kind, _ in declarations
        ],
    }


def decision_node(
    node_id: str,
    title: str,
    node_name: str,
    inputs: list[dict],
    output_type: str,
    informal: str,
) -> dict:
    namespace = f"{NS}.Nodes.{node_name}"
    source = f"StructuralExhaustion/CT1/Nodes/{node_name}.lean"
    contract_ref = node_ref(namespace, "Contract", source, "abbrev")
    declarations = [
        ("contract", "Contract", "abbrev", ""),
        ("decision", "Decision", "inductive", ""),
        ("plan", "Plan", "structure", ""),
        ("implementation", "run", "definition", ""),
    ]
    return {
        "artifactType": "formalNodeSpec",
        "schemaVersion": "2.0.0",
        "graphVersion": VERSION,
        "nodeId": node_id,
        "nodeKind": "decision",
        "title": title,
        "human": {
            "informal": informal,
            "latex": "",
            "whyNeeded": "Its indexed result is the complete input contract for the selected successor.",
            "failureMeaning": "No edge can be selected without constructing its declared evidence.",
            "proofHints": ["Construct a decision constructor; do not return an unchecked tag."],
        },
        "contracts": CONTRACTS_BY_NODE[node_id],
        "formalContract": {
            "contractId": f"{node_id}.contract",
            "executionMode": "computable",
            "leanContractRef": contract_ref,
            "inputs": inputs,
            "outputs": [slot("decision", "data", output_type)],
            "branches": BRANCHES[node_id],
            "dischargeCondition": "The Lean contract resolves and its constructors match the outgoing typed edges exactly.",
        },
        "leanImplementation": implementation(namespace, source, declarations),
        "source": {"document": "branch_closure_methodology_extended.tex", "section": SECTION, "diagramKey": node_id.split(".")[-1]},
    }


def terminal_node(
    node_id: str,
    terminal_case: str,
    terminal_ctor: str,
    node_ctor: str,
    outcome_ctor: str,
    evidence: list[dict],
    claim: str,
) -> dict:
    graph_source = "StructuralExhaustion/CT1/Graph.lean"
    execution_source = "StructuralExhaustion/CT1/Execution.lean"
    graph_ns = f"{NS}.Graph"
    terminal_ref = ref(f"{graph_ns}.Terminal.{terminal_ctor}", graph_source, "constructor", graph_ns)
    outcome_ref = ref(f"{NS}.Outcome.{outcome_ctor}", execution_source, "constructor", NS)
    declarations = [
        binding("state", "Terminal", ref(f"{graph_ns}.Terminal", graph_source, "inductive", graph_ns)),
        binding("constructor", terminal_ctor, terminal_ref),
        binding("constructor", node_ctor, ref(f"{graph_ns}.NodeId.{node_ctor}", graph_source, "constructor", graph_ns)),
        binding("constructor", outcome_ctor, ref(f"{NS}.RawOutcome.{outcome_ctor}", execution_source, "constructor", NS)),
        binding("constructor", outcome_ctor, outcome_ref),
    ]
    return {
        "artifactType": "formalNodeSpec",
        "schemaVersion": "2.0.0",
        "graphVersion": VERSION,
        "nodeId": node_id,
        "nodeKind": "terminal",
        "title": f"{terminal_case} terminal",
        "human": {
            "informal": f"The semantic run ends at the exact {terminal_case} outcome.",
            "latex": "",
            "whyNeeded": "The terminal index prevents a payload or certificate from being attached to another route.",
            "failureMeaning": "The terminal is unavailable unless its predecessor evidence has been constructed.",
            "proofHints": ["Use the indexed RawOutcome and Outcome constructors."],
        },
        "contracts": CONTRACTS_BY_NODE[node_id],
        "formalContract": {
            "contractId": f"{node_id}.contract",
            "executionMode": "proof_only",
            "leanContractRef": ref(f"{NS}.RawOutcome", execution_source, "inductive", NS),
            "inputs": [
                slot("framework", "data", f"{NS}.Framework"),
                slot("input", "state", f"{NS}.Input framework"),
                *evidence,
            ],
            "outputs": [slot("rawOutcome", "payload", f"{NS}.RawOutcome framework input .{terminal_ctor}")],
            "dischargeCondition": "The terminal constructor, raw outcome, certified outcome, and incoming typed edge all resolve.",
        },
        "leanImplementation": {
            "namespace": graph_ns,
            "sourceFile": graph_source,
            "requiredRoles": ["state", "constructor"],
            "declarations": declarations,
        },
        "source": {"document": "branch_closure_methodology_extended.tex", "section": SECTION, "diagramKey": terminal_ctor},
        "terminal": {
            "terminalCase": terminal_case,
            "terminalConstructorRef": terminal_ref,
            "outcomeConstructorRef": outcome_ref,
            "claimTypeExpression": claim,
            "evidenceSlots": evidence,
        },
    }


def build_nodes() -> list[dict]:
    entry_source = "StructuralExhaustion/CT1/Nodes/Entry.lean"
    entry_ns = f"{NS}.Nodes.Entry"
    entry = {
        "artifactType": "formalNodeSpec",
        "schemaVersion": "2.0.0",
        "graphVersion": VERSION,
        "nodeId": ENTRY,
        "nodeKind": "entry",
        "title": "Validated CT1 entry",
        "human": {
            "informal": "Admit the ambient object, branch state, and baseline proof without mixing in node implementations.",
            "latex": "(G, B, \\operatorname{Baseline}(G))",
            "whyNeeded": "Static target and test vocabulary belongs to Framework; runtime evidence begins in Input.",
            "failureMeaning": "The CT1 machine is not invoked until Input has been constructed.",
            "proofHints": ["Entry.run is the identity boundary."],
        },
        "contracts": CONTRACTS_BY_NODE[ENTRY],
        "formalContract": {
            "contractId": f"{ENTRY}.contract",
            "executionMode": "declarative",
            "leanContractRef": node_ref(entry_ns, "Contract", entry_source, "abbrev"),
            "inputs": [slot("input", "state", f"{NS}.Input framework")],
            "outputs": [slot("entry", "state", f"{NS}.Input framework")],
            "dischargeCondition": "Entry.run preserves the validated Input definitionally.",
        },
        "leanImplementation": implementation(
            entry_ns, entry_source,
            [("contract", "Contract", "abbrev", ""), ("implementation", "run", "definition", "")],
        ),
        "source": {"document": "branch_closure_methodology_extended.tex", "section": SECTION, "diagramKey": "entry"},
    }
    scope = decision_node(
        SCOPE, "Scope admission", "Scope",
        [slot("input", "state", f"{NS}.Input framework"), slot("plan", "algorithm", f"{NS}.Nodes.Scope.Plan framework input")],
        f"{NS}.Nodes.Scope.Contract framework input",
        "Decide between a typed scope exit and a scope-ready state.",
    )
    equivalence_source = "StructuralExhaustion/CT1/Nodes/Equivalence.lean"
    equivalence_ns = f"{NS}.Nodes.Equivalence"
    equivalence = {
        "artifactType": "formalNodeSpec",
        "schemaVersion": "2.0.0",
        "graphVersion": VERSION,
        "nodeId": EQUIV,
        "nodeKind": "certification",
        "title": "Target-test equivalence certification",
        "human": {
            "informal": "Certify both directions between target membership and realization of the declared test family.",
            "latex": "\\operatorname{Target}(G)\\leftrightarrow\\exists i,w,\\operatorname{Realizes}(i,w)",
            "whyNeeded": "A negative realization decision implies target avoidance only through this certificate.",
            "failureMeaning": "Failure is a design-time repair obligation; no CorePlan exists until certification is supplied.",
            "proofHints": ["Keep both implications explicit in EquivalenceCertificate."],
        },
        "contracts": CONTRACTS_BY_NODE[EQUIV],
        "formalContract": {
            "contractId": f"{EQUIV}.contract",
            "executionMode": "external_certificate",
            "leanContractRef": node_ref(equivalence_ns, "Contract", equivalence_source, "abbrev"),
            "inputs": [
                slot("scopeState", "state", f"{NS}.ScopedState framework input"),
                slot("plan", "algorithm", f"{NS}.Nodes.Equivalence.Plan framework input"),
            ],
            "outputs": [slot("equivalence", "certificate", f"{NS}.EquivalenceState framework input")],
            "dischargeCondition": "The plan constructs an EquivalenceState before realization is inspected.",
        },
        "leanImplementation": implementation(
            equivalence_ns, equivalence_source,
            [("contract", "Contract", "abbrev", ""), ("plan", "Plan", "structure", ""), ("implementation", "run", "definition", "")],
        ),
        "source": {"document": "branch_closure_methodology_extended.tex", "section": SECTION, "diagramKey": "equivalence"},
    }
    realization = decision_node(
        REALIZATION, "Realization decision", "Realization",
        [
            slot("equivalence", "state", f"{NS}.EquivalenceState framework input"),
            slot("plan", "algorithm", f"{NS}.Nodes.Realization.Plan framework input"),
        ],
        f"{NS}.Nodes.Realization.Contract framework input equivalence",
        "Return either a C1 certificate or a complete target-avoiding state.",
    )
    payload = decision_node(
        PAYLOAD, "Payload classification", "Payload",
        [
            slot("avoiding", "state", f"{NS}.AvoidingState framework input"),
            slot("plan", "algorithm", f"{NS}.Nodes.Payload.Plan framework input"),
        ],
        f"{NS}.Nodes.Payload.Contract framework input avoiding",
        "Classify one target-avoiding state into exactly one of the six typed consumer payloads.",
    )
    terminals = [
        terminal_node(
            SCOPE_TERM, "scope", "scope", "scopeTerminal", "scope",
            [slot("candidate", "state", f"{NS}.ScopeCandidate framework input")],
            f"¬ {NS}.ScopeReadyAt framework input",
        ),
        terminal_node(
            C1_TERM, "c1", "c1", "c1Terminal", "c1",
            [slot("certificate", "certificate", f"{NS}.C1Certificate framework input")],
            "framework.ct2.Target input.G",
        ),
    ]
    for consumer, node_id in ROUTE_TERMINALS.items():
        upper = consumer.upper()
        terminals.append(
            terminal_node(
                node_id, consumer, consumer, f"{consumer}Terminal", consumer,
                [
                    slot("avoiding", "state", f"{NS}.AvoidingState framework input"),
                    slot("payload", "payload", f"{NS}.{upper}Payload framework input avoiding"),
                ],
                f"port.accepts (.{consumer} payload)",
            )
        )
    return [entry, scope, terminals[0], equivalence, realization, terminals[1], payload, *terminals[2:]]


def api_ref(name: str, source: str, kind: str, module: str = NS) -> dict:
    return ref(f"{module}.{name}", source, kind, module)


def build_tactic(nodes: list[dict]) -> dict:
    types = "StructuralExhaustion/CT1/Types.lean"
    graph = "StructuralExhaustion/CT1/Graph.lean"
    execution = "StructuralExhaustion/CT1/Execution.lean"
    theorems = "StructuralExhaustion/CT1/Theorems.lean"
    formal_api = {
        "framework": api_ref("Framework", types, "structure"),
        "input": api_ref("Input", types, "structure"),
        "testRealization": api_ref("TestRealization", types, "structure"),
        "scopeReadyAt": api_ref("ScopeReadyAt", types, "definition"),
        "scopedState": api_ref("ScopedState", types, "structure"),
        "equivalenceCertificate": api_ref("EquivalenceCertificate", types, "structure"),
        "equivalenceState": api_ref("EquivalenceState", types, "structure"),
        "avoidingState": api_ref("AvoidingState", types, "structure"),
        "c1Certificate": api_ref("C1Certificate", types, "structure"),
        "ct2Payload": api_ref("CT2Payload", types, "structure"),
        "ct2Adapter": api_ref("toInput", types, "definition", f"{NS}.CT2Payload"),
        "ct3Adapter": api_ref("toInput", types, "definition", f"{NS}.CT3Payload"),
        "ct4Adapter": api_ref("toInput", types, "definition", f"{NS}.CT4Payload"),
        "ct5Adapter": api_ref("toInput", types, "definition", f"{NS}.CT5Payload"),
        "handoffPayload": api_ref("HandoffPayload", types, "inductive"),
        "port": api_ref("Port", types, "structure"),
        "handoffPlan": api_ref("HandoffPlan", types, "structure"),
        "nodeId": api_ref("NodeId", graph, "inductive", f"{NS}.Graph"),
        "terminal": api_ref("Terminal", graph, "inductive", f"{NS}.Graph"),
        "edge": api_ref("Edge", graph, "inductive", f"{NS}.Graph"),
        "path": api_ref("Path", graph, "inductive", f"{NS}.Graph"),
        "validTrace": api_ref("ValidTrace", graph, "definition", f"{NS}.Graph"),
        "corePlan": api_ref("CorePlan", execution, "structure"),
        "rawOutcome": api_ref("RawOutcome", execution, "inductive"),
        "coreResult": api_ref("CoreResult", execution, "structure"),
        "runCore": api_ref("runCore", execution, "definition"),
        "outcome": api_ref("Outcome", execution, "inductive"),
        "outcomeClaim": api_ref("OutcomeClaim", execution, "definition"),
        "executionResult": api_ref("ExecutionResult", execution, "structure"),
        "run": api_ref("run", execution, "definition"),
        "runTraced": api_ref("runTraced", execution, "definition"),
        "soundness": api_ref("run_verified", theorems, "theorem"),
        "totality": api_ref("run_total", theorems, "theorem"),
        "traceValidity": api_ref("run_trace_valid", theorems, "theorem"),
        "c1Coverage": api_ref("c1_terminal_covered", theorems, "theorem"),
        "c1Closure": api_ref("c1_terminal_closes", theorems, "theorem"),
        "adapterAmbient": api_ref("ct2_payload_same_ambient", theorems, "theorem"),
        "ct3Alignment": api_ref("ct3_payload_aligned", theorems, "theorem"),
        "ct4Alignment": api_ref("ct4_payload_aligned", theorems, "theorem"),
        "ct5Alignment": api_ref("ct5_payload_aligned", theorems, "theorem"),
    }
    instances = {
        "scope": "instances/ct1/toy-scope.json",
        "c1": "instances/ct1/toy-c1.json",
        **{consumer: f"instances/ct1/toy-route-{consumer}.json" for consumer in ROUTE_TERMINALS},
    }
    return {
        "artifactType": "formalTacticSpec",
        "schemaVersion": "2.0.0",
        "graphVersion": VERSION,
        "tacticId": "CT1",
        "name": "Target-test alignment and first closure",
        "signature": {
            "input": "validated_branch_state",
            "close": ["C1"],
            "handoff": ["P_1_to_2", "P_1_to_3", "P_1_to_4", "P_1_to_5", "P_1_to_6", "P_1_to_17"],
            "scope": ["target_test_scope_unavailable"],
        },
        "entryNodeId": ENTRY,
        "nodeRefs": [f"nodes/{node['nodeId']}.json" for node in nodes],
        "transitions": TRANSITIONS,
        "terminalCases": ["scope", "c1", *ROUTE_TERMINALS],
        "terminalCoverage": [
            {"terminalCase": case, "mode": "executable_instance", "instanceRef": path}
            for case, path in instances.items()
        ],
        "formalApi": formal_api,
        "totalityPolicy": {
            "allNodesBound": True,
            "allTransitionsDeclared": True,
            "allDecisionBranchesMapped": True,
            "allTracesKernelCertified": True,
            "allTerminalOutcomesTyped": True,
            "allConsumerTriggersCarried": True,
        },
        "source": {"document": "branch_closure_methodology_extended.tex", "section": SECTION},
        "contractInventoryRef": "contracts.json",
    }


def build_contracts() -> dict:
    types = "StructuralExhaustion/CT1/Types.lean"
    graph = "StructuralExhaustion/CT1/Graph.lean"
    theorems = "StructuralExhaustion/CT1/Theorems.lean"
    records = [
        ("S-Def", [ENTRY], "Framework contains static target-test vocabulary; Input contains only runtime data.", [api_ref("Framework", types, "structure"), api_ref("Input", types, "structure")]),
        ("S-Dich", [SCOPE, REALIZATION, PAYLOAD], "Each decision constructor corresponds to one and only one outgoing typed edge.", [api_ref("Edge", graph, "inductive", f"{NS}.Graph"), api_ref("Decision", "StructuralExhaustion/CT1/Nodes/Scope.lean", "inductive", f"{NS}.Nodes.Scope"), api_ref("Decision", "StructuralExhaustion/CT1/Nodes/Realization.lean", "inductive", f"{NS}.Nodes.Realization"), api_ref("Decision", "StructuralExhaustion/CT1/Nodes/Payload.lean", "inductive", f"{NS}.Nodes.Payload")]),
        ("S-Equiv", [EQUIV, REALIZATION, C1_TERM], "The target-test equivalence is certified before realization is decided.", [api_ref("EquivalenceCertificate", types, "structure"), api_ref("EquivalenceState", types, "structure"), api_ref("AvoidingState", types, "structure")]),
        ("S-Pers", [REALIZATION, PAYLOAD, *ROUTE_TERMINALS.values()], "Every negative branch and routed payload retains the same target-avoiding predecessor state.", [api_ref("AvoidingState", types, "structure"), api_ref("HandoffPayload", types, "inductive")]),
        ("S-Rout", [PAYLOAD, *ROUTE_TERMINALS.values()], "One six-constructor classifier emits exactly one indexed downstream payload.", [api_ref("HandoffPayload", types, "inductive"), api_ref("Outcome", "StructuralExhaustion/CT1/Execution.lean", "inductive")]),
        ("S-Trig", list(ROUTE_TERMINALS.values()), "HandoffPlan certifies consumer acceptance without altering the mathematical core result.", [api_ref("Port", types, "structure"), api_ref("HandoffPlan", types, "structure")]),
        ("A-Cert", [C1_TERM], "A realized test and the forward equivalence implication yield the exact target proposition.", [api_ref("C1Certificate", types, "structure"), api_ref("c1_terminal_closes", theorems, "theorem")]),
        ("A-Scope", [SCOPE, SCOPE_TERM], "A failed scope admission carries a proof that ScopeReadyAt is false.", [api_ref("ScopeReadyAt", types, "definition"), api_ref("ScopeCandidate", types, "structure")]),
    ]
    return {
        "artifactType": "tacticContractInventory",
        "schemaVersion": "2.0.0",
        "graphVersion": VERSION,
        "tacticId": "CT1",
        "contracts": [
            {
                "contractInstanceId": f"CT1.{schema}.1",
                "contractSchema": schema,
                "statement": {"informal": statement, "latex": ""},
                "nodeIds": node_ids,
                "leanEvidence": evidence,
                "dischargePolicy": "The generic validator checks membership and declarations; Lean checks the indexed contract and every constructor.",
            }
            for schema, node_ids, statement, evidence in records
        ],
    }


def build_formalization(tactic: dict, nodes: list[dict]) -> dict:
    return {
        "artifactType": "tacticFormalizationIndex",
        "schemaVersion": "2.0.0",
        "graphVersion": VERSION,
        "tacticId": "CT1",
        "toolchain": "leanprover/lean4:v4.31.0",
        "rootModule": "StructuralExhaustion",
        "nodeBindings": [
            {
                "nodeId": node["nodeId"],
                "nodeSpecRef": node_ref_path,
                "contractDeclaration": node["formalContract"]["leanContractRef"]["declaration"],
                "requiredDeclarations": [item["ref"]["declaration"] for item in node["leanImplementation"]["declarations"]],
            }
            for node_ref_path, node in zip(tactic["nodeRefs"], nodes)
        ],
        "aggregateDeclarations": {name: declaration["declaration"] for name, declaration in tactic["formalApi"].items()},
        "generatedBindingCheck": "StructuralExhaustion/Generated/BindingCheck.lean",
    }


def lean_example_ref(name: str, kind: str = "definition") -> dict:
    return ref(
        f"StructuralExhaustion.Examples.CT1Toy.{name}",
        "StructuralExhaustion/Examples/CT1Toy.lean",
        kind,
        "StructuralExhaustion.Examples.CT1Toy",
    )


def build_instance(case: str) -> dict:
    if case == "scope":
        stem, framework, input_name, plan, port, handoff = "toy-scope", "scopeFramework", "scopeInput", "scopePlan", "scopePort", "scopeHandoff"
        result, terminal_theorem, trace_theorem = "scopeResult", "scope_terminal", "scope_trace"
        node_path = [ENTRY, SCOPE, SCOPE_TERM]
        edge_path = ["CT1.edge.begin", "CT1.edge.scope.exit"]
    elif case == "c1":
        stem, framework, input_name, plan, port, handoff = "toy-c1", "hitFramework", "hitInput", "hitPlan", "hitPort", "hitHandoff"
        result, terminal_theorem, trace_theorem = "hitResult", "hit_terminal", "hit_trace"
        node_path = [ENTRY, SCOPE, EQUIV, REALIZATION, C1_TERM]
        edge_path = ["CT1.edge.begin", "CT1.edge.scope.ready", "CT1.edge.equivalence.certified", "CT1.edge.realization.hit"]
    else:
        stem, framework, input_name, plan, port, handoff = f"toy-route-{case}", "routingFramework", "routingInput", f"{case}Plan", "routingPort", "routingHandoff"
        result, terminal_theorem, trace_theorem = f"{case}Result", f"{case}_terminal", f"{case}_trace"
        node_path = [ENTRY, SCOPE, EQUIV, REALIZATION, PAYLOAD, ROUTE_TERMINALS[case]]
        edge_path = ["CT1.edge.begin", "CT1.edge.scope.ready", "CT1.edge.equivalence.certified", "CT1.edge.realization.avoiding", f"CT1.edge.payload.{case}"]
    return {
        "artifactType": "tacticInstantiation",
        "schemaVersion": "2.0.0",
        "graphVersion": VERSION,
        "instanceId": stem,
        "tacticId": "CT1",
        "bindings": [
            {"slotId": "framework", "leanRef": lean_example_ref(framework)},
            {"slotId": "input", "leanRef": lean_example_ref(input_name)},
            {"slotId": "corePlan", "leanRef": lean_example_ref(plan)},
            {"slotId": "port", "leanRef": lean_example_ref(port)},
            {"slotId": "handoffPlan", "leanRef": lean_example_ref(handoff)},
        ],
        "expectedTerminalCase": case,
        "expectedNodePath": node_path,
        "expectedEdgePath": edge_path,
        "executionResultRef": lean_example_ref(result),
        "terminalTheoremRef": lean_example_ref(terminal_theorem, "theorem"),
        "traceTheoremRef": lean_example_ref(trace_theorem, "theorem"),
    }


def main() -> int:
    nodes = build_nodes()
    tactic = build_tactic(nodes)
    write(TACTIC_ROOT / "tactic.json", tactic)
    write(TACTIC_ROOT / "contracts.json", build_contracts())
    write(TACTIC_ROOT / "formalization.json", build_formalization(tactic, nodes))
    for node in nodes:
        write(NODE_ROOT / f"{node['nodeId']}.json", node)
        write(
            SCHEMA_ROOT / f"{node['nodeId']}.schema.json",
            {
                "$schema": "https://json-schema.org/draft/2020-12/schema",
                "$id": f"https://example.org/structural-exhaustion/ct1/nodes/{node['nodeId']}.schema.json",
                "allOf": [
                    {"$ref": "../../formalization.bundle.schema.json#/$defs/formalNodeSpec"},
                    {
                        "properties": {
                            "nodeId": {"const": node["nodeId"]},
                            "nodeKind": {"const": node["nodeKind"]},
                        },
                        "required": ["nodeId", "nodeKind"],
                    },
                ],
            },
        )
    for case in ["scope", "c1", *ROUTE_TERMINALS]:
        instance = build_instance(case)
        write(INSTANCE_ROOT / f"{instance['instanceId']}.json", instance)
    print(f"Wrote CT1-v1: {len(nodes)} nodes, {len(TRANSITIONS)} edges, 8 instances")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
