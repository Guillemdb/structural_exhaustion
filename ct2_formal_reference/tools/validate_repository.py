#!/usr/bin/env python3
"""Validate every semantic tactic graph and its Lean binding contract."""
from __future__ import annotations

import hashlib
import json
import re
from collections import defaultdict, deque
from pathlib import Path

from jsonschema import Draft202012Validator

try:
    from tools.generate_binding_check import (
        load_graph,
        render_cytoscape,
        render_node_index,
        tactic_instances,
    )
except ModuleNotFoundError:
    from generate_binding_check import (
        load_graph,
        render_cytoscape,
        render_node_index,
        tactic_instances,
    )

ROOT = Path(__file__).resolve().parents[1]


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def schema_validator(bundle: dict, definition: str) -> Draft202012Validator:
    return Draft202012Validator({
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$defs": bundle["$defs"],
        "$ref": f"#/$defs/{definition}",
    })


def schema_errors(errors: list[str], validator: Draft202012Validator, value: dict, label: str) -> None:
    for error in sorted(validator.iter_errors(value), key=lambda item: list(item.path)):
        location = ".".join(str(part) for part in error.path)
        suffix = f" at {location}" if location else ""
        errors.append(f"{label}: schema error{suffix}: {error.message}")


DECLARATION_PATTERN = re.compile(
    r"\b(?:def|abbrev|theorem|structure|inductive|class)\s+([A-Za-z_][A-Za-z0-9_]*)\b"
)
CONSTRUCTOR_PATTERN = re.compile(r"(?m)^\s*\|\s*([A-Za-z_][A-Za-z0-9_]*)\b")


def local_declarations(source: str) -> set[str]:
    return set(DECLARATION_PATTERN.findall(source)) | set(CONSTRUCTOR_PATTERN.findall(source))


def validate_ref(errors: list[str], declaration_ref: dict, label: str, check_module: str) -> None:
    source_path = ROOT / declaration_ref["sourceFile"]
    if not source_path.is_file():
        errors.append(f"{label}: missing Lean source {declaration_ref['sourceFile']}")
        return
    local_name = declaration_ref["declaration"].split(".")[-1]
    if local_name not in local_declarations(source_path.read_text(encoding="utf-8")):
        errors.append(f"{label}: {local_name} not declared in {declaration_ref['sourceFile']}")
    if f"#check {declaration_ref['declaration']}" not in check_module:
        errors.append(f"{label}: binding check missing for {declaration_ref['declaration']}")


def validate_tactic(
    errors: list[str],
    bundle: dict,
    validators: dict[str, Draft202012Validator],
    manifest: dict,
    record: dict,
    check_module: str,
) -> tuple[int, int, int, int]:
    tactic_id = record["tacticId"]
    tactic_path = ROOT / record["specRef"]
    tactic_root = tactic_path.parent
    tactic, nodes = load_graph(ROOT, tactic_id)
    inventory = load(ROOT / record["contractInventoryRef"])
    formalization = load(ROOT / record["formalizationRef"])
    verification_path = ROOT / f"generated/{tactic_id.lower()}-lean-verification.json"
    verification = load(verification_path) if verification_path.exists() else None
    instances = {str(path.relative_to(ROOT)): value for path, value in tactic_instances(ROOT, tactic_id)}

    schema_errors(errors, validators["formalTacticSpec"], tactic, str(tactic_path.relative_to(ROOT)))
    for node_ref, node in zip(tactic["nodeRefs"], nodes):
        schema_errors(errors, validators["formalNodeSpec"], node, str((tactic_root / node_ref).relative_to(ROOT)))
    for label, instance in instances.items():
        schema_errors(errors, validators["tacticInstantiation"], instance, label)
    schema_errors(errors, validators["tacticContractInventory"], inventory, record["contractInventoryRef"])
    schema_errors(errors, validators["tacticFormalizationIndex"], formalization, record["formalizationRef"])
    if verification is None:
        errors.append(f"missing {verification_path.relative_to(ROOT)}")
    else:
        schema_errors(errors, validators["leanVerificationResult"], verification, str(verification_path.relative_to(ROOT)))

    version = tactic["graphVersion"]
    if not version.startswith(f"{tactic_id}-v"):
        errors.append(f"{tactic_id}: graphVersion must be owned by the tactic")
    for label, artifact in [
        (record["contractInventoryRef"], inventory),
        (record["formalizationRef"], formalization),
        *instances.items(),
    ]:
        if artifact.get("tacticId") != tactic_id or artifact.get("graphVersion") != version:
            errors.append(f"{label}: tacticId or graphVersion differs from tactic.json")
    if verification and (
        verification.get("tacticId") != tactic_id or verification.get("graphVersion") != version
    ):
        errors.append(f"{verification_path.relative_to(ROOT)}: tacticId or graphVersion differs from tactic.json")

    node_ids = [node["nodeId"] for node in nodes]
    idset = set(node_ids)
    if len(node_ids) != len(idset):
        errors.append(f"{tactic_id}: duplicate node IDs")
    if any(not node_id.startswith(f"{tactic_id}.") for node_id in node_ids):
        errors.append(f"{tactic_id}: node ID owned by another tactic")
    disk_refs = {f"nodes/{path.name}" for path in (ROOT / record["nodeDirectory"]).glob("*.json")}
    if disk_refs != set(tactic["nodeRefs"]):
        errors.append(f"{tactic_id}: nodeRefs must name every and only node file")
    for node_ref_path, node in zip(tactic["nodeRefs"], nodes):
        node_id = node["nodeId"]
        if Path(node_ref_path).name != f"{node_id}.json":
            errors.append(f"{node_id}: node filename is not its semantic ID")
        if node["formalContract"]["contractId"] != f"{node_id}.contract":
            errors.append(f"{node_id}: contractId is not derived from nodeId")
        concrete = ROOT / f"schemas/concrete/nodes/{node_id}.schema.json"
        if not concrete.is_file():
            errors.append(f"{node_id}: missing concrete node schema")

    entries = [node for node in nodes if node["nodeKind"] == "entry"]
    if len(entries) != 1 or entries[0]["nodeId"] != tactic["entryNodeId"]:
        errors.append(f"{tactic_id}: graph must have one declared entry")

    transitions = tactic["transitions"]
    edge_ids = [edge["transitionId"] for edge in transitions]
    if len(edge_ids) != len(set(edge_ids)):
        errors.append(f"{tactic_id}: duplicate transition IDs")
    edge_by_id = {edge["transitionId"]: edge for edge in transitions}
    outgoing: dict[str, list[dict]] = defaultdict(list)
    incoming: dict[str, list[dict]] = defaultdict(list)
    for edge in transitions:
        source, target = edge["fromNodeId"], edge["toNodeId"]
        if source not in idset or target not in idset:
            errors.append(f"{edge['transitionId']}: unknown endpoint {source} -> {target}")
            continue
        if source == target:
            errors.append(f"{edge['transitionId']}: self transitions are forbidden")
        outgoing[source].append(edge)
        incoming[target].append(edge)

    node_by_id = {node["nodeId"]: node for node in nodes}
    for node in nodes:
        node_id, kind = node["nodeId"], node["nodeKind"]
        if kind == "terminal" and outgoing[node_id]:
            errors.append(f"{node_id}: terminal has outgoing transitions")
        if kind != "terminal" and not outgoing[node_id]:
            errors.append(f"{node_id}: nonterminal has no outgoing transition")
        if node_id == tactic["entryNodeId"]:
            if incoming[node_id] or len(outgoing[node_id]) != 1 or outgoing[node_id][0]["guard"]["kind"] != "unconditional":
                errors.append(f"{node_id}: entry boundary is malformed")
        elif not incoming[node_id]:
            errors.append(f"{node_id}: non-entry has no predecessor")
        if kind == "certification":
            if len(outgoing[node_id]) != 1 or outgoing[node_id][0]["guard"]["kind"] != "unconditional":
                errors.append(f"{node_id}: certification must have one evidence-carrying advance")
            elif not outgoing[node_id][0]["guard"]["evidenceSlots"]:
                errors.append(f"{node_id}: certification edge does not carry its certified state")
        if kind == "decision":
            branches = node["formalContract"].get("branches", [])
            if {branch["transitionId"] for branch in branches} != {edge["transitionId"] for edge in outgoing[node_id]}:
                errors.append(f"{node_id}: branches differ from outgoing transitions")
            if len({branch["branchTag"] for branch in branches}) != len(branches):
                errors.append(f"{node_id}: duplicate branch tags")
            for branch in branches:
                edge = edge_by_id.get(branch["transitionId"])
                if edge is None:
                    continue
                guard = edge["guard"]
                for field in ("branchTag", "resultConstructorRef", "evidenceSlots"):
                    if guard.get(field) != branch.get(field):
                        errors.append(f"{edge['transitionId']}: guard {field} differs from node branch")

    reachable: set[str] = set()
    queue = deque([tactic["entryNodeId"]] if tactic["entryNodeId"] in idset else [])
    while queue:
        node_id = queue.popleft()
        if node_id in reachable:
            continue
        reachable.add(node_id)
        queue.extend(edge["toNodeId"] for edge in outgoing[node_id])
    if reachable != idset:
        errors.append(f"{tactic_id}: unreachable nodes {sorted(idset - reachable)}")
    indegree = {node_id: len(incoming[node_id]) for node_id in idset}
    dag_queue = deque(node_id for node_id, degree in indegree.items() if degree == 0)
    visited = 0
    while dag_queue:
        node_id = dag_queue.popleft()
        visited += 1
        for edge in outgoing[node_id]:
            indegree[edge["toNodeId"]] -= 1
            if indegree[edge["toNodeId"]] == 0:
                dag_queue.append(edge["toNodeId"])
    has_cycle = visited != len(idset)
    if tactic_id == "CT12":
        loop_edges = [
            edge for edge in transitions
            if edge["transitionId"] == "CT12.edge.decrease.loop"
        ]
        if not has_cycle:
            errors.append("CT12: peeling graph must contain its certified back edge")
        if len(loop_edges) != 1:
            errors.append("CT12: expected exactly one named decrease back edge")
        else:
            loop_edge = loop_edges[0]
            if (
                loop_edge["fromNodeId"] != "CT12.certify.decrease"
                or loop_edge["toNodeId"] != "CT12.decide.saturation"
                or not any(
                    "DecreasedState" in item["typeExpression"]
                    for item in loop_edge["guard"]["evidenceSlots"]
                )
            ):
                errors.append("CT12: back edge is not licensed by DecreasedState")
        acyclic_edges = [
            edge for edge in transitions
            if edge["transitionId"] != "CT12.edge.decrease.loop"
        ]
        acyclic_indegree = {node_id: 0 for node_id in idset}
        acyclic_outgoing: dict[str, list[str]] = defaultdict(list)
        for edge in acyclic_edges:
            acyclic_indegree[edge["toNodeId"]] += 1
            acyclic_outgoing[edge["fromNodeId"]].append(edge["toNodeId"])
        acyclic_queue = deque(
            node_id for node_id, degree in acyclic_indegree.items() if degree == 0
        )
        acyclic_visited = 0
        while acyclic_queue:
            node_id = acyclic_queue.popleft()
            acyclic_visited += 1
            for target in acyclic_outgoing[node_id]:
                acyclic_indegree[target] -= 1
                if acyclic_indegree[target] == 0:
                    acyclic_queue.append(target)
        if acyclic_visited != len(idset):
            errors.append("CT12: removing the certified back edge must make the graph acyclic")
        decrease_ref = tactic["formalApi"].get("loopDecrease", {}).get("declaration")
        if decrease_ref != "StructuralExhaustion.CT12.Graph.Edge.loop_decreases":
            errors.append("CT12: formal API must expose the back-edge decrease theorem")
    elif has_cycle:
        errors.append(f"{tactic_id}: semantic graph contains an unauthorized cycle")

    terminals = [node for node in nodes if node["nodeKind"] == "terminal"]
    terminal_by_case = {node["terminal"]["terminalCase"]: node for node in terminals}
    if len(terminal_by_case) != len(terminals) or set(terminal_by_case) != set(tactic["terminalCases"]):
        errors.append(f"{tactic_id}: terminalCases and terminal nodes differ")
    for edge in transitions:
        target = node_by_id.get(edge["toNodeId"])
        if target and target["nodeKind"] == "terminal":
            case = target["terminal"]["terminalCase"]
            closes = len(case) > 1 and case[0] == "c" and case[1].isdigit()
            expected = "scope" if case == "scope" else "close" if closes else "handoff"
        else:
            expected = "advance"
        if edge["kind"] != expected:
            errors.append(f"{edge['transitionId']}: kind must be {expected}")

    refs_to_check: list[tuple[str, dict]] = []
    for node in nodes:
        declared_roles = {item["role"] for item in node["leanImplementation"]["declarations"]}
        missing_roles = set(node["leanImplementation"]["requiredRoles"]) - declared_roles
        if missing_roles:
            errors.append(f"{node['nodeId']}: missing roles {sorted(missing_roles)}")
        refs_to_check.extend((node["nodeId"], item["ref"]) for item in node["leanImplementation"]["declarations"])
        if terminal := node.get("terminal"):
            refs_to_check.extend([
                (node["nodeId"], terminal["terminalConstructorRef"]),
                (node["nodeId"], terminal["outcomeConstructorRef"]),
            ])
    refs_to_check.extend((edge["transitionId"], edge["transitionConstructorRef"]) for edge in transitions)
    refs_to_check.extend((f"{tactic_id}.formalApi.{name}", declaration_ref) for name, declaration_ref in tactic["formalApi"].items())

    coverage = tactic["terminalCoverage"]
    if len({item["terminalCase"] for item in coverage}) != len(coverage) or {item["terminalCase"] for item in coverage} != set(terminal_by_case):
        errors.append(f"{tactic_id}: terminal coverage is not exact")
    for item in coverage:
        label = f"{tactic_id}.coverage.{item['terminalCase']}"
        if item["mode"] == "parametric_theorem":
            refs_to_check.append((label, item["theoremRef"]))
        elif item["instanceRef"] not in instances:
            errors.append(f"{label}: missing instance {item['instanceRef']}")
        elif instances[item["instanceRef"]]["expectedTerminalCase"] != item["terminalCase"]:
            errors.append(f"{label}: instance reaches another terminal")

    membership: dict[str, set[str]] = defaultdict(set)
    contract_names: set[str] = set()
    for contract in inventory["contracts"]:
        contract_names.add(contract["contractSchema"])
        for node_id in contract["nodeIds"]:
            if node_id not in idset:
                errors.append(f"{contract['contractInstanceId']}: unknown node {node_id}")
            membership[node_id].add(contract["contractSchema"])
        refs_to_check.extend((contract["contractInstanceId"], item) for item in contract["leanEvidence"])
    if contract_names != {contract for node in nodes for contract in node["contracts"]}:
        errors.append(f"{tactic_id}: inventory and nodes use different contract families")
    for node in nodes:
        if set(node["contracts"]) != membership[node["nodeId"]]:
            errors.append(f"{node['nodeId']}: contract inventory membership differs")

    for label, declaration_ref in refs_to_check:
        validate_ref(errors, declaration_ref, label, check_module)

    bindings = formalization["nodeBindings"]
    if [item["nodeId"] for item in bindings] != node_ids:
        errors.append(f"{tactic_id}: formalization node order differs")
    for formal_binding, node_ref_path, node in zip(bindings, tactic["nodeRefs"], nodes):
        expected_required = {item["ref"]["declaration"] for item in node["leanImplementation"]["declarations"]}
        if formal_binding["nodeSpecRef"] != node_ref_path:
            errors.append(f"{node['nodeId']}: formalization nodeSpecRef differs")
        if formal_binding["contractDeclaration"] != node["formalContract"]["leanContractRef"]["declaration"]:
            errors.append(f"{node['nodeId']}: formalization contract differs")
        if set(formal_binding["requiredDeclarations"]) != expected_required:
            errors.append(f"{node['nodeId']}: formalization declarations differ")
    expected_aggregates = {name: item["declaration"] for name, item in tactic["formalApi"].items()}
    if formalization["aggregateDeclarations"] != expected_aggregates:
        errors.append(f"{tactic_id}: aggregate declaration index differs")
    if formalization["generatedBindingCheck"] != manifest["leanProject"]["bindingCheckRef"]:
        errors.append(f"{tactic_id}: formalization points to another binding module")

    for label, instance in instances.items():
        slots = [item["slotId"] for item in instance["bindings"]]
        expected_slots = ["framework", "input", "corePlan", "port", "handoffPlan"]
        if sorted(slots) != sorted(expected_slots) or len(slots) != len(set(slots)):
            errors.append(f"{label}: invocation slots are not exact")
        for item in instance["bindings"]:
            validate_ref(errors, item["leanRef"], label, check_module)
        for field in ("executionResultRef", "terminalTheoremRef", "traceTheoremRef"):
            validate_ref(errors, instance[field], f"{label}.{field}", check_module)
        node_path, edge_path = instance["expectedNodePath"], instance["expectedEdgePath"]
        if len(node_path) != len(edge_path) + 1 or node_path[0] != tactic["entryNodeId"]:
            errors.append(f"{label}: malformed entry path")
            continue
        for source, edge_id, target in zip(node_path, edge_path, node_path[1:]):
            edge = edge_by_id.get(edge_id)
            if edge is None or (edge["fromNodeId"], edge["toNodeId"]) != (source, target):
                errors.append(f"{label}: {edge_id} does not justify {source} -> {target}")
        terminal = terminal_by_case.get(instance["expectedTerminalCase"])
        if terminal is None or node_path[-1] != terminal["nodeId"]:
            errors.append(f"{label}: path ends at another terminal")

    stem = tactic_id.lower()
    index_path = ROOT / f"generated/{stem}-node-index.csv"
    graph_path = ROOT / f"generated/{stem}.cytoscape.json"
    if index_path.read_text(encoding="utf-8") != render_node_index(ROOT, tactic_id):
        errors.append(f"{index_path.relative_to(ROOT)} is stale")
    if graph_path.read_text(encoding="utf-8") != render_cytoscape(ROOT, tactic_id):
        errors.append(f"{graph_path.relative_to(ROOT)} is stale")

    if verification and verification.get("status") == "kernel_checked":
        pinned = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
        if verification["toolchain"]["leanToolchain"] != pinned:
            errors.append(f"{verification_path.relative_to(ROOT)}: toolchain pin is stale")
        if verification["toolchain"]["lakefileHash"] != sha(ROOT / "lakefile.toml"):
            errors.append(f"{verification_path.relative_to(ROOT)}: lakefile hash is stale")
        if verification.get("diagnostics"):
            errors.append(f"{verification_path.relative_to(ROOT)}: successful result has diagnostics")
        if any(status != "passed" for status in verification["aggregateResults"].values()):
            errors.append(f"{verification_path.relative_to(ROOT)}: aggregate check failed")
        verification_nodes = {item["nodeId"]: item for item in verification["nodeResults"]}
        if set(verification_nodes) != idset:
            errors.append(f"{verification_path.relative_to(ROOT)}: node set is stale")
        for node in nodes:
            result = verification_nodes.get(node["nodeId"])
            if not result or result["status"] != "kernel_checked":
                errors.append(f"{verification_path.relative_to(ROOT)}: {node['nodeId']} not checked")
                continue
            declarations = {item["declaration"]: item for item in result["declarations"]}
            for item in node["leanImplementation"]["declarations"]:
                declaration_ref = item["ref"]
                result_decl = declarations.get(declaration_ref["declaration"])
                if not result_decl or result_decl.get("sourceHash") != sha(ROOT / declaration_ref["sourceFile"]):
                    errors.append(f"{verification_path.relative_to(ROOT)}: stale {declaration_ref['declaration']}")
                elif result_decl["status"] != "kernel_checked" or not result_decl.get("actualType"):
                    errors.append(f"{verification_path.relative_to(ROOT)}: unresolved {declaration_ref['declaration']}")

    return len(nodes), len(transitions), len(terminals), len(instances)


def main() -> int:
    errors: list[str] = []
    bundle_path = ROOT / "schemas/formalization.bundle.schema.json"
    bundle = load(bundle_path)
    try:
        Draft202012Validator.check_schema(bundle)
    except Exception as error:
        errors.append(f"{bundle_path.relative_to(ROOT)} is not a valid schema: {error}")
    validators = {
        name: schema_validator(bundle, name)
        for name in (
            "formalNodeSpec", "formalTacticSpec", "tacticInstantiation",
            "leanVerificationResult", "tacticFormalizationIndex",
            "tacticContractInventory", "formalProofRepositoryManifest",
        )
    }
    manifest = load(ROOT / "manifest.json")
    schema_errors(errors, validators["formalProofRepositoryManifest"], manifest, "manifest.json")
    tactic_ids = [record["tacticId"] for record in manifest["tactics"]]
    expected_tactics = [f"CT{number}" for number in range(1, 18)]
    if tactic_ids != expected_tactics or len(tactic_ids) != len(set(tactic_ids)):
        errors.append("manifest tactics must be the ordered, unique sequence CT1 through CT17")
    for relative in manifest["schemas"] + manifest["instances"] + manifest["generatedArtifacts"]:
        if not (ROOT / relative).exists():
            errors.append(f"manifest references missing file {relative}")
    check_path = ROOT / manifest["leanProject"]["bindingCheckRef"]
    check_module = check_path.read_text(encoding="utf-8") if check_path.exists() else ""
    if not check_path.exists():
        errors.append(f"missing binding check {check_path.relative_to(ROOT)}")

    totals = [0, 0, 0, 0]
    for record in manifest["tactics"]:
        counts = validate_tactic(errors, bundle, validators, manifest, record, check_module)
        totals = [left + right for left, right in zip(totals, counts)]

    listed_instances = set(manifest["instances"])
    discovered_instances = {
        str(path.relative_to(ROOT))
        for path in (ROOT / "instances").rglob("*.json")
    }
    if listed_instances != discovered_instances:
        errors.append("manifest.instances must list every and only instance JSON")

    admission = re.compile(r"\b(?:sorry|admit|axiom)\b")
    for path in sorted((ROOT / "StructuralExhaustion").rglob("*.lean")):
        source = path.read_text(encoding="utf-8")
        stripped = re.sub(r"/--.*?-/", "", source, flags=re.S)
        stripped = re.sub(r"/-.*?-/", "", stripped, flags=re.S)
        stripped = re.sub(r"--.*", "", stripped)
        if match := admission.search(stripped):
            errors.append(f"{path.relative_to(ROOT)} contains {match.group(0)!r}")

    if errors:
        print("CT1-CT17 repository validation failed:")
        for error in errors:
            print(f"- {error}")
        return 1
    print(
        f"OK: {len(tactic_ids)} tactics, {totals[0]} semantic nodes, {totals[1]} typed transitions, "
        f"{totals[2]} exact terminals, {totals[3]} executable instances"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
