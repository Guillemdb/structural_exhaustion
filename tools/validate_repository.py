#!/usr/bin/env python3
"""Validate the compiled automation-first catalog and all derived contracts."""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict, deque
from pathlib import Path

from jsonschema import Draft202012Validator

try:
    from lint_automation_first import lint as lint_lean_sources
except ImportError:  # imported as tools.validate_repository
    from tools.lint_automation_first import lint as lint_lean_sources


AUTHOR_PROVISIONS = {
    "user_definition",
    "user_operator",
    "user_finite_enumeration",
    "instance_bridge",
    "optimized_implementation",
}
DERIVED_PROVISIONS = {
    "framework_constant",
    "typeclass_inferred",
    "derived_definitionally",
    "derived_from_predecessor",
    "derived_by_generic_search",
    "derived_by_generic_theorem",
    "derived_by_computation",
    "policy_selected",
    "framework_transition",
    "generated_audit",
}
TRANSITION_FRAMEWORK_RESPONSIBILITIES = [
    "exactSourceLedger",
    "semanticDiscovery",
    "targetContextConstruction",
    "triggerConstruction",
    "targetExecution",
    "accumulatedLedgerOutput",
    "transitionProvenance",
]
TRANSITION_EXPECTED_PROBLEM_INPUTS = {
    "CT1.residual.avoiding->CT2": ["targetCapability", "minimalityKernel"],
    "CT1.residual.avoiding->CT2.localDeletion": [
        "targetCapability",
        "minimalityKernel",
    ],
    "CT1.terminal.c1->CT12": [
        "targetCapability",
        "semanticDiscoveryAdapter",
    ],
    "CT2.residual.separatingContext->CT3": [
        "targetCapability",
        "semanticDiscoveryAdapter",
    ],
    "CT2.residual.criticality->CT10": [
        "targetCapability",
        "semanticDiscoveryAdapter",
    ],
    "CT5.residual.chargeLedger->CT14": ["targetCapability"],
    "CT6.residual.activeLedger->CT9": [
        "targetCapability",
        "semanticDiscoveryAdapter",
    ],
    "CT9.residual.overload->CT7": [
        "targetCapability",
        "semanticDiscoveryAdapter",
    ],
    "CT14.residual.capacity->CT14": ["targetCapability"],
}
SUSPICIOUS_CAPABILITY = re.compile(
    r"(?:^|\.)(?:solve|run|execute|outcome|result|claim|certificate|residual)(?:$|[A-Z_.])",
    re.IGNORECASE,
)
RETIRED_CATALOG_TEXT = re.compile(
    r"\bFinitePresentation\b|\buser_finite_presentation\b"
)


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def retired_catalog_references(value: object, location: str = "<root>") -> list[str]:
    """Locate legacy finite-API names in any exported catalog string."""
    if isinstance(value, dict):
        return [
            error
            for key, item in value.items()
            for error in retired_catalog_references(item, f"{location}/{key}")
        ]
    if isinstance(value, list):
        return [
            error
            for index, item in enumerate(value)
            for error in retired_catalog_references(item, f"{location}/{index}")
        ]
    if isinstance(value, str) and RETIRED_CATALOG_TEXT.search(value):
        return [f"{location}: retired custom finite API reference {value!r}"]
    return []


def edge_contract(edge: dict) -> dict:
    return {
        "edgeId": edge["edgeId"],
        "constructor": edge["constructor"],
        "constructorType": edge["constructorType"],
        "sourceNode": edge["sourceNode"],
        "targetNode": edge["targetNode"],
    }


def reachable(entry: str, outgoing: dict[str, list[str]]) -> set[str]:
    seen: set[str] = set()
    queue = deque([entry])
    while queue:
        node = queue.popleft()
        if node in seen:
            continue
        seen.add(node)
        queue.extend(outgoing[node])
    return seen


def graph_has_cycle(nodes: set[str], transitions: list[dict]) -> bool:
    indegree = {node: 0 for node in nodes}
    outgoing: dict[str, list[str]] = defaultdict(list)
    for edge in transitions:
        outgoing[edge["sourceNode"]].append(edge["targetNode"])
        indegree[edge["targetNode"]] += 1
    queue = deque(node for node, degree in indegree.items() if degree == 0)
    visited = 0
    while queue:
        node = queue.popleft()
        visited += 1
        for target in outgoing[node]:
            indegree[target] -= 1
            if indegree[target] == 0:
                queue.append(target)
    return visited != len(nodes)


def refs(values: list[dict]) -> list[str]:
    return [value["ref"] for value in values]


def manifest_covers(reference: str, manifest: set[str]) -> bool:
    if reference in manifest:
        return True
    return any(
        candidate.endswith(f".{reference}")
        or reference.endswith(f".{candidate}")
        for candidate in manifest
    )


def validate_tactic(errors: list[str], tactic: dict) -> None:
    tactic_id = tactic["tacticId"]
    nodes = tactic["nodes"]
    transitions = tactic["transitions"]
    terminals = tactic["terminals"]
    node_ids = [node["nodeId"] for node in nodes]
    node_set = set(node_ids)

    if len(node_ids) != len(node_set):
        errors.append(f"{tactic_id}: duplicate node identifiers")
    if [node["ordinal"] for node in nodes] != list(range(1, len(nodes) + 1)):
        errors.append(f"{tactic_id}: node ordinals differ from constructor order")
    if [edge["ordinal"] for edge in transitions] != list(
        range(1, len(transitions) + 1)
    ):
        errors.append(f"{tactic_id}: edge ordinals differ from constructor order")
    if [terminal["ordinal"] for terminal in terminals] != list(
        range(1, len(terminals) + 1)
    ):
        errors.append(f"{tactic_id}: terminal ordinals differ from constructor order")

    entries = [node["nodeId"] for node in nodes if node["nodeKind"] == "entry"]
    if len(entries) != 1:
        errors.append(f"{tactic_id}: expected exactly one entry node")
        entry = None
    else:
        entry = entries[0]

    outgoing_edges: dict[str, list[dict]] = defaultdict(list)
    incoming_edges: dict[str, list[dict]] = defaultdict(list)
    edge_ids: set[str] = set()
    for edge in transitions:
        edge_id = edge["edgeId"]
        if edge_id in edge_ids:
            errors.append(f"{tactic_id}: duplicate edge {edge_id}")
        edge_ids.add(edge_id)
        if edge["sourceNode"] not in node_set or edge["targetNode"] not in node_set:
            errors.append(f"{edge_id}: endpoint is absent from Graph.NodeId")
            continue
        if edge["provision"] != "generated_audit":
            errors.append(f"{edge_id}: graph edges must be generated audit objects")
        outgoing_edges[edge["sourceNode"]].append(edge)
        incoming_edges[edge["targetNode"]].append(edge)

    terminal_nodes = {terminal["nodeId"] for terminal in terminals}
    if len(terminal_nodes) != len(terminals):
        errors.append(f"{tactic_id}: terminal constructors do not map injectively")
    if not terminal_nodes <= node_set:
        errors.append(f"{tactic_id}: terminal maps outside Graph.NodeId")

    if entry is not None:
        outgoing = {
            node: [edge["targetNode"] for edge in outgoing_edges[node]]
            for node in node_set
        }
        missing = node_set - reachable(entry, outgoing)
        if missing:
            errors.append(f"{tactic_id}: unreachable nodes {sorted(missing)}")
        if incoming_edges[entry]:
            errors.append(f"{tactic_id}: entry node has incoming edges")

    for terminal in terminal_nodes:
        if outgoing_edges[terminal]:
            errors.append(f"{terminal}: terminal node has outgoing edges")

    capability = tactic["capability"]
    if capability["tacticId"] != tactic_id:
        errors.append(f"{tactic_id}: capability tactic identifier disagrees")
    manifest = set(refs(capability["requiredDefinitions"])) | set(
        refs(capability["requiredInstances"])
    )
    for item in capability["requiredDefinitions"]:
        if item["provision"] not in AUTHOR_PROVISIONS:
            errors.append(
                f"{tactic_id}: capability definition {item['ref']} is not author-provided"
            )
        if SUSPICIOUS_CAPABILITY.search(item["ref"]):
            errors.append(
                f"{tactic_id}: capability appears to inject a whole result via {item['ref']}"
            )
    for item in capability["requiredInstances"]:
        if item["provision"] != "typeclass_inferred":
            errors.append(f"{tactic_id}: required instance {item['ref']} has wrong provision")
    if not capability["derivedOperations"]:
        errors.append(f"{tactic_id}: capability lists no framework-derived operations")

    profile_ids: set[str] = set()
    for profile in tactic.get("capabilityProfiles", []):
        profile_id = profile["capabilityId"]
        if profile_id in profile_ids:
            errors.append(f"{tactic_id}: duplicate capability profile {profile_id}")
        profile_ids.add(profile_id)
        if profile["tacticId"] != tactic_id:
            errors.append(f"{tactic_id}: capability profile tactic identifier disagrees")
        for item in profile["requiredDefinitions"]:
            if item["provision"] not in AUTHOR_PROVISIONS:
                errors.append(
                    f"{tactic_id}: profile definition {item['ref']} is not author-provided"
                )
            if SUSPICIOUS_CAPABILITY.search(item["ref"]):
                errors.append(
                    f"{tactic_id}: profile injects a whole result via {item['ref']}"
                )
        if not profile["derivedOperations"]:
            errors.append(f"{tactic_id}: profile {profile_id} has no derived operations")

    capabilities = [capability, *tactic.get("capabilityProfiles", [])]
    requirement_refs = {
        item["ref"]
        for current_capability in capabilities
        for item in current_capability["requiredDefinitions"]
    }
    concepts = tactic.get("capabilityConcepts", [])
    concept_ids = [concept["conceptId"] for concept in concepts]
    concept_refs = [concept["requirementRef"] for concept in concepts]
    declaration_names = [
        concept["formalDeclaration"]["name"] for concept in concepts
    ]
    if len(concept_ids) != len(set(concept_ids)):
        errors.append(f"{tactic_id}: duplicate capability concept identifiers")
    if len(concept_refs) != len(set(concept_refs)):
        errors.append(f"{tactic_id}: duplicate capability concept requirement references")
    if len(declaration_names) != len(set(declaration_names)):
        errors.append(f"{tactic_id}: duplicate capability concept declarations")
    if set(concept_refs) != requirement_refs:
        missing = sorted(requirement_refs - set(concept_refs))
        orphaned = sorted(set(concept_refs) - requirement_refs)
        if missing:
            errors.append(
                f"{tactic_id}: capability concepts omit requirements {missing}"
            )
        if orphaned:
            errors.append(
                f"{tactic_id}: orphaned capability concepts for {orphaned}"
            )
    concept_id_by_ref = {
        concept["requirementRef"]: concept["conceptId"] for concept in concepts
    }
    for current_capability in capabilities:
        for item in current_capability["requiredDefinitions"]:
            expected_concept_id = concept_id_by_ref.get(item["ref"])
            if item.get("conceptId") != expected_concept_id:
                errors.append(
                    f"{tactic_id}: requirement {item['ref']} has conceptId "
                    f"{item.get('conceptId')!r}, expected {expected_concept_id!r}"
                )

    for node in nodes:
        node_id = node["nodeId"]
        automation = node["automation"]
        formal = node["formalContract"]
        expected_incoming = [edge_contract(edge) for edge in incoming_edges[node_id]]
        expected_outgoing = [edge_contract(edge) for edge in outgoing_edges[node_id]]
        if formal["incomingEdges"] != expected_incoming:
            errors.append(f"{node_id}: incoming formal contract differs from Graph.Edge")
        if formal["outgoingEdges"] != expected_outgoing:
            errors.append(f"{node_id}: outgoing formal contract differs from Graph.Edge")
        if automation["executionClass"] == "interactiveFallback":
            errors.append(f"{node_id}: interactive fallback defeats exact automation")
        if automation["manualObligations"]:
            errors.append(f"{node_id}: avoidable manual obligations remain")
        if not automation["generatedOutputs"]:
            errors.append(f"{node_id}: generated output contract is empty")

        for item in automation["authorInputs"]:
            if item["provision"] not in AUTHOR_PROVISIONS:
                errors.append(f"{node_id}: author input {item['ref']} has derived provision")
            if not manifest_covers(item["ref"], manifest):
                errors.append(
                    f"{node_id}: author input {item['ref']} is absent from capability manifest"
                )
        for item in automation["inferredInputs"]:
            if item["provision"] != "typeclass_inferred":
                errors.append(f"{node_id}: inferred input {item['ref']} is mistagged")
        for item in automation["predecessorInputs"]:
            if item["provision"] != "derived_from_predecessor":
                errors.append(f"{node_id}: predecessor input {item['ref']} is mistagged")
        for item in automation["derivedInputs"]:
            if item["provision"] not in DERIVED_PROVISIONS:
                errors.append(f"{node_id}: derived input {item['ref']} is author-provided")

        expected_transitive = (
            automation["authorInputs"]
            + automation["inferredInputs"]
            + automation["predecessorInputs"]
            + automation["derivedInputs"]
            + automation["frameworkTheorems"]
        )
        if automation["transitiveDependencies"] != expected_transitive:
            errors.append(f"{node_id}: transitive dependency projection is not exact")

        is_terminal = node_id in terminal_nodes
        if is_terminal and node["nodeKind"] not in {"certificate", "residual"}:
            errors.append(f"{node_id}: terminal is not classified as certificate/residual")
        if not is_terminal and not outgoing_edges[node_id]:
            errors.append(f"{node_id}: executable node has no outgoing edge")

    cyclic = graph_has_cycle(node_set, transitions)
    if cyclic and tactic["loopDecrease"] is None:
        errors.append(f"{tactic_id}: cyclic graph has no compiled decrease theorem")
    if not cyclic and tactic["loopDecrease"] is not None:
        errors.append(f"{tactic_id}: acyclic graph exports a spurious decrease theorem")


def validate_transition_profiles(errors: list[str], catalog: dict) -> None:
    tactic_ids = {tactic["tacticId"] for tactic in catalog["tactics"]}
    residual_ids = {
        residual["residualKindId"]
        for tactic in catalog["tactics"]
        for residual in tactic["residualKinds"]
    }
    profile_ids: set[str] = set()
    profiles_by_family: dict[str, list[str]] = defaultdict(list)
    for profile in catalog["transitionProfiles"]:
        profile_id = profile["profileId"]
        if profile_id in profile_ids:
            errors.append(f"duplicate transition profile identifier {profile_id}")
        profile_ids.add(profile_id)
        family_id = f"{profile['sourceTacticId']}->{profile['targetTacticId']}"
        profiles_by_family[family_id].append(profile_id)
        if profile["familyId"] != family_id:
            errors.append(f"{profile_id}: transition family identifier is not canonical")
        if profile["sourceResidualKind"] not in residual_ids:
            errors.append(f"{profile_id}: source residual kind is not registered")
        if profile["sourceTacticId"] not in tactic_ids:
            errors.append(f"{profile_id}: source tactic is not registered")
        if profile["targetTacticId"] not in tactic_ids:
            errors.append(f"{profile_id}: target tactic is not registered")
        target_prefix = f"StructuralExhaustion.{profile['targetTacticId']}."
        if not (
            profile["targetExecutableInterface"].startswith(target_prefix)
            and profile["targetExecutableInterface"].endswith("executableInterface")
        ):
            errors.append(
                f"{profile_id}: target executable interface does not belong to "
                f"{profile['targetTacticId']}"
            )
        declaration_suffixes = {
            "transitionConstructor": ".transition",
            "advanceExecutor": ".advance",
        }
        for field, suffix in declaration_suffixes.items():
            declaration = profile[field]
            if not (
                declaration.startswith("StructuralExhaustion.Routes.")
                and declaration.endswith(suffix)
            ):
                errors.append(
                    f"{profile_id}: {field} is not the registered framework "
                    f"{suffix.removeprefix('.')} declaration"
                )
        boundary = profile.get("authoringBoundary")
        if not isinstance(boundary, dict):
            errors.append(f"{profile_id}: authoring boundary is missing")
            continue
        responsibilities = boundary.get("frameworkOwnedResponsibilities")
        if responsibilities != TRANSITION_FRAMEWORK_RESPONSIBILITIES:
            errors.append(
                f"{profile_id}: framework-owned transition responsibilities are not exact"
            )
        semantic_discovery = boundary.get("semanticDiscovery")
        if not isinstance(semantic_discovery, dict):
            errors.append(f"{profile_id}: semantic discovery boundary is missing")
            continue
        discovery_kind = semantic_discovery.get("kind")
        adapter_type = semantic_discovery.get("adapterType")
        problem_inputs = boundary.get("problemSpecificInputs")
        expected_inputs = TRANSITION_EXPECTED_PROBLEM_INPUTS.get(profile_id)
        if expected_inputs is not None and problem_inputs != expected_inputs:
            errors.append(
                f"{profile_id}: problem-specific transition inputs are not exact"
            )
        if discovery_kind == "capabilityDiscovery":
            if adapter_type is not None:
                errors.append(
                    f"{profile_id}: capability discovery must not name an adapter"
                )
            if not isinstance(problem_inputs, list) or (
                "targetCapability" not in problem_inputs
                or "semanticDiscoveryAdapter" in problem_inputs
            ):
                errors.append(
                    f"{profile_id}: capability-discovery input boundary is inconsistent"
                )
        elif discovery_kind == "problemSemanticAdapter":
            if not isinstance(problem_inputs, list) or (
                "targetCapability" not in problem_inputs
                or "semanticDiscoveryAdapter" not in problem_inputs
            ):
                errors.append(
                    f"{profile_id}: semantic-adapter input boundary is inconsistent"
                )
            if not isinstance(adapter_type, str) or not adapter_type.startswith(
                "StructuralExhaustion.Routes."
            ):
                errors.append(
                    f"{profile_id}: semantic adapter is not a Lean type reference"
                )
        else:
            errors.append(
                f"{profile_id}: unknown semantic discovery kind {discovery_kind}"
            )

    required_profiles = {
        "CT1.residual.avoiding->CT2",
        "CT1.residual.avoiding->CT2.localDeletion",
        "CT1.terminal.c1->CT12",
        "CT2.residual.separatingContext->CT3",
        "CT2.residual.criticality->CT10",
        "CT6.residual.activeLedger->CT9",
    }
    if not required_profiles <= profile_ids:
        errors.append(
            "missing foundational transition profiles "
            f"{sorted(required_profiles - profile_ids)}"
        )

    family_ids: set[str] = set()
    referenced_profile_ids: list[str] = []
    for family in catalog["transitionFamilies"]:
        family_id = family["familyId"]
        if family_id in family_ids:
            errors.append(f"duplicate transition family identifier {family_id}")
        family_ids.add(family_id)
        expected_family_id = f"{family['sourceTacticId']}->{family['targetTacticId']}"
        if family_id != expected_family_id:
            errors.append(f"{family_id}: transition family identifier is not canonical")
        expected_profiles = profiles_by_family.get(family_id, [])
        if family["profileIds"] != expected_profiles:
            errors.append(f"{family_id}: transition family profile projection is not exact")
        referenced_profile_ids.extend(family["profileIds"])
    if set(profiles_by_family) != family_ids:
        errors.append("transition families do not exactly cover registered CT pairs")
    if len(referenced_profile_ids) != len(set(referenced_profile_ids)):
        errors.append("a transition profile occurs in more than one family")
    if set(referenced_profile_ids) != profile_ids:
        errors.append("transition families do not exactly cover transition profiles")


def validate(root: Path) -> list[str]:
    errors = lint_lean_sources(root)
    catalog_path = root / "generated/lean-machines.json"
    schema_path = root / "schemas/lean-machine-catalog.schema.json"
    if not catalog_path.is_file():
        return errors + ["generated/lean-machines.json is missing"]

    catalog = load_json(catalog_path)
    schema = load_json(schema_path)
    for error in Draft202012Validator(schema).iter_errors(catalog):
        location = "/".join(str(part) for part in error.absolute_path)
        errors.append(f"catalog schema {location or '<root>'}: {error.message}")

    if catalog.get("sourceOfTruth", {}).get("kind") != "compiledLeanEnvironment":
        errors.append("catalog is not marked as a compiled Lean projection")
    errors.extend(retired_catalog_references(catalog))
    expected_ids = [f"CT{number}" for number in range(1, 18)]
    actual_ids = [tactic.get("tacticId") for tactic in catalog.get("tactics", [])]
    if actual_ids != expected_ids:
        errors.append(f"registry order is {actual_ids}, expected {expected_ids}")

    for tactic in catalog.get("tactics", []):
        validate_tactic(errors, tactic)
    validate_transition_profiles(errors, catalog)
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path("."))
    args = parser.parse_args()
    root = args.root.resolve()
    errors = validate(root)
    if errors:
        print("Repository validation failed:")
        for error in errors:
            print(f"- {error}")
        return 1

    catalog = load_json(root / "generated/lean-machines.json")
    print(
        "OK: 17 automation-first Lean tactics, "
        f"{sum(len(t['nodes']) for t in catalog['tactics'])} nodes, "
        f"{sum(len(t['transitions']) for t in catalog['tactics'])} typed edges, "
        f"{sum(len(t['residualKinds']) for t in catalog['tactics'])} residual kinds, "
        f"{len(catalog['transitionFamilies'])} transition families, "
        f"{len(catalog['transitionProfiles'])} transition profiles, "
        "0 manual node obligations"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
