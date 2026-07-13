from __future__ import annotations

import hashlib
import json
from collections import defaultdict, deque
from copy import deepcopy
from pathlib import Path

from jsonschema import Draft202012Validator

from tools.lint_automation_first import (
    AXIOM_DECLARATION_PATTERN,
    TRUSTED_EXTERNAL_AXIOMS,
    lint as lint_lean_sources,
)
from tools.render_artifacts import catalog_status_tex
from tools.render_schemas import render_schemas
from tools.validate_machine_run import validate_record
from tools.validate_repository import (
    AUTHOR_PROVISIONS,
    ROUTE_EXPECTED_PROBLEM_INPUTS,
    ROUTE_FRAMEWORK_RESPONSIBILITIES,
    validate,
    validate_routes,
    validate_tactic,
)
from tools.verify_lean import automation_graph_route_errors


ROOT = Path(__file__).resolve().parents[1]
CATALOG_PATH = ROOT / "generated/lean-machines.json"
MATHLIB_RELEASE = "v4.31.0"
MATHLIB_COMMIT = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"


def load(relative: str) -> dict:
    return json.loads((ROOT / relative).read_text(encoding="utf-8"))


def test_hss_is_the_only_trusted_external_axiom() -> None:
    assert TRUSTED_EXTERNAL_AXIOMS == {
        Path(
            "lean/StructuralExhaustion/Graph/External/"
            "HegdeSandeepShashank.lean"
        ): {"p13Free_hasPowerOfTwoCycle"}
    }
    authored_axioms: list[tuple[Path, str]] = []
    source_roots = [ROOT / "lean/StructuralExhaustion", ROOT / "examples"]
    for source_root in source_roots:
        for path in source_root.rglob("*.lean"):
            if ".lake" in path.parts:
                continue
            authored_axioms.extend(
                (path.relative_to(ROOT), name)
                for name in AXIOM_DECLARATION_PATTERN.findall(
                    path.read_text(encoding="utf-8")
                )
            )
    assert authored_axioms == [
        (
            Path(
                "lean/StructuralExhaustion/Graph/External/"
                "HegdeSandeepShashank.lean"
            ),
            "p13Free_hasPowerOfTwoCycle",
        )
    ]


def tactic_ids() -> list[str]:
    return [f"CT{number}" for number in range(1, 18)]


def edge_contract(edge: dict) -> dict:
    return {
        "edgeId": edge["edgeId"],
        "constructor": edge["constructor"],
        "constructorType": edge["constructorType"],
        "sourceNode": edge["sourceNode"],
        "targetNode": edge["targetNode"],
    }


def reachable(entry: str, transitions: list[dict]) -> set[str]:
    outgoing: dict[str, list[str]] = defaultdict(list)
    for edge in transitions:
        outgoing[edge["sourceNode"]].append(edge["targetNode"])
    seen: set[str] = set()
    queue = deque([entry])
    while queue:
        node = queue.popleft()
        if node in seen:
            continue
        seen.add(node)
        queue.extend(outgoing[node])
    return seen


def has_cycle(nodes: set[str], transitions: list[dict]) -> bool:
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


def manifest_covers(reference: str, manifest: set[str]) -> bool:
    if reference in manifest:
        return True
    return any(
        candidate.endswith(f".{reference}")
        or reference.endswith(f".{candidate}")
        for candidate in manifest
    )


def first_terminal_path(tactic: dict) -> tuple[list[dict], dict]:
    entry = next(
        node["nodeId"] for node in tactic["nodes"] if node["nodeKind"] == "entry"
    )
    terminals = {terminal["nodeId"]: terminal for terminal in tactic["terminals"]}
    outgoing: dict[str, list[dict]] = defaultdict(list)
    for edge in tactic["transitions"]:
        outgoing[edge["sourceNode"]].append(edge)
    queue: deque[tuple[str, list[dict]]] = deque([(entry, [])])
    seen: set[str] = set()
    while queue:
        node, path = queue.popleft()
        if node in terminals:
            return path, terminals[node]
        if node in seen:
            continue
        seen.add(node)
        for edge in outgoing[node]:
            queue.append((edge["targetNode"], path + [edge]))
    raise AssertionError(f"{tactic['tacticId']} has no reachable terminal")


def test_catalog_is_the_compiled_schema_v7_ct1_to_ct17_registry() -> None:
    catalog = load("generated/lean-machines.json")
    schema = load("schemas/lean-machine-catalog.schema.json")
    assert list(Draft202012Validator(schema).iter_errors(catalog)) == []
    assert catalog["artifactType"] == "automationFirstLeanCatalog"
    assert catalog["schemaVersion"] == "7.0.0"
    assert catalog["sourceOfTruth"] == {
        "kind": "compiledLeanEnvironment",
        "rootModule": "StructuralExhaustion",
        "registry": "StructuralExhaustion.Canonical.tactics",
    }
    assert [tactic["tacticId"] for tactic in catalog["tactics"]] == tactic_ids()
    assert len(catalog["provisionTaxonomy"]) == len(set(catalog["provisionTaxonomy"]))
    for tactic in catalog["tactics"]:
        assert tactic["namespace"] == f"StructuralExhaustion.{tactic['tacticId']}"
        assert tactic["apiVersion"].startswith(f"{tactic['tacticId']}-v")
        assert tactic["capability"]["tacticId"] == tactic["tacticId"]
        assert all(
            profile["tacticId"] == tactic["tacticId"]
            for profile in tactic["capabilityProfiles"]
        )
        concepts = tactic["capabilityConcepts"]
        requirement_refs = {
            item["ref"]
            for capability in [tactic["capability"], *tactic["capabilityProfiles"]]
            for item in capability["requiredDefinitions"]
        }
        assert {concept["requirementRef"] for concept in concepts} == requirement_refs
        assert len({concept["conceptId"] for concept in concepts}) == len(concepts)
        concept_ids = {concept["conceptId"] for concept in concepts}
        assert all(
            item["conceptId"] in concept_ids
            for capability in [tactic["capability"], *tactic["capabilityProfiles"]]
            for item in capability["requiredDefinitions"]
        )
        run_declaration = next(
            declaration
            for declaration in tactic["apiDeclarations"]
            if declaration["name"] == f"{tactic['namespace']}.run"
        )
        assert "ExecutionResult" in run_declaration["type"]


def test_canonical_lean_sources_have_standard_surface_and_no_legacy_api() -> None:
    assert lint_lean_sources(ROOT) == []
    root_module = (ROOT / "lean/StructuralExhaustion.lean").read_text(encoding="utf-8")
    for tactic_id in tactic_ids():
        directory = ROOT / f"lean/StructuralExhaustion/{tactic_id}"
        for filename in ("Automation.lean", "Execution.lean", "Graph.lean", "Theorems.lean"):
            assert (directory / filename).is_file()
        for legacy in ("Interface.lean", "StaticInputs.lean", "StaticContract.lean"):
            assert not (directory / legacy).exists()

        automation = (directory / "Automation.lean").read_text(encoding="utf-8")
        assert "nodeAutomationContracts" in automation
        assert "residualKindContracts" in automation
        tactic_number = tactic_id.removeprefix("CT")
        assert f'ct{tactic_number}_execute ' in automation
        assert f'ct{tactic_number}_total ' in automation
        assert any(
            "capabilityContract" in path.read_text(encoding="utf-8")
            for path in directory.glob("*.lean")
        )
        graph = (directory / "Graph.lean").read_text(encoding="utf-8")
        for declaration in ("inductive NodeId", "inductive Edge", "inductive Path", "ValidTrace"):
            assert declaration in graph
        theorems = (directory / "Theorems.lean").read_text(encoding="utf-8")
        for declaration in (
            "run_verified",
            "run_trace_valid",
            "run_total",
            "run_deterministic",
            "outcome_exhaustive",
        ):
            assert declaration in theorems
        assert f"import StructuralExhaustion.{tactic_id}.Automation" in root_module
        assert (ROOT / f"lean/StructuralExhaustion/Examples/{tactic_id}AutomationFirst.lean").is_file()


def test_all_lake_packages_pin_the_same_mathlib_and_toolchain() -> None:
    package_roots = [
        ROOT / "lean",
        ROOT / "examples/even_cycle",
        ROOT / "examples/erdos_64_eg",
        ROOT / "examples/greedy_coloring",
        ROOT / "examples/mantel",
    ]
    toolchains = {
        (package_root / "lean-toolchain").read_text(encoding="utf-8").strip()
        for package_root in package_roots
    }
    assert toolchains == {"leanprover/lean4:v4.31.0"}

    for package_root in package_roots:
        lakefile = (package_root / "lakefile.toml").read_text(encoding="utf-8")
        assert 'name = "mathlib"' in lakefile
        assert 'git = "https://github.com/leanprover-community/mathlib4"' in lakefile
        assert f'rev = "{MATHLIB_RELEASE}"' in lakefile

        manifest = json.loads(
            (package_root / "lake-manifest.json").read_text(encoding="utf-8")
        )
        mathlib = next(
            package for package in manifest["packages"]
            if package["name"] == "mathlib"
        )
        assert mathlib["inputRev"] == MATHLIB_RELEASE
        assert mathlib["rev"] == MATHLIB_COMMIT


def test_graph_examples_are_external_framework_consumers() -> None:
    for example_name in ("even_cycle", "erdos_64_eg", "greedy_coloring", "mantel"):
        example_root = ROOT / f"examples/{example_name}"
        lakefile = (example_root / "lakefile.toml").read_text(encoding="utf-8")
        assert 'name = "structural_exhaustion"' in lakefile
        assert 'path = "../../lean"' in lakefile

        manifest = json.loads(
            (example_root / "lake-manifest.json").read_text(encoding="utf-8")
        )
        dependency = next(
            package
            for package in manifest["packages"]
            if package["name"] == "structural_exhaustion"
        )
        assert dependency["type"] == "path"
        assert dependency["dir"] == "../../lean"

    framework_sources = list((ROOT / "lean/StructuralExhaustion").rglob("*.lean"))
    assert all(
        all(
            f"import {module}" not in path.read_text(encoding="utf-8")
            for module in (
                "EvenCycleExample", "Erdos64EG", "GreedyColoringExample",
                "MantelExample",
            )
        )
        for path in framework_sources
    )


def test_mathlib_graph_profiles_are_framework_owned_and_reused() -> None:
    graph_root = ROOT / "lean/StructuralExhaustion/Graph"
    minimum_degree = (graph_root / "MinimumDegreeCycle.lean").read_text(
        encoding="utf-8"
    )
    minimum_degree_routed = (
        graph_root / "MinimumDegreeCycleRouted.lean"
    ).read_text(encoding="utf-8")
    endpoint_parity = (graph_root / "EndpointParityCycle.lean").read_text(
        encoding="utf-8"
    )
    greedy_coloring = (graph_root / "GreedyColoring.lean").read_text(
        encoding="utf-8"
    )
    mantel = (graph_root / "Mantel.lean").read_text(encoding="utf-8")
    graph_umbrella = (ROOT / "lean/StructuralExhaustion/Graph.lean").read_text(
        encoding="utf-8"
    )

    for declaration in (
        "structure StaticInput",
        "def targetEncoding",
        "def ct2Capability",
        "def ct2DeletionRule",
        "theorem dart_has_tight_endpoint",
    ):
        assert declaration in minimum_degree
    for declaration in (
        "def edgeRootedEncoding",
        "def edgeRootedDeletionProfile",
        "theorem routedDart_has_tight_endpoint",
        "structure EdgeRootedDeletionPrefix",
        "theorem exists_edgeRootedDeletionPrefix",
    ):
        assert declaration in minimum_degree_routed
    for declaration in (
        "structure Profile",
        "def ct6Run",
        "def ct9Run",
        "def sameParityEndpointPositions",
        "theorem target_of_baseline",
        "def ct1Run",
    ):
        assert declaration in endpoint_parity
    for declaration in (
        "inductive BoundedOrder",
        "def stepProfile",
        "def colorOrder",
        "theorem colorable_of_bounded_order",
        "def maxDegreeColoring",
        "theorem colorable_maxDegree_succ",
        "def peelingRun",
        "def ct1Run",
    ):
        assert declaration in greedy_coloring
    for declaration in (
        "def dartCells",
        "def localBudget",
        "def profile",
        "theorem sum_localBudget_eq",
        "def run",
        "theorem offending_degree_sum_gt",
        "theorem edgeCount_le_card_sq_div_four_of_triangleFree",
    ):
        assert declaration in mantel

    assert "import StructuralExhaustion.Graph.MinimumDegreeCycle" in graph_umbrella
    assert (
        "import StructuralExhaustion.Graph.MinimumDegreeCycleRouted"
        in graph_umbrella
    )
    assert "import StructuralExhaustion.Graph.EndpointParityCycle" in graph_umbrella
    assert "import StructuralExhaustion.Graph.GreedyColoring" in graph_umbrella
    assert "import StructuralExhaustion.Graph.Mantel" in graph_umbrella

    even_problem = (
        ROOT / "examples/even_cycle/EvenCycleExample/Problem.lean"
    ).read_text(encoding="utf-8")
    erdos_problem = (
        ROOT / "examples/erdos_64_eg/Erdos64EG/InternalProblem.lean"
    ).read_text(encoding="utf-8")
    assert "EndpointParityCycle.Profile.evenCycle" in even_problem
    assert "MinimumDegreeCycle.StaticInput" in erdos_problem

    even_deletion = (
        ROOT / "examples/even_cycle/EvenCycleExample/CT2Audit.lean"
    ).read_text(encoding="utf-8")
    erdos_ct1 = (
        ROOT / "examples/erdos_64_eg/Erdos64EG/CT1.lean"
    ).read_text(encoding="utf-8")
    erdos_ct2 = (
        ROOT / "examples/erdos_64_eg/Erdos64EG/CT2.lean"
    ).read_text(encoding="utf-8")
    assert "(staticInput V).cycleDeletionProfile" in even_deletion
    assert "(staticInput V).edgeRootedEncoding" in erdos_ct1
    assert "(staticInput V).edgeRootedDeletionProfile" in erdos_ct2
    assert "TargetCertificateEncoding (P := problem V)" not in erdos_ct1
    assert "structure VerifiedCT1CT2Prefix" not in erdos_ct2
    assert "discover_disabled_of_closure" not in erdos_ct2


def test_greedy_coloring_example_is_thin_and_complete() -> None:
    example_root = ROOT / "examples/greedy_coloring"
    run_source = (example_root / "GreedyColoringExample/Run.lean").read_text(
        encoding="utf-8"
    )
    assert "Graph.GreedyColoring.colorable_maxDegree_succ" in run_source
    assert "Graph.GreedyColoring.peelingRun" in run_source
    assert "Graph.GreedyColoring.ct1Run" in run_source
    assert "CT4.FunctionalCardinalityProfile" not in run_source

    concrete = (example_root / "GreedyColoringExample/Concrete.lean").read_text(
        encoding="utf-8"
    )
    for theorem in (
        "coloring_values",
        "coloring_is_proper",
        "ct12_terminal_exhausted",
        "ct4_terminal_missing",
        "ct1_terminal_c1",
    ):
        assert theorem in concrete


def test_mantel_example_is_thin_and_complete() -> None:
    example_root = ROOT / "examples/mantel"
    run_source = (example_root / "MantelExample/Run.lean").read_text(
        encoding="utf-8"
    )
    assert "Graph.Mantel.edgeCount_le_card_sq_div_four_of_triangleFree" in run_source
    assert "Graph.Mantel.run" in run_source
    assert "CT11.NegativeBudgetProfile" not in run_source

    concrete = (example_root / "MantelExample/Concrete.lean").read_text(
        encoding="utf-8"
    )
    for theorem in (
        "terminal_localized",
        "trace_exact",
        "selected_dart_exact",
        "triangleFree",
        "mantel_bound",
    ):
        assert theorem in concrete


def test_even_cycle_example_exposes_the_complete_run_surface() -> None:
    example_root = ROOT / "examples/even_cycle"
    assert not (ROOT / "lean/StructuralExhaustion/Examples/EvenCycle").exists()

    run_source = (example_root / "EvenCycleExample/Run.lean").read_text(
        encoding="utf-8"
    )
    assert "minimumDegreeThree_hasEvenCycle" in run_source
    assert "finalCT1Run" in run_source
    assert "import EvenCycleExample.Concrete" not in run_source
    deletion_audit = (
        example_root / "EvenCycleExample/CT2Audit.lean"
    ).read_text(encoding="utf-8")
    assert "(staticInput V).ct2DeletionRule" in deletion_audit
    assert "localRoute_disabled" in deletion_audit
    assert "MinimumDegreeCycleRouted" in deletion_audit
    assert "(staticInput V).cycleDeletionProfile" in deletion_audit
    assert "Routes.CT1ToCT2.LocalDeletion.rule" not in deletion_audit
    assert "heavyDartRun" in deletion_audit
    concrete = (example_root / "EvenCycleExample/Concrete.lean").read_text(
        encoding="utf-8"
    )
    for theorem in (
        "ct6_trace_exact",
        "ct9_trace_exact",
        "ct1_trace_exact",
    ):
        assert theorem in concrete


def test_every_node_has_exact_automation_and_capability_contracts() -> None:
    for tactic in load("generated/lean-machines.json")["tactics"]:
        capability = tactic["capability"]
        manifest = {
            item["ref"] for item in capability["requiredDefinitions"]
        } | {item["ref"] for item in capability["requiredInstances"]}
        assert capability["derivedOperations"]
        assert all(
            item["provision"] in AUTHOR_PROVISIONS
            for item in capability["requiredDefinitions"]
        )
        assert all(
            item["provision"] == "typeclass_inferred"
            for item in capability["requiredInstances"]
        )

        node_ids = [node["nodeId"] for node in tactic["nodes"]]
        assert len(node_ids) == len(set(node_ids))
        assert [node["ordinal"] for node in tactic["nodes"]] == list(
            range(1, len(node_ids) + 1)
        )
        for node in tactic["nodes"]:
            automation = node["automation"]
            assert automation["generatedOutputs"]
            assert automation["manualObligations"] == []
            assert automation["executionClass"] != "interactiveFallback"
            assert all(
                manifest_covers(item["ref"], manifest)
                for item in automation["authorInputs"]
            )
            expected = (
                automation["authorInputs"]
                + automation["inferredInputs"]
                + automation["predecessorInputs"]
                + automation["derivedInputs"]
                + automation["frameworkTheorems"]
            )
            assert automation["transitiveDependencies"] == expected
            assert node["formalContract"]["predecessorIndexed"] is True
            output_refs = {item["ref"] for item in automation["generatedOutputs"]}
            assert all("|" not in reference for reference in output_refs)
            dependency_refs = {
                item["ref"]
                for key in ("predecessorInputs", "derivedInputs")
                for item in automation[key]
            }
            assert output_refs.isdisjoint(dependency_refs)


def test_graphs_are_closed_reachable_exact_and_only_ct12_is_cyclic() -> None:
    catalog = load("generated/lean-machines.json")
    for tactic in catalog["tactics"]:
        nodes = tactic["nodes"]
        transitions = tactic["transitions"]
        node_ids = {node["nodeId"] for node in nodes}
        entries = [node["nodeId"] for node in nodes if node["nodeKind"] == "entry"]
        assert len(entries) == 1
        assert reachable(entries[0], transitions) == node_ids
        assert [edge["ordinal"] for edge in transitions] == list(
            range(1, len(transitions) + 1)
        )
        assert all(edge["provision"] == "generated_audit" for edge in transitions)
        assert all(
            edge["sourceNode"] in node_ids and edge["targetNode"] in node_ids
            for edge in transitions
        )

        terminals = {terminal["nodeId"] for terminal in tactic["terminals"]}
        assert terminals == {
            node["nodeId"]
            for node in nodes
            if node["nodeKind"] in {"certificate", "residual"}
        }
        for node in nodes:
            incoming = [edge_contract(edge) for edge in transitions if edge["targetNode"] == node["nodeId"]]
            outgoing = [edge_contract(edge) for edge in transitions if edge["sourceNode"] == node["nodeId"]]
            assert node["formalContract"]["incomingEdges"] == incoming
            assert node["formalContract"]["outgoingEdges"] == outgoing
            if node["nodeId"] in terminals:
                assert outgoing == []

        cyclic = has_cycle(node_ids, transitions)
        if tactic["tacticId"] == "CT12":
            assert cyclic
            assert tactic["loopDecrease"] is not None
            assert "next < load" in tactic["loopDecrease"]["type"] or "next < current" in tactic["loopDecrease"]["type"]
            without_back_edge = [
                edge for edge in transitions if edge["edgeId"] != "CT12.edge.loopBack"
            ]
            assert not has_cycle(node_ids, without_back_edge)
        else:
            assert not cyclic
            assert tactic["loopDecrease"] is None


def test_residual_registry_and_routes_are_explicit_and_framework_owned() -> None:
    catalog = load("generated/lean-machines.json")
    residuals = [
        residual for tactic in catalog["tactics"] for residual in tactic["residualKinds"]
    ]
    residual_ids = {residual["residualKindId"] for residual in residuals}
    assert len(residual_ids) == len(residuals)
    assert all(residual["semanticFields"] for residual in residuals)
    assert {route["routeId"] for route in catalog["routes"]} == {
        "CT1.residual.avoiding->CT2",
        "CT1.residual.avoiding->CT2.localDeletion",
        "CT2.residual.separatingContext->CT3",
        "CT2.residual.criticality->CT10",
        "CT6.residual.activeLedger->CT9",
    }
    expected_semantic_discovery = {
        "CT1.residual.avoiding->CT2": {
            "kind": "capabilityDiscovery",
            "adapterType": None,
        },
        "CT1.residual.avoiding->CT2.localDeletion": {
            "kind": "capabilityDiscovery",
            "adapterType": None,
        },
        "CT2.residual.separatingContext->CT3": {
            "kind": "problemSemanticAdapter",
            "adapterType": "StructuralExhaustion.Routes.CT2ToCT3.PieceDiscovery",
        },
        "CT2.residual.criticality->CT10": {
            "kind": "problemSemanticAdapter",
            "adapterType": "StructuralExhaustion.Routes.CT2ToCT10.DataDiscovery",
        },
        "CT6.residual.activeLedger->CT9": {
            "kind": "problemSemanticAdapter",
            "adapterType": "StructuralExhaustion.Routes.CT6ToCT9.ItemCollectionAdapter",
        },
    }
    for route in catalog["routes"]:
        route_id = route["routeId"]
        assert route["sourceResidualKind"] in residual_ids
        assert route["targetTacticId"] in tactic_ids()
        assert "instanceAuthoringRequired" not in route
        boundary = route["authoringBoundary"]
        assert boundary["semanticDiscovery"] == expected_semantic_discovery[route_id]
        assert boundary["problemSpecificInputs"] == ROUTE_EXPECTED_PROBLEM_INPUTS[
            route_id
        ]
        assert (
            boundary["frameworkOwnedResponsibilities"]
            == ROUTE_FRAMEWORK_RESPONSIBILITIES
        )
        for field in (
            "discovery",
            "triggerConstructor",
            "soundnessTheorem",
            "contextPreservationTheorem",
            "provenanceTheorem",
        ):
            assert route[field].startswith("StructuralExhaustion.")


def test_generated_schemas_are_exact_catalog_residual_and_route_projections() -> None:
    catalog = load("generated/lean-machines.json")
    index = load("schemas/generated/index.json")
    assert index["schemaVersion"] == "2.0.0"
    assert index["canonicalCatalog"] == "generated/lean-machines.json"
    assert [item["tacticId"] for item in index["tactics"]] == tactic_ids()

    tactic_by_id = {tactic["tacticId"]: tactic for tactic in catalog["tactics"]}
    expected_paths: set[str] = set(index["routes"])
    for item in index["tactics"]:
        tactic = tactic_by_id[item["tacticId"]]
        expected_paths.update(
            [item["tacticSchema"], item["runSchema"], item["verificationSchema"]]
        )
        expected_paths.update(item["nodeSchemas"])
        expected_paths.update(item["residualSchemas"])

        tactic_schema = load(item["tacticSchema"])
        Draft202012Validator.check_schema(tactic_schema)
        assert tactic_schema["allOf"][1]["const"] == tactic
        assert tactic_schema["x-capability"] == tactic["capability"]
        assert tactic_schema["x-capabilityProfiles"] == tactic["capabilityProfiles"]
        assert tactic_schema["x-capabilityConcepts"] == tactic["capabilityConcepts"]

        nodes = {node["nodeId"]: node for node in tactic["nodes"]}
        for relative in item["nodeSchemas"]:
            schema = load(relative)
            Draft202012Validator.check_schema(schema)
            node = schema["allOf"][1]["const"]
            assert node == nodes[node["nodeId"]]
            assert schema["x-automationContract"] == node["automation"]
            assert schema["x-formalContract"] == node["formalContract"]

        residuals = {
            residual["residualKindId"]: residual for residual in tactic["residualKinds"]
        }
        for relative in item["residualSchemas"]:
            schema = load(relative)
            Draft202012Validator.check_schema(schema)
            residual = schema["allOf"][1]["const"]
            assert residual == residuals[residual["residualKindId"]]

        verification = load(item["verificationSchema"])
        constants = verification["allOf"][1]["properties"]
        assert constants["nodeCount"]["const"] == len(tactic["nodes"])
        assert constants["transitionCount"]["const"] == len(tactic["transitions"])
        assert constants["terminalCount"]["const"] == len(tactic["terminals"])
        assert constants["manualObligationCount"]["const"] == 0

    route_by_id = {route["routeId"]: route for route in catalog["routes"]}
    for relative in index["routes"]:
        schema = load(relative)
        Draft202012Validator.check_schema(schema)
        route = schema["allOf"][1]["const"]
        assert route == route_by_id[route["routeId"]]

    actual_paths = {
        path.relative_to(ROOT).as_posix()
        for path in (ROOT / "schemas/generated").rglob("*.schema.json")
    }
    assert actual_paths == expected_paths


def test_schema_renderer_reproduces_the_checked_in_projection(tmp_path: Path) -> None:
    catalog = load("generated/lean-machines.json")
    schema_root = tmp_path / "schemas"
    schema_root.mkdir(parents=True)
    for schema in (ROOT / "schemas").glob("*.schema.json"):
        (schema_root / schema.name).write_bytes(schema.read_bytes())
    render_schemas(tmp_path, catalog)
    expected_root = tmp_path / "schemas/generated"
    observed_root = ROOT / "schemas/generated"
    expected = {
        path.relative_to(expected_root).as_posix(): path.read_bytes()
        for path in expected_root.rglob("*") if path.is_file()
    }
    observed = {
        path.relative_to(observed_root).as_posix(): path.read_bytes()
        for path in observed_root.rglob("*") if path.is_file()
    }
    assert observed == expected


def test_run_validator_accepts_a_compiled_path_and_rejects_reordering() -> None:
    catalog = load("generated/lean-machines.json")
    tactic = next(tactic for tactic in catalog["tactics"] if tactic["tacticId"] == "CT2")
    path, terminal = first_terminal_path(tactic)
    execution_ref = next(
        declaration["name"]
        for declaration in tactic["apiDeclarations"]
        if declaration["name"] == "StructuralExhaustion.CT2.run"
    )

    def step(edge: dict) -> dict:
        return {
            "edgeOrdinal": edge["ordinal"],
            "edgeId": edge["edgeId"],
            "constructor": edge["constructor"],
            "edgeType": edge["constructorType"],
            "sourceNode": edge["sourceNode"],
            "targetNode": edge["targetNode"],
            "evidenceRef": None,
        }

    record = {
        "artifactType": "leanMachineRun",
        "schemaVersion": "2.0.0",
        "tacticId": tactic["tacticId"],
        "apiVersion": tactic["apiVersion"],
        "catalogHash": hashlib.sha256(CATALOG_PATH.read_bytes()).hexdigest(),
        "executionRef": execution_ref,
        "startNode": next(
            node["nodeId"] for node in tactic["nodes"] if node["nodeKind"] == "entry"
        ),
        "steps": [step(edge) for edge in path],
        "terminal": terminal,
    }
    assert validate_record(record) == []

    reordered = deepcopy(record)
    reordered["steps"][:2] = reversed(reordered["steps"][:2])
    assert any("does not continue" in error for error in validate_record(reordered))

    wrong_hash = deepcopy(record)
    wrong_hash["catalogHash"] = "0" * 64
    assert "catalogHash does not match" in "\n".join(validate_record(wrong_hash))


def test_manifest_projects_the_catalog_and_generated_files_exist() -> None:
    catalog = load("generated/lean-machines.json")
    manifest = load("generated/manifest.json")
    route_manifest = load("generated/route-manifest.json")
    assert manifest["schemaVersion"] == "3.0.0"
    assert manifest["catalog"] == "generated/lean-machines.json"
    assert manifest["catalogStatus"] == "framework/generated/catalog-status.tex"
    assert (ROOT / manifest["catalogStatus"]).is_file()
    assert [item["tacticId"] for item in manifest["tactics"]] == tactic_ids()
    assert manifest["routes"] == catalog["routes"]
    assert route_manifest["schemaVersion"] == "2.0.0"
    assert route_manifest["routes"] == catalog["routes"]
    for tactic in manifest["tactics"]:
        for key in ("mermaid", "cytoscape", "manuscriptFigure"):
            assert (ROOT / tactic[key]).is_file()


def test_catalog_status_is_computed_from_catalog() -> None:
    catalog = load("generated/lean-machines.json")
    status = catalog_status_tex(catalog)
    assert rf"\newcommand{{\CatalogTacticCount}}{{{len(catalog['tactics'])}}}" in status
    assert rf"\newcommand{{\CatalogRouteCount}}{{{len(catalog['routes'])}}}" in status
    capability_routes = sum(
        route["authoringBoundary"]["semanticDiscovery"]["kind"]
        == "capabilityDiscovery"
        for route in catalog["routes"]
    )
    adapter_routes = sum(
        route["authoringBoundary"]["semanticDiscovery"]["kind"]
        == "problemSemanticAdapter"
        for route in catalog["routes"]
    )
    assert (
        rf"\newcommand{{\CatalogCapabilityDiscoveryRouteCount}}{{{capability_routes}}}"
        in status
    )
    assert (
        rf"\newcommand{{\CatalogProblemSemanticAdapterRouteCount}}{{{adapter_routes}}}"
        in status
    )
    manual_obligations = sum(
        len(node["automation"]["manualObligations"])
        for tactic in catalog["tactics"]
        for node in tactic["nodes"]
    )
    assert (
        rf"\newcommand{{\CatalogManualObligationCount}}{{{manual_obligations}}}"
        in status
    )


def test_repository_validator_accepts_and_rejects_contract_corruption() -> None:
    assert validate(ROOT) == []
    catalog = load("generated/lean-machines.json")

    broken_tactic = deepcopy(catalog["tactics"][0])
    broken_tactic["nodes"][0]["automation"]["generatedOutputs"] = []
    errors: list[str] = []
    validate_tactic(errors, broken_tactic)
    assert any("generated output contract is empty" in error for error in errors)

    broken_concepts = deepcopy(catalog["tactics"][0])
    broken_concepts["capabilityConcepts"].pop()
    errors = []
    validate_tactic(errors, broken_concepts)
    assert any("capability concepts omit requirements" in error for error in errors)

    wrong_concept_link = deepcopy(catalog["tactics"][0])
    wrong_concept_link["capability"]["requiredDefinitions"][0][
        "conceptId"
    ] = "CT1.capability.wrong"
    errors = []
    validate_tactic(errors, wrong_concept_link)
    assert any("has conceptId" in error for error in errors)

    broken_routes = deepcopy(catalog)
    broken_routes["routes"][0]["sourceResidualKind"] = "CT1.residual.unknown"
    errors = []
    validate_routes(errors, broken_routes)
    assert any("source residual kind is not registered" in error for error in errors)

    broken_authoring = deepcopy(catalog)
    separating_route = next(
        route
        for route in broken_authoring["routes"]
        if route["routeId"] == "CT2.residual.separatingContext->CT3"
    )
    separating_route["authoringBoundary"]["semanticDiscovery"]["adapterType"] = (
        "StructuralExhaustion.Routes.CT2ToCT10.DataDiscovery"
    )
    errors = []
    validate_routes(errors, broken_authoring)
    assert any("not the semantic adapter projection" in error for error in errors)

    hidden_adapter = deepcopy(catalog)
    hidden_adapter["routes"][0]["authoringBoundary"]["problemSpecificInputs"].append(
        "semanticDiscoveryAdapter"
    )
    errors = []
    validate_routes(errors, hidden_adapter)
    assert any("input boundary is inconsistent" in error for error in errors)

    composite_output = deepcopy(catalog)
    composite_output["tactics"][0]["nodes"][0]["automation"][
        "generatedOutputs"
    ][0]["ref"] = "FirstOutput|SecondOutput"
    assert any(
        "combines distinct Lean outputs" in error
        for error in automation_graph_route_errors(composite_output)
    )

    overlapping_output = deepcopy(catalog)
    automation = overlapping_output["tactics"][0]["nodes"][0]["automation"]
    automation["generatedOutputs"][0]["ref"] = automation["predecessorInputs"][0][
        "ref"
    ]
    assert any(
        "generated outputs overlap inputs" in error
        for error in automation_graph_route_errors(overlapping_output)
    )


def test_kernel_verification_matches_the_current_catalog() -> None:
    catalog = load("generated/lean-machines.json")
    verification = load("generated/kernel-verification.json")
    schema = load("schemas/kernel-verification.schema.json")
    assert list(Draft202012Validator(schema).iter_errors(verification)) == []
    assert verification["status"] == "kernel_checked"
    assert set(verification["aggregate"].values()) == {"passed"}
    assert verification["catalogHash"] == hashlib.sha256(CATALOG_PATH.read_bytes()).hexdigest()
    summaries = {item["tacticId"]: item for item in verification["tactics"]}
    assert list(summaries) == tactic_ids()
    for tactic in catalog["tactics"]:
        summary = summaries[tactic["tacticId"]]
        assert summary["nodeCount"] == len(tactic["nodes"])
        assert summary["transitionCount"] == len(tactic["transitions"])
        assert summary["terminalCount"] == len(tactic["terminals"])
