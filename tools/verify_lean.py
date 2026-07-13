#!/usr/bin/env python3
"""Kernel-check the canonical automation-first Lean catalog and projections."""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from jsonschema import Draft202012Validator

try:
    from lint_automation_first import (
        lint as lint_lean_sources,
        untrusted_admissions,
    )
    from validate_repository import validate_routes, validate_tactic
except ImportError:  # imported as tools.verify_lean
    from tools.lint_automation_first import (
        lint as lint_lean_sources,
        untrusted_admissions,
    )
    from tools.validate_repository import validate_routes, validate_tactic


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "lean"
EXAMPLE_ROOTS = {
    "evenCycleExample": ROOT / "examples/even_cycle",
    "erdos64Example": ROOT / "examples/erdos_64_eg",
    "greedyColoringExample": ROOT / "examples/greedy_coloring",
    "mantelExample": ROOT / "examples/mantel",
}
PACKAGE_ROOTS = {"framework": LEAN_ROOT, **EXAMPLE_ROOTS}
CATALOG_PATH = ROOT / "generated/lean-machines.json"
CATALOG_SCHEMA_PATH = ROOT / "schemas/lean-machine-catalog.schema.json"
GENERATED_SCHEMA_ROOT = ROOT / "schemas/generated"
RESULT_PATH = ROOT / "generated/kernel-verification.json"
EXAMPLE_INDEX_PATH = ROOT / "generated/examples/index.json"
EXAMPLE_EXPORTS = {
    "evenCycleExample": ("EvenCycleExample/WebExport.lean", "even-cycle.raw.json"),
    "erdos64Example": ("Erdos64EG/WebExport.lean", "erdos-64.raw.json"),
    "greedyColoringExample": (
        "GreedyColoringExample/WebExport.lean",
        "greedy-coloring.raw.json",
    ),
    "mantelExample": ("MantelExample/WebExport.lean", "mantel.raw.json"),
}


def run(
    command: list[str],
    *,
    cwd: Path = LEAN_ROOT,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=cwd,
        env=env,
        text=True,
        capture_output=True,
    )


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_lean_comments_and_strings(source: str) -> str:
    """Remove non-code regions before scanning for authored admissions."""
    previous = None
    while source != previous:
        previous = source
        source = re.sub(r"/-.*?-/", "", source, flags=re.S)
    source = re.sub(r"--.*", "", source)
    return re.sub(r'"(?:\\.|[^"\\])*"', '""', source)


def authored_admissions() -> list[str]:
    offenders: list[str] = []
    source_roots = [LEAN_ROOT / "StructuralExhaustion", *EXAMPLE_ROOTS.values()]
    for source_root in source_roots:
        for path in sorted(source_root.rglob("*.lean")):
            if "Generated" in path.parts or ".lake" in path.parts:
                continue
            source = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
            relative = path.relative_to(ROOT)
            if untrusted_admissions(relative, source):
                offenders.append(path.relative_to(ROOT).as_posix())
    return offenders


def json_schema_errors(catalog: dict) -> list[str]:
    schema = json.loads(CATALOG_SCHEMA_PATH.read_text(encoding="utf-8"))
    return [
        f"{'/'.join(map(str, error.absolute_path)) or '<root>'}: {error.message}"
        for error in Draft202012Validator(schema).iter_errors(catalog)
    ]


def automation_graph_route_errors(catalog: dict) -> list[str]:
    errors: list[str] = []
    for tactic in catalog.get("tactics", []):
        validate_tactic(errors, tactic)
        for node in tactic["nodes"]:
            automation = node["automation"]
            output_refs = {
                item["ref"] for item in automation["generatedOutputs"]
            }
            dependency_refs = {
                item["ref"]
                for key in ("predecessorInputs", "derivedInputs")
                for item in automation[key]
            }
            for reference in output_refs:
                if "|" in reference:
                    errors.append(
                        f"{node['nodeId']}: generated output {reference} "
                        "combines distinct Lean outputs"
                    )
            overlap = sorted(output_refs & dependency_refs)
            if overlap:
                errors.append(
                    f"{node['nodeId']}: generated outputs overlap inputs {overlap}"
                )
    validate_routes(errors, catalog)
    return errors


def binding_check(catalog: dict) -> str:
    """Generate a declaration check directly from the current catalog."""
    declarations: list[str] = []
    for tactic in catalog["tactics"]:
        declarations.extend(item["name"] for item in tactic["apiDeclarations"])
        declarations.extend(
            concept["formalDeclaration"]["name"]
            for concept in tactic["capabilityConcepts"]
        )
        declarations.extend(edge["constructor"] for edge in tactic["transitions"])
        declarations.extend(terminal["constructor"] for terminal in tactic["terminals"])
        for profile in tactic.get("capabilityProfiles", []):
            declarations.extend(
                item["ref"]
                for key in ("requiredDefinitions", "derivedOperations")
                for item in profile[key]
            )
    for route in catalog["routes"]:
        declarations.extend(
            route[field]
            for field in (
                "discovery",
                "triggerConstructor",
                "soundnessTheorem",
                "contextPreservationTheorem",
                "provenanceTheorem",
            )
        )
        adapter_type = route["authoringBoundary"]["semanticDiscovery"][
            "adapterType"
        ]
        if adapter_type is not None:
            declarations.append(adapter_type)
    unique = list(dict.fromkeys(declarations))
    return (
        "import StructuralExhaustion\n\n"
        "/-! Ephemeral automation-first declaration binding check. -/\n\n"
        + "\n".join(f"#check {name}" for name in unique)
        + "\n"
    )


def files_below(root: Path, pattern: str) -> dict[str, bytes]:
    if not root.is_dir():
        return {}
    return {
        path.relative_to(root).as_posix(): path.read_bytes()
        for path in sorted(root.rglob(pattern))
        if path.is_file()
    }


def schemas_are_fresh(catalog_path: Path) -> tuple[bool, str]:
    with tempfile.TemporaryDirectory(prefix="structural-exhaustion-schemas-") as raw:
        temporary_root = Path(raw)
        temporary_schema_root = temporary_root / "schemas"
        temporary_schema_root.mkdir(parents=True)
        for schema in (ROOT / "schemas").glob("*.schema.json"):
            shutil.copy2(schema, temporary_schema_root / schema.name)
        rendered = run(
            [
                sys.executable,
                str(ROOT / "tools/render_schemas.py"),
                "--catalog",
                str(catalog_path),
                "--root",
                str(temporary_root),
            ],
            cwd=ROOT,
        )
        if rendered.returncode != 0:
            return False, rendered.stdout + rendered.stderr
        expected = files_below(temporary_root / "schemas/generated", "*")
        observed = files_below(GENERATED_SCHEMA_ROOT, "*")
        if expected == observed:
            return True, ""
        missing = sorted(set(expected) - set(observed))
        stale = sorted(set(observed) - set(expected))
        changed = sorted(
            path for path in set(expected) & set(observed)
            if expected[path] != observed[path]
        )
        return False, (
            f"generated schema mismatch; missing={missing}, stale={stale}, "
            f"changed={changed}"
        )


def generated_artifacts_are_fresh(catalog_path: Path) -> tuple[bool, str]:
    """Compare every catalog-owned file below ``generated/`` byte for byte."""
    with tempfile.TemporaryDirectory(prefix="structural-exhaustion-artifacts-") as raw:
        temporary_root = Path(raw)
        temporary_schema_root = temporary_root / "schemas"
        temporary_schema_root.mkdir(parents=True)
        for schema in (ROOT / "schemas").glob("*.schema.json"):
            shutil.copy2(schema, temporary_schema_root / schema.name)
        rendered = run(
            [
                sys.executable,
                str(ROOT / "tools/render_artifacts.py"),
                "--catalog",
                str(catalog_path),
                "--root",
                str(temporary_root),
            ],
            cwd=ROOT,
        )
        if rendered.returncode != 0:
            return False, rendered.stdout + rendered.stderr

        managed = {
            "automation-summary.json",
            "manifest.json",
            "node-index.csv",
            "route-manifest.json",
        }
        expected_root = temporary_root / "generated"
        observed_root = ROOT / "generated"
        expected = {
            path.relative_to(expected_root).as_posix(): path.read_bytes()
            for path in expected_root.rglob("*")
            if path.is_file()
            and (
                path.relative_to(expected_root).parts[0] in {"mermaid", "cytoscape"}
                or path.relative_to(expected_root).as_posix() in managed
            )
        }
        observed = {
            path.relative_to(observed_root).as_posix(): path.read_bytes()
            for path in observed_root.rglob("*")
            if path.is_file()
            and path.name not in {"lean-machines.json", "kernel-verification.json"}
            and path.relative_to(observed_root).parts[0] != "examples"
        }
        if expected == observed:
            return True, ""
        missing = sorted(set(expected) - set(observed))
        stale = sorted(set(observed) - set(expected))
        changed = sorted(
            path for path in set(expected) & set(observed)
            if expected[path] != observed[path]
        )
        return False, (
            f"generated artifact mismatch; missing={missing}, stale={stale}, "
            f"changed={changed}"
        )


def example_catalog_is_fresh(
    catalog_path: Path, temporary_root: Path
) -> tuple[bool, str]:
    """Fresh-export all package descriptors and compare hydrated bytes."""
    raw_root = temporary_root / "raw-examples"
    output_root = temporary_root / "rendered-examples"
    raw_root.mkdir(parents=True, exist_ok=True)
    failures: list[str] = []
    for package_name, (module_path, filename) in EXAMPLE_EXPORTS.items():
        environment = os.environ.copy()
        environment["STRUCTURAL_EXHAUSTION_EXAMPLE_EXPORT"] = str(
            raw_root / filename
        )
        exported = run(
            ["lake", "env", "lean", module_path],
            cwd=EXAMPLE_ROOTS[package_name],
            env=environment,
        )
        if exported.returncode != 0:
            failures.append(
                f"[{package_name}]\n{(exported.stdout + exported.stderr).rstrip()}"
            )
    if failures:
        return False, "\n".join(failures)

    rendered = run(
        [
            sys.executable,
            str(ROOT / "tools/render_example_catalog.py"),
            "--raw-root",
            str(raw_root),
            "--root",
            str(output_root),
            "--source-root",
            str(ROOT),
            "--catalog",
            str(catalog_path),
        ],
        cwd=ROOT,
    )
    if rendered.returncode != 0:
        return False, rendered.stdout + rendered.stderr

    expected = files_below(output_root / "generated/examples", "*")
    observed = files_below(ROOT / "generated/examples", "*")
    if expected == observed:
        return True, ""
    missing = sorted(set(expected) - set(observed))
    stale = sorted(set(observed) - set(expected))
    changed = sorted(
        path
        for path in set(expected) & set(observed)
        if expected[path] != observed[path]
    )
    return False, (
        f"generated example mismatch; missing={missing}, stale={stale}, "
        f"changed={changed}"
    )


def write_result(
    catalog: dict,
    pinned: str,
    observed: str,
    aggregate: dict[str, str],
) -> None:
    success = all(status == "passed" for status in aggregate.values())
    result = {
        "artifactType": "leanKernelVerification",
        "schemaVersion": "2.0.0",
        "status": "kernel_checked" if success else "failed",
        "catalogHash": sha256(CATALOG_PATH),
        "exampleCatalogHash": (
            sha256(EXAMPLE_INDEX_PATH) if EXAMPLE_INDEX_PATH.is_file() else "0" * 64
        ),
        "toolchain": {"pinned": pinned, "observed": observed},
        "aggregate": aggregate,
        "tactics": [
            {
                "tacticId": tactic["tacticId"],
                "status": "kernel_checked" if success else "failed",
                "nodeCount": len(tactic["nodes"]),
                "transitionCount": len(tactic["transitions"]),
                "terminalCount": len(tactic["terminals"]),
            }
            for tactic in catalog["tactics"]
        ],
    }
    RESULT_PATH.parent.mkdir(parents=True, exist_ok=True)
    RESULT_PATH.write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def print_failure(label: str, detail: str) -> None:
    if detail.strip():
        print(f"[{label}]\n{detail.rstrip()}", file=sys.stderr)


def main() -> int:
    lake = shutil.which("lake")
    if lake is None:
        print("lake is unavailable; install elan and the pinned Lean toolchain", file=sys.stderr)
        return 2

    catalog = json.loads(CATALOG_PATH.read_text(encoding="utf-8"))
    pinned = (LEAN_ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    versions = {
        name: run([lake, "env", "lean", "--version"], cwd=package_root)
        for name, package_root in PACKAGE_ROOTS.items()
    }
    observed = (versions["framework"].stdout or versions["framework"].stderr).strip()
    pinned_version = pinned.rsplit(":v", 1)[-1]
    package_pins = {
        name: (package_root / "lean-toolchain").read_text(encoding="utf-8").strip()
        for name, package_root in PACKAGE_ROOTS.items()
    }
    toolchains_aligned = set(package_pins.values()) == {pinned}
    version_ok = toolchains_aligned and all(
        version.returncode == 0
        and f"version {pinned_version}" in (version.stdout or version.stderr)
        for version in versions.values()
    )

    build = run([lake, "build"])
    example_builds = {
        name: run([lake, "build"], cwd=package_root)
        for name, package_root in EXAMPLE_ROOTS.items()
    }
    all_builds_ok = build.returncode == 0 and all(
        result.returncode == 0 for result in example_builds.values()
    )
    admissions = authored_admissions()
    legacy_errors = lint_lean_sources(ROOT)
    schema_errors = json_schema_errors(catalog)
    contract_errors = automation_graph_route_errors(catalog)

    with tempfile.TemporaryDirectory(prefix="structural-exhaustion-verify-") as raw:
        temporary = Path(raw)

        fresh_catalog = temporary / "lean-machines.json"
        export_env = os.environ.copy()
        export_env["STRUCTURAL_EXHAUSTION_EXPORT"] = str(fresh_catalog)
        export = run(
            [lake, "env", "lean", "StructuralExhaustion/Canonical/Export.lean"],
            env=export_env,
        )
        catalog_fresh = (
            export.returncode == 0
            and fresh_catalog.is_file()
            and fresh_catalog.read_bytes() == CATALOG_PATH.read_bytes()
        )

        binding_path = temporary / "AutomationFirstBindingCheck.lean"
        binding_path.write_text(binding_check(catalog), encoding="utf-8")
        binding = run([lake, "env", "lean", str(binding_path)])

        schemas_fresh, schema_freshness_detail = schemas_are_fresh(CATALOG_PATH)
        artifacts_fresh, artifact_freshness_detail = generated_artifacts_are_fresh(
            CATALOG_PATH
        )
        example_catalog_fresh, example_catalog_freshness_detail = (
            example_catalog_is_fresh(
                fresh_catalog if fresh_catalog.is_file() else CATALOG_PATH,
                temporary,
            )
        )

    aggregate = {
        # These four names remain required by kernel-verification.schema.json.
        "build": "passed" if all_builds_ok and version_ok else "failed",
        "frameworkBuild": "passed" if build.returncode == 0 else "failed",
        "evenCycleExampleBuild": (
            "passed" if example_builds["evenCycleExample"].returncode == 0 else "failed"
        ),
        "erdos64ExampleBuild": (
            "passed" if example_builds["erdos64Example"].returncode == 0 else "failed"
        ),
        "greedyColoringExampleBuild": (
            "passed"
            if example_builds["greedyColoringExample"].returncode == 0
            else "failed"
        ),
        "mantelExampleBuild": (
            "passed" if example_builds["mantelExample"].returncode == 0 else "failed"
        ),
        "toolchainAlignment": "passed" if version_ok else "failed",
        "catalogFreshness": "passed" if catalog_fresh else "failed",
        "exampleCatalogFreshness": (
            "passed" if example_catalog_fresh else "failed"
        ),
        "bindingResolution": "passed" if binding.returncode == 0 else "failed",
        "noAdmissions": "passed" if not admissions else "failed",
        # Automation-first verification layers.
        "catalogSchema": "passed" if not schema_errors else "failed",
        "automationGraphRoutes": "passed" if not contract_errors else "failed",
        "schemaFreshness": "passed" if schemas_fresh else "failed",
        "generatedArtifactFreshness": "passed" if artifacts_fresh else "failed",
        "legacyAbsence": "passed" if not legacy_errors else "failed",
    }
    write_result(catalog, pinned, observed, aggregate)

    if all(status == "passed" for status in aggregate.values()):
        node_count = sum(len(tactic["nodes"]) for tactic in catalog["tactics"])
        edge_count = sum(len(tactic["transitions"]) for tactic in catalog["tactics"])
        residual_count = sum(len(tactic["residualKinds"]) for tactic in catalog["tactics"])
        print(
            f"Kernel checked {len(catalog['tactics'])} automation-first tactics, "
            f"{node_count} nodes, {edge_count} typed edges, "
            f"{residual_count} residual kinds, {len(catalog['routes'])} routes, "
            f"and {len(EXAMPLE_EXPORTS)} compiled examples"
        )
        return 0

    if build.returncode != 0:
        print_failure("frameworkBuild", build.stdout + build.stderr)
    for name, result in example_builds.items():
        if result.returncode != 0:
            print_failure(f"{name}Build", result.stdout + result.stderr)
    if not version_ok:
        version_details = "; ".join(
            f"{name}: pin={package_pins[name]}, observed="
            f"{(version.stdout or version.stderr).strip()}"
            for name, version in versions.items()
        )
        print_failure("toolchainAlignment", version_details)
    if not catalog_fresh:
        print_failure("catalogFreshness", export.stdout + export.stderr or "catalog bytes differ")
    if binding.returncode != 0:
        print_failure("bindingResolution", binding.stdout + binding.stderr)
    if admissions:
        print_failure("noAdmissions", ", ".join(admissions))
    if schema_errors:
        print_failure("catalogSchema", "\n".join(schema_errors))
    if contract_errors:
        print_failure("automationGraphRoutes", "\n".join(contract_errors))
    if not schemas_fresh:
        print_failure("schemaFreshness", schema_freshness_detail)
    if not artifacts_fresh:
        print_failure("generatedArtifactFreshness", artifact_freshness_detail)
    if not example_catalog_fresh:
        print_failure("exampleCatalogFreshness", example_catalog_freshness_detail)
    if legacy_errors:
        print_failure("legacyAbsence", "\n".join(legacy_errors))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
