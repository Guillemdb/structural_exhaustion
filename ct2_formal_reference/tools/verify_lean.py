#!/usr/bin/env python3
"""Kernel-check CT1 through CT17 and emit one result per semantic graph."""
from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

try:
    from tools.generate_binding_check import load_graph, tactic_instances
except ModuleNotFoundError:
    from generate_binding_check import load_graph, tactic_instances

ROOT = Path(__file__).resolve().parents[1]


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, cwd=ROOT, text=True, capture_output=True)


def version_from_toolchain(toolchain: str) -> str | None:
    match = re.search(r":v([^\s]+)$", toolchain)
    return match.group(1) if match else None


def version_from_lean_output(output: str) -> str | None:
    match = re.search(r"\bversion\s+([^,\s)]+)", output)
    return match.group(1) if match else None


def checked_declaration_types(output: str) -> dict[str, str]:
    """Extract normalized types from Lean's potentially multiline output."""
    header = re.compile(
        r"(?m)^(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)"
        r"(?:\.\{[^}]*\})?(?=\s|:)"
    )
    matches = list(header.finditer(output))
    types: dict[str, str] = {}
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(output)
        rendered = output[match.end():end].strip()
        if rendered.startswith(":"):
            rendered = rendered[1:].strip()
        if rendered:
            types[match.group("name")] = re.sub(r"\s+", " ", rendered)
    return types


def authored_source_has_admission() -> tuple[bool, list[str]]:
    admission_re = re.compile(r"\b(?:sorry|admit|axiom)\b")
    offenders: list[str] = []
    for path in sorted((ROOT / "StructuralExhaustion").rglob("*.lean")):
        if "Generated" in path.parts:
            continue
        source = path.read_text(encoding="utf-8")
        source = re.sub(r"/--.*?-/", "", source, flags=re.S)
        source = re.sub(r"/-.*?-/", "", source, flags=re.S)
        source = re.sub(r"--.*", "", source)
        if admission_re.search(source):
            offenders.append(str(path.relative_to(ROOT)))
    return bool(offenders), offenders


def declaration_result(binding: dict, actual_types: dict[str, str], success: bool) -> dict:
    declaration_ref = binding["ref"]
    declaration = declaration_ref["declaration"]
    source_path = ROOT / declaration_ref["sourceFile"]
    resolved = declaration in actual_types
    return {
        "declaration": declaration,
        "status": "kernel_checked" if success and resolved else "resolved" if resolved else "failed",
        "actualType": actual_types.get(declaration),
        "sourceHash": sha(source_path) if source_path.is_file() else None,
    }


def coverage_resolved(tactic: dict, tactic_id: str, actual_types: dict[str, str]) -> bool:
    instances = {str(path.relative_to(ROOT)): value for path, value in tactic_instances(ROOT, tactic_id)}
    for coverage in tactic["terminalCoverage"]:
        if coverage["mode"] == "parametric_theorem":
            if coverage["theoremRef"]["declaration"] not in actual_types:
                return False
            continue
        instance = instances.get(coverage["instanceRef"])
        if instance is None:
            return False
        refs = [
            *(item["leanRef"] for item in instance["bindings"]),
            instance["executionResultRef"],
            instance["terminalTheoremRef"],
            instance["traceTheoremRef"],
        ]
        if any(item["declaration"] not in actual_types for item in refs):
            return False
    return True


def result_for_tactic(
    tactic_id: str,
    actual_types: dict[str, str],
    pinned_toolchain: str,
    version_output: str,
    toolchain_matches: bool,
    build: subprocess.CompletedProcess[str],
    binding: subprocess.CompletedProcess[str],
    bindings_resolved: bool,
    has_admission: bool,
    admission_files: list[str],
) -> tuple[dict, bool]:
    tactic, nodes = load_graph(ROOT, tactic_id)
    missing_sources = sorted({
        item["ref"]["sourceFile"]
        for node in nodes
        for item in node["leanImplementation"]["declarations"]
        if not (ROOT / item["ref"]["sourceFile"]).is_file()
    })
    node_bindings_resolved = all(
        item["ref"]["declaration"] in actual_types
        for node in nodes
        for item in node["leanImplementation"]["declarations"]
    )
    soundness = tactic["formalApi"].get("soundness", {}).get("declaration")
    totality = tactic["formalApi"].get("totality", {}).get("declaration")
    trace_validity = tactic["formalApi"].get("traceValidity", {}).get("declaration")
    soundness_checked = bool(soundness and soundness in actual_types)
    totality_checked = bool(totality and totality in actual_types)
    trace_validity_checked = bool(trace_validity and trace_validity in actual_types)
    terminal_coverage_checked = coverage_resolved(tactic, tactic_id, actual_types)
    success = all((
        toolchain_matches,
        build.returncode == 0,
        binding.returncode == 0,
        bindings_resolved,
        node_bindings_resolved,
        not missing_sources,
        not has_admission,
        soundness_checked,
        totality_checked,
        trace_validity_checked,
        terminal_coverage_checked,
    ))
    node_results = []
    for node in nodes:
        declarations = [
            declaration_result(item, actual_types, success)
            for item in node["leanImplementation"]["declarations"]
        ]
        node_results.append({
            "nodeId": node["nodeId"],
            "status": "kernel_checked" if success and all(item["status"] == "kernel_checked" for item in declarations) else "failed",
            "declarations": declarations,
        })

    diagnostics: list[str] = []
    if not toolchain_matches:
        diagnostics.append("Lean version does not match lean-toolchain.")
    if build.returncode != 0:
        diagnostics.append("lake build failed:\n" + build.stdout + build.stderr)
    if binding.returncode != 0:
        diagnostics.append("binding check failed:\n" + binding.stdout + binding.stderr)
    elif not bindings_resolved:
        diagnostics.append("One or more generated #check declarations did not resolve.")
    if missing_sources:
        diagnostics.append("Missing referenced Lean sources: " + ", ".join(missing_sources))
    if has_admission:
        diagnostics.append("Authored Lean admissions: " + ", ".join(admission_files))
    missing_aggregates = [
        label
        for label, checked in (
            ("soundness", soundness_checked),
            ("totality", totality_checked),
            ("trace validity", trace_validity_checked),
            ("terminal coverage", terminal_coverage_checked),
        )
        if not checked
    ]
    if missing_aggregates:
        diagnostics.append("Missing aggregate checks: " + ", ".join(missing_aggregates))

    result = {
        "artifactType": "leanVerificationResult",
        "schemaVersion": tactic["schemaVersion"],
        "graphVersion": tactic["graphVersion"],
        "verificationId": f"{tactic_id}.local." + datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "tacticId": tactic_id,
        "status": "kernel_checked" if success else "failed",
        "toolchain": {
            "leanToolchain": pinned_toolchain,
            "lakefileHash": sha(ROOT / "lakefile.toml"),
            "leanVersionObserved": version_output or None,
        },
        "nodeResults": node_results,
        "aggregateResults": {
            "toolchain": "passed" if toolchain_matches else "failed",
            "build": "passed" if build.returncode == 0 else "failed",
            "bindingResolution": "passed" if bindings_resolved else "failed",
            "nodeBindings": "passed" if node_bindings_resolved else "failed",
            "sourceFiles": "passed" if not missing_sources else "failed",
            "noAdmissions": "passed" if not has_admission else "failed",
            "soundness": "passed" if soundness_checked else "failed",
            "totality": "passed" if totality_checked else "failed",
            "traceValidity": "passed" if trace_validity_checked else "failed",
            "terminalCoverage": "passed" if terminal_coverage_checked else "failed",
        },
        "diagnostics": diagnostics,
    }
    return result, success


def main() -> int:
    lake = shutil.which("lake")
    if lake is None:
        print("lake is unavailable; install elan and the pinned toolchain.", file=sys.stderr)
        return 2
    manifest = load(ROOT / "manifest.json")
    tactic_ids = [record["tacticId"] for record in manifest["tactics"]]
    pinned_toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    version_proc = run([lake, "env", "lean", "--version"])
    version_output = (version_proc.stdout or version_proc.stderr).strip()
    toolchain_matches = (
        version_proc.returncode == 0
        and version_from_toolchain(pinned_toolchain) == version_from_lean_output(version_output)
    )
    has_admission, admission_files = authored_source_has_admission()
    build = run([lake, "build"])
    check_path = ROOT / manifest["leanProject"]["bindingCheckRef"]
    binding = run([lake, "env", "lean", str(check_path.relative_to(ROOT))])
    actual_types = checked_declaration_types("\n".join((binding.stdout, binding.stderr)))
    expected = re.findall(
        r"(?m)^#check\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$",
        check_path.read_text(encoding="utf-8"),
    )
    bindings_resolved = binding.returncode == 0 and all(name in actual_types for name in expected)

    all_success = True
    for tactic_id in tactic_ids:
        result, success = result_for_tactic(
            tactic_id, actual_types, pinned_toolchain, version_output,
            toolchain_matches, build, binding, bindings_resolved,
            has_admission, admission_files,
        )
        result_path = ROOT / f"generated/{tactic_id.lower()}-lean-verification.json"
        result_path.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(f"Wrote {result_path.relative_to(ROOT)} with status {result['status']}")
        all_success = all_success and success
    return 0 if all_success else 1


if __name__ == "__main__":
    raise SystemExit(main())
