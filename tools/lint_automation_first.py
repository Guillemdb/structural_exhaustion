#!/usr/bin/env python3
"""Reject proof injection and legacy CT architecture in canonical Lean sources."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


CT_DIRECTORY = re.compile(r"^CT([1-9]|1[0-7])$")
CT_IMPORT = re.compile(r"^import StructuralExhaustion\.CT([1-9]|1[0-7])(?:\.|$)")
LEGACY_FILENAMES = {
    "Interface.lean",
    "StaticInputs.lean",
    "StaticContract.lean",
}
LEGACY_PATTERNS = {
    "authored node plan": re.compile(r"\b(?:CorePlan|HandoffPlan|PayloadPlan)\b|\bstructure\s+\w*Plan\b"),
    "consumer port": re.compile(r"\bPort\b"),
    "alignment predicate": re.compile(r"\b\w*Aligned\b"),
    "legacy static-input API": re.compile(r"\b(?:staticInputContract|StaticInputContract|Core\.StaticInput)\b"),
    "runtime scope classifier": re.compile(r"\b(?:ScopeReady|ScopeCandidate|scopeDecidable)\b"),
}
ADMISSION_PATTERN = re.compile(
    r"^\s*(?P<kind>sorry|admit|axiom|unsafe)\b", re.MULTILINE
)
AXIOM_DECLARATION_PATTERN = re.compile(
    r"^\s*axiom\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b", re.MULTILINE
)
TRUSTED_EXTERNAL_AXIOMS = {
    Path("lean/StructuralExhaustion/Graph/External/HegdeSandeepShashank.lean"): {
        "p13Free_hasPowerOfTwoCycle"
    }
}
CLASSICAL_NAMESPACE_PATTERN = re.compile(
    r"^\s*(?:open\s+Classical\b|local\s+open\s+Classical\b)",
    re.MULTILINE,
)
WHOLE_SOLVER_FIELD = re.compile(
    r"^\s+(?:solve|run|execute|outcome|result|claim|certificate|residual)\w*\s*:",
    re.MULTILINE | re.IGNORECASE,
)
RETIRED_CONTRACT_PATTERN = re.compile(
    r"\bS-(?:Def|Dich|Comp|Equiv|Rout|Trig)\b"
)
RETIRED_FINITE_API_PATTERN = re.compile(
    r"\bFinitePresentation\b|\buser_finite_presentation\b"
)
RETIRED_GRAPH_API_PATTERN = re.compile(
    r"\bFiniteSimpleGraph\b|\bOrientedEdge\b|\bincidenceCount\b|"
    r"\bdeleteOrientedEdge\b"
)
RETIRED_SURFACES = (
    "ct2_formal_reference",
    "framework/json_schemas",
    "framework/branch_closure_methodology_extended.pdf",
    "schemas/proof-audit.schema.json",
    "structural_exhaustion_automation_first_refactor.md",
)


def lean_files(root: Path) -> list[Path]:
    return sorted((root / "lean/StructuralExhaustion").rglob("*.lean"))


def external_example_files(root: Path) -> list[Path]:
    examples = root / "examples"
    if not examples.is_dir():
        return []
    return sorted(
        path
        for package in examples.iterdir()
        if package.is_dir()
        for path in package.rglob("*.lean")
        if ".lake" not in path.parts
    )


def external_example_modules(root: Path) -> set[str]:
    """Return the public root modules of every external example package."""
    examples = root / "examples"
    if not examples.is_dir():
        return set()
    return {
        path.stem
        for package in examples.iterdir()
        if package.is_dir()
        for path in package.glob("*.lean")
    }


def ct_number(path: Path) -> int | None:
    for part in path.parts:
        match = CT_DIRECTORY.match(part)
        if match:
            return int(match.group(1))
    return None


def untrusted_admissions(relative: Path, text: str) -> list[str]:
    """Return authored admissions not in the exact external-theorem allowlist."""
    allowed_axioms = TRUSTED_EXTERNAL_AXIOMS.get(relative, set())
    violations: list[str] = []
    for match in ADMISSION_PATTERN.finditer(text):
        kind = match.group("kind")
        if kind == "axiom":
            declaration = AXIOM_DECLARATION_PATTERN.match(text, match.start())
            if declaration and declaration.group("name") in allowed_axioms:
                continue
        violations.append(kind)
    return violations


def lint(root: Path) -> list[str]:
    errors: list[str] = []
    source_root = root / "lean/StructuralExhaustion"
    example_modules = external_example_modules(root)

    for relative, expected in TRUSTED_EXTERNAL_AXIOMS.items():
        path = root / relative
        if not path.is_file():
            errors.append(f"{relative}: trusted external theorem module is missing")
            continue
        found = AXIOM_DECLARATION_PATTERN.findall(
            path.read_text(encoding="utf-8")
        )
        if len(found) != len(expected) or set(found) != expected:
            errors.append(
                f"{relative}: expected exactly the trusted external axioms "
                f"{sorted(expected)}, found {found}"
            )

    for relative in RETIRED_SURFACES:
        if (root / relative).exists():
            errors.append(f"{relative}: retired architecture surface remains")

    authored_documents = [
        root / "README.md",
        root / "lean/README.md",
        root / "schemas/README.md",
    ]
    authored_documents.extend((root / "examples").glob("*/README.md"))
    authored_documents.extend((root / "docs").glob("*.md"))
    authored_documents.extend((root / "framework").glob("*.tex"))
    authored_documents.extend((root / "schemas").glob("*.json"))
    for path in authored_documents:
        if path.is_file() and RETIRED_CONTRACT_PATTERN.search(
            path.read_text(encoding="utf-8")
        ):
            errors.append(
                f"{path.relative_to(root)}: contains retired soundness-contract vocabulary"
            )

    for number in range(1, 18):
        directory = source_root / f"CT{number}"
        for required in ("Automation.lean", "Execution.lean", "Graph.lean", "Theorems.lean"):
            if not (directory / required).is_file():
                errors.append(f"CT{number}: missing canonical {required}")
        for legacy in LEGACY_FILENAMES:
            path = directory / legacy
            if path.exists():
                errors.append(f"{path.relative_to(root)}: legacy compatibility file remains")

    for path in lean_files(root):
        relative = path.relative_to(root)
        text = path.read_text(encoding="utf-8")
        number = ct_number(path)

        if untrusted_admissions(relative, text):
            errors.append(f"{relative}: contains an admission or unsafe declaration")
        if CLASSICAL_NAMESPACE_PATTERN.search(text):
            errors.append(f"{relative}: opens the forbidden Classical namespace")
        if RETIRED_CONTRACT_PATTERN.search(text):
            errors.append(f"{relative}: contains retired soundness-contract vocabulary")
        if RETIRED_FINITE_API_PATTERN.search(text):
            errors.append(f"{relative}: contains the retired custom finite API")
        if RETIRED_GRAPH_API_PATTERN.search(text):
            errors.append(f"{relative}: contains the retired custom graph API")

        if number is not None:
            for label, pattern in LEGACY_PATTERNS.items():
                if pattern.search(text):
                    errors.append(f"{relative}: contains {label}")

            for line in text.splitlines():
                match = CT_IMPORT.match(line)
                if match and int(match.group(1)) != number:
                    errors.append(
                        f"{relative}: producer CT{number} imports consumer CT{match.group(1)}"
                    )

            if path.name in {"Capability.lean", "Spec.lean", "Ops.lean"}:
                match = WHOLE_SOLVER_FIELD.search(text)
                if match:
                    field = match.group(0).strip()
                    errors.append(
                        f"{relative}: suspicious whole-result capability field `{field}`"
                    )

        for module in example_modules:
            if re.search(rf"^import\s+{re.escape(module)}(?:\.|$)", text, re.MULTILINE):
                errors.append(
                    f"{relative}: reusable framework imports external example {module}"
                )

    for path in external_example_files(root):
        relative = path.relative_to(root)
        text = path.read_text(encoding="utf-8")
        if untrusted_admissions(relative, text):
            errors.append(f"{relative}: contains an admission or unsafe declaration")
        if CLASSICAL_NAMESPACE_PATTERN.search(text):
            errors.append(f"{relative}: opens the forbidden Classical namespace")
        if RETIRED_CONTRACT_PATTERN.search(text):
            errors.append(f"{relative}: contains retired soundness-contract vocabulary")
        if RETIRED_FINITE_API_PATTERN.search(text):
            errors.append(f"{relative}: contains the retired custom finite API")
        if RETIRED_GRAPH_API_PATTERN.search(text):
            errors.append(f"{relative}: contains the retired custom graph API")
        if "StructuralExhaustion.Examples.EvenCycle" in text:
            errors.append(
                f"{relative}: uses the retired in-framework worked-example namespace"
            )

    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path("."))
    args = parser.parse_args()
    root = args.root.resolve()
    errors = lint(root)
    if errors:
        print("Automation-first architecture violations:")
        for error in errors:
            print(f"- {error}")
        return 1
    print("OK: CT1–CT17 expose only automation-first canonical APIs")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
