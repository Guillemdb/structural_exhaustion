#!/usr/bin/env python3
"""Enforce the Hypostructure production import and trust boundaries."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


FRAMEWORK_ROOT = Path("hypostructure/Hypostructure")
FRAMEWORK_MODULE = Path("hypostructure/Hypostructure.lean")
EG_ROOT = Path("examples/hypostructure_erdos_64_eg")
PDE_ROOT = Path("examples/hypostructure_pde")
DEFAULT_ALLOWLIST = Path("migration/hypostructure/trust-allowlist.json")
BUILD_TIME_EXPORTERS = frozenset(
    {Path("hypostructure/Hypostructure/Canonical/WebExport.lean")}
)

LEGACY_MODULE_PREFIXES = (
    "StructuralExhaustion",
    "Erdos64EG",
    "EvenCycleExample",
    "GreedyColoringExample",
    "MantelExample",
)
APPLICATION_MODULES = {
    "eg": "HypostructureErdos64EG",
    "pde": "HypostructurePDEExamples",
    "parity": "HypostructureParity",
}
ALLOWED_EXTERNAL_MODULE_PREFIXES = ("Mathlib",)
APPLICATION_FRAMEWORK_LAYERS = {
    "eg": {"Core", "Graph", "Canonical"},
    "pde": {"Core", "PDE", "Canonical"},
}
CT_LAYER = re.compile(r"CT([1-9]|1[0-7])$")
PUBLIC_CT_MODULES = {"Spec", "Capability", "Automation"}
IGNORED_PATH_PARTS = {".git", ".lake", "build", "node_modules", "__pycache__"}

IMPORT_PATTERN = re.compile(
    r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?P<modules>[^\n]+)",
    re.MULTILINE,
)
MODULE_PATTERN = re.compile(
    r"(?:_root_\.)?[A-Za-z_][A-Za-z0-9_']*"
    r"(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)
FORBIDDEN_KEYWORD_PATTERN = re.compile(
    r"(?<![A-Za-z0-9_'])(?P<kind>sorry|admit|unsafe)(?![A-Za-z0-9_'])"
)
AXIOM_PATTERN = re.compile(
    r"^[ \t]*(?:@\[[^\n]*\][ \t]*(?:\n[ \t]*)?)*"
    r"(?:(?:private|protected|noncomputable|local)[ \t\r\n]+)*"
    r"(?P<kind>axiom|constant)[ \t\r\n]+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b",
    re.MULTILINE,
)
PLURAL_AXIOM_PATTERN = re.compile(
    r"^[ \t]*(?:@\[[^\n]*\][ \t]*(?:\n[ \t]*)?)*"
    r"(?:(?:private|protected|noncomputable|local)[ \t\r\n]+)*"
    r"(?P<kind>axioms|constants)\b",
    re.MULTILINE,
)
NAMESPACE_PATTERN = re.compile(
    r"^[ \t]*namespace[ \t]+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)",
    re.MULTILINE,
)
DECLARATION_PATTERN = re.compile(
    r"^[ \t]*(?:@\[[^\n]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|scoped|local|partial)[ \t]+)*"
    r"(?:def|abbrev|theorem|lemma|structure|class|inductive|opaque|instance)"
    r"[ \t]+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)",
    re.MULTILINE,
)


@dataclass(frozen=True)
class SourceFile:
    path: Path
    relative: Path
    package: str
    layer: str | None = None
    ct_number: int | None = None


@dataclass(frozen=True)
class Import:
    module: str
    line: int


@dataclass(frozen=True)
class AllowedAxiom:
    path: Path
    declaration: str
    source_id: str


def _is_ignored(path: Path) -> bool:
    return any(part in IGNORED_PATH_PARTS for part in path.parts)


def _lean_files(root: Path) -> list[Path]:
    if not root.is_dir():
        return []
    return sorted(path for path in root.rglob("*.lean") if not _is_ignored(path))


def _framework_source(root: Path, path: Path) -> SourceFile:
    relative = path.relative_to(root)
    if relative == FRAMEWORK_MODULE:
        return SourceFile(path, relative, "framework", "root")

    within = relative.relative_to(FRAMEWORK_ROOT)
    first = within.parts[0]
    layer = Path(first).stem
    ct_match = CT_LAYER.fullmatch(layer)
    return SourceFile(
        path,
        relative,
        "framework",
        layer,
        int(ct_match.group(1)) if ct_match else None,
    )


def production_files(root: Path) -> list[SourceFile]:
    """Return every Lean file in a new production package, excluding parity."""
    files: list[SourceFile] = []
    framework_module = root / FRAMEWORK_MODULE
    if framework_module.is_file():
        files.append(_framework_source(root, framework_module))
    files.extend(
        _framework_source(root, path)
        for path in _lean_files(root / FRAMEWORK_ROOT)
    )
    files.extend(
        SourceFile(path, path.relative_to(root), package)
        for package, package_root in (("eg", EG_ROOT), ("pde", PDE_ROOT))
        for path in _lean_files(root / package_root)
    )
    return sorted(files, key=lambda source: source.relative.as_posix())


def legacy_files(root: Path) -> list[Path]:
    """Return frozen legacy Lean sources that must not import Hypostructure."""
    files: set[Path] = set()
    legacy_module = root / "lean/StructuralExhaustion.lean"
    if legacy_module.is_file():
        files.add(legacy_module)
    files.update(_lean_files(root / "lean/StructuralExhaustion"))

    examples = root / "examples"
    if examples.is_dir():
        for package in examples.iterdir():
            if not package.is_dir() or package.name.startswith("hypostructure_"):
                continue
            if package.name == "generated":
                continue
            files.update(_lean_files(package))
    return sorted(files)


def strip_non_code(text: str) -> str:
    """Mask nested comments and strings while preserving source positions."""
    output: list[str] = []
    index = 0
    state = "code"
    block_depth = 0
    while index < len(text):
        char = text[index]
        pair = text[index : index + 2]

        if state == "code":
            if pair == "--":
                output.extend("  ")
                index += 2
                state = "line_comment"
            elif pair == "/-":
                output.extend("  ")
                index += 2
                block_depth = 1
                state = "block_comment"
            elif char == '"':
                output.append(" ")
                index += 1
                state = "string"
            else:
                output.append(char)
                index += 1
            continue

        if state == "line_comment":
            output.append("\n" if char == "\n" else " ")
            index += 1
            if char == "\n":
                state = "code"
            continue

        if state == "block_comment":
            if pair == "/-":
                output.extend("  ")
                index += 2
                block_depth += 1
            elif pair == "-/":
                output.extend("  ")
                index += 2
                block_depth -= 1
                if block_depth == 0:
                    state = "code"
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue

        if state == "string":
            if char == "\\" and index + 1 < len(text):
                output.extend(
                    "\n" if item == "\n" else " "
                    for item in text[index : index + 2]
                )
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
                if char == '"':
                    state = "code"

    return "".join(output)


def _line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def imports(text: str) -> list[Import]:
    result: list[Import] = []
    for match in IMPORT_PATTERN.finditer(text):
        line = _line_number(text, match.start())
        result.extend(
            Import(module.removeprefix("_root_."), line)
            for module in MODULE_PATTERN.findall(match.group("modules"))
        )
    return result


def _has_module_prefix(module: str, prefix: str) -> bool:
    return module == prefix or module.startswith(f"{prefix}.")


def _is_build_time_exporter(source: SourceFile) -> bool:
    """Recognize exact top-level consumers of the compiled Lean environment."""
    return source.relative in BUILD_TIME_EXPORTERS


def _forbidden_name(name: str) -> str | None:
    components = re.split(r"[._]", name)
    lowered = [component.casefold() for component in components]
    if any("handoff" in component for component in lowered):
        return "handoff"
    if any("legacy" in component for component in lowered):
        return "legacy"
    if any("future" in component for component in lowered):
        return "future"
    if any(
        component in {"compat", "compatibility"}
        or (
            component.startswith("compat")
            and not component.startswith("compatible")
        )
        for component in lowered
    ):
        return "compatibility"
    if any(component.endswith("compat") for component in lowered):
        return "compatibility alias"
    return None


def _route_ct_numbers(source: SourceFile) -> set[int]:
    return {
        int(number)
        for part in source.relative.parts
        for number in re.findall(r"CT([1-9]|1[0-7])", part)
    }


def _framework_layer_error(source: SourceFile, module: str) -> str | None:
    if not _has_module_prefix(module, "Hypostructure"):
        return None
    if _is_build_time_exporter(source):
        return None
    if module == "Hypostructure":
        if source.layer == "root":
            return "root module imports itself"
        return "domain inversion: layered source imports the umbrella module"

    parts = module.split(".")
    imported_layer = parts[1]
    imported_ct = CT_LAYER.fullmatch(imported_layer)

    if source.layer == "root":
        return None
    if source.layer == "Core":
        if imported_layer != "Core":
            return f"domain inversion: Core imports {imported_layer}"
        return None
    if source.ct_number is not None:
        if imported_layer == "Core" or imported_layer == f"CT{source.ct_number}":
            return None
        return (
            f"domain inversion: producer CT{source.ct_number} imports "
            f"{imported_layer}"
        )
    if source.layer == "Routes":
        if imported_layer in {"Core", "Routes"}:
            return None
        if imported_ct:
            number = int(imported_ct.group(1))
            route_numbers = _route_ct_numbers(source)
            if number not in route_numbers:
                return (
                    f"route imports CT{number} outside its source/target profile "
                    f"{sorted(route_numbers)}"
                )
            if len(parts) > 2 and parts[2] not in PUBLIC_CT_MODULES:
                return (
                    f"route imports non-public CT{number} module {parts[2]}"
                )
            return None
        return f"domain inversion: Routes imports {imported_layer}"
    if source.layer == "Graph":
        if imported_layer == "Core" or imported_layer == "Graph" or imported_ct:
            return None
        return f"domain inversion: Graph imports {imported_layer}"
    if source.layer == "PDE":
        if imported_layer == "Core" or imported_layer == "PDE" or imported_ct:
            return None
        return f"domain inversion: PDE imports {imported_layer}"
    return None


def _application_layer_error(source: SourceFile, module: str) -> str | None:
    if module == "Hypostructure":
        return None
    imported_layer = module.split(".")[1]
    if CT_LAYER.fullmatch(imported_layer):
        return None
    if imported_layer in APPLICATION_FRAMEWORK_LAYERS[source.package]:
        return None
    if imported_layer == "Routes":
        return (
            f"{source.package} application imports framework Routes directly"
        )
    return (
        f"domain inversion: {source.package} application imports "
        f"{imported_layer} framework layer"
    )


def _import_error(source: SourceFile, module: str) -> str | None:
    for prefix in LEGACY_MODULE_PREFIXES:
        if _has_module_prefix(module, prefix):
            return f"legacy import {module}"

    if any(part.casefold().startswith("generated") for part in module.split(".")):
        return f"generated source import {module}"

    forbidden = _forbidden_name(module)
    if forbidden:
        return f"forbidden {forbidden} import name {module}"

    if _has_module_prefix(module, APPLICATION_MODULES["parity"]):
        return f"production imports parity module {module}"

    if source.package == "framework":
        for package in ("eg", "pde"):
            if _has_module_prefix(module, APPLICATION_MODULES[package]):
                return f"generic framework imports {package} application {module}"
        if _has_module_prefix(module, "Hypostructure"):
            return _framework_layer_error(source, module)
        if _is_build_time_exporter(source) and _has_module_prefix(module, "Lean"):
            return None
        if any(
            _has_module_prefix(module, prefix)
            for prefix in ALLOWED_EXTERNAL_MODULE_PREFIXES
        ):
            return None
        return f"unauthorized external import {module}"

    own_module = APPLICATION_MODULES[source.package]
    if _has_module_prefix(module, own_module):
        return None
    for package in ("eg", "pde"):
        application = APPLICATION_MODULES[package]
        if package != source.package and _has_module_prefix(module, application):
            return (
                f"domain inversion: {source.package} application imports "
                f"{package} application {module}"
            )
    if _has_module_prefix(module, "Hypostructure"):
        return _application_layer_error(source, module)
    if any(
        _has_module_prefix(module, prefix)
        for prefix in ALLOWED_EXTERNAL_MODULE_PREFIXES
    ):
        return None
    return f"unauthorized external import {module}"


def _external_axiom_path(path: Path) -> bool:
    parts = path.parts
    allowed_prefixes = (
        ("hypostructure", "Hypostructure", "Graph", "External"),
        ("hypostructure", "Hypostructure", "PDE", "External"),
    )
    return any(parts[: len(prefix)] == prefix for prefix in allowed_prefixes)


def load_allowlist(path: Path | None) -> tuple[set[AllowedAxiom], list[str]]:
    if path is None or not path.is_file():
        return set(), []
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        return set(), [f"{path}: invalid trust allowlist: {error}"]

    errors: list[str] = []
    if not isinstance(document, dict):
        return set(), [f"{path}: trust allowlist root must be an object"]
    if document.get("schema_version") != 1:
        errors.append(f"{path}: trust allowlist schema_version must be 1")
    raw_entries = document.get("allowed_axioms")
    if not isinstance(raw_entries, list):
        return set(), errors + [f"{path}: allowed_axioms must be a list"]

    entries: set[AllowedAxiom] = set()
    entry_keys: set[tuple[Path, str]] = set()
    for index, raw in enumerate(raw_entries):
        label = f"{path}: allowed_axioms[{index}]"
        if not isinstance(raw, dict):
            errors.append(f"{label} must be an object")
            continue
        raw_path = raw.get("path")
        declaration = raw.get("declaration")
        source_id = raw.get("source_id")
        if not all(
            isinstance(value, str) and value.strip()
            for value in (raw_path, declaration, source_id)
        ):
            errors.append(
                f"{label} requires nonempty path, declaration, and source_id strings"
            )
            continue
        relative = Path(raw_path)
        if relative.is_absolute() or ".." in relative.parts:
            errors.append(f"{label} path must be repository-relative")
            continue
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", declaration):
            errors.append(f"{label} declaration must be an exact local Lean name")
            continue
        entry = AllowedAxiom(relative, declaration, source_id)
        entry_key = (relative, declaration)
        if entry_key in entry_keys:
            errors.append(
                f"{label} duplicates exact axiom key {relative}:{declaration}"
            )
            continue
        if not _external_axiom_path(relative):
            errors.append(
                f"{label} is outside Hypostructure Graph/PDE External"
            )
            continue
        entry_keys.add(entry_key)
        entries.add(entry)
    return entries, errors


def _source_name_errors(source: SourceFile, text: str) -> list[str]:
    errors: list[str] = []
    for component in source.relative.with_suffix("").parts:
        forbidden = _forbidden_name(component)
        if forbidden:
            errors.append(
                f"{source.relative}: forbidden {forbidden} source path component "
                f"{component}"
            )

    for pattern, label in (
        (NAMESPACE_PATTERN, "namespace"),
        (DECLARATION_PATTERN, "declaration"),
    ):
        for match in pattern.finditer(text):
            name = match.group("name")
            forbidden = _forbidden_name(name)
            if forbidden:
                errors.append(
                    f"{source.relative}:{_line_number(text, match.start())}: "
                    f"forbidden {forbidden} {label} name {name}"
                )
    return errors


def _source_admission_errors(
    source: SourceFile,
    text: str,
    allowlist: set[AllowedAxiom],
    seen: dict[tuple[Path, str], int],
) -> list[str]:
    errors: list[str] = []
    for match in FORBIDDEN_KEYWORD_PATTERN.finditer(text):
        errors.append(
            f"{source.relative}:{_line_number(text, match.start())}: "
            f"forbidden {match.group('kind')} admission"
        )
    for match in PLURAL_AXIOM_PATTERN.finditer(text):
        errors.append(
            f"{source.relative}:{_line_number(text, match.start())}: "
            f"plural {match.group('kind')} declarations cannot be allowlisted"
        )
    for match in AXIOM_PATTERN.finditer(text):
        kind = match.group("kind")
        name = match.group("name")
        line = _line_number(text, match.start())
        matching = {
            entry
            for entry in allowlist
            if entry.path == source.relative and entry.declaration == name
        }
        if kind != "axiom":
            errors.append(
                f"{source.relative}:{line}: constant declaration {name} is forbidden; "
                "use a singular audited axiom at an External boundary"
            )
        elif not _external_axiom_path(source.relative):
            errors.append(
                f"{source.relative}:{line}: axiom {name} is outside an External boundary"
            )
        elif not matching:
            errors.append(
                f"{source.relative}:{line}: unauthorized axiom {name}"
            )
        else:
            key = (source.relative, name)
            seen[key] = seen.get(key, 0) + 1
    return errors


def check_repository(
    root: Path,
    *,
    allowlist_path: Path | None = None,
) -> list[str]:
    """Return all Hypostructure import/admission firewall violations."""
    root = root.resolve()
    if allowlist_path is None:
        candidate = root / DEFAULT_ALLOWLIST
        allowlist_path = candidate if candidate.is_file() else None
    elif not allowlist_path.is_absolute():
        allowlist_path = root / allowlist_path

    allowlist, errors = load_allowlist(allowlist_path)
    seen_axioms: dict[tuple[Path, str], int] = {}

    for source in production_files(root):
        raw_text = source.path.read_text(encoding="utf-8")
        text = strip_non_code(raw_text)
        errors.extend(_source_name_errors(source, text))
        errors.extend(_source_admission_errors(source, text, allowlist, seen_axioms))
        for imported in imports(text):
            error = _import_error(source, imported.module)
            if error:
                errors.append(f"{source.relative}:{imported.line}: {error}")

    for entry in allowlist:
        count = seen_axioms.get((entry.path, entry.declaration), 0)
        if count != 1:
            errors.append(
                f"{entry.path}: allowlisted axiom {entry.declaration} "
                f"must occur exactly once; found {count}"
            )

    for path in legacy_files(root):
        relative = path.relative_to(root)
        text = strip_non_code(path.read_text(encoding="utf-8"))
        for imported in imports(text):
            if any(
                _has_module_prefix(imported.module, module)
                for module in APPLICATION_MODULES.values()
            ) or _has_module_prefix(imported.module, "Hypostructure"):
                errors.append(
                    f"{relative}:{imported.line}: legacy production imports "
                    f"Hypostructure module {imported.module}"
                )

    return sorted(set(errors))


def _display_path(root: Path, path: Path | None) -> Path | None:
    if path is None:
        return None
    try:
        return path.resolve().relative_to(root.resolve())
    except ValueError:
        return path


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check Hypostructure import direction and authored admissions."
    )
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument(
        "--allowlist",
        type=Path,
        default=None,
        help=f"trust allowlist (default: {DEFAULT_ALLOWLIST})",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)
    root = args.root.resolve()
    errors = check_repository(root, allowlist_path=args.allowlist)
    if errors:
        print("Hypostructure import/admission firewall violations:")
        for error in errors:
            print(f"- {error}")
        return 1

    allowlist = _display_path(root, args.allowlist)
    suffix = f" using {allowlist}" if allowlist else ""
    print(
        f"OK: Hypostructure firewall passed for "
        f"{len(production_files(root))} production Lean files{suffix}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
