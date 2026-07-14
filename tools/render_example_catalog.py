#!/usr/bin/env python3
"""Hydrate compiled Lean example descriptors into deterministic web artifacts.

Lean owns the example/workflow semantics.  This renderer only normalizes repeated
declaration metadata, embeds trusted source files, validates cross references, and
adds byte-level hashes for freshness checks.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

try:
    from tools.render_manuscript_fragments import (
        ManuscriptRenderError,
        render_manuscript_fragments,
    )
except ModuleNotFoundError:  # Direct execution adds tools/, not the repository root.
    from render_manuscript_fragments import (  # type: ignore[no-redef]
        ManuscriptRenderError,
        render_manuscript_fragments,
    )


ROOT = Path(__file__).resolve().parents[1]
SCHEMA_ROOT = ROOT / "schemas"
EXPECTED_EXAMPLES = {
    "EvenCycleExample": "even-cycle",
    "Erdos64EG": "erdos-64",
    "GreedyColoringExample": "greedy-coloring",
    "MantelExample": "mantel",
}
TRUSTED_MODULE_ROOTS = {
    "StructuralExhaustion": Path("lean"),
    "EvenCycleExample": Path("examples/even_cycle"),
    "Erdos64EG": Path("examples/erdos_64_eg"),
    "GreedyColoringExample": Path("examples/greedy_coloring"),
    "MantelExample": Path("examples/mantel"),
}


class ExampleCatalogError(ValueError):
    """A raw descriptor or hydrated artifact violates the trusted contract."""


def canonical_json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ExampleCatalogError(f"cannot read JSON {path}: {error}") from error
    if not isinstance(value, dict):
        raise ExampleCatalogError(f"{path}: expected a JSON object")
    return value


def schema_errors(value: object, schema_path: Path) -> list[str]:
    schema = load_json(schema_path)
    return [
        f"{'/'.join(map(str, error.absolute_path)) or '<root>'}: {error.message}"
        for error in Draft202012Validator(schema).iter_errors(value)
    ]


def require_schema(value: object, schema_path: Path, label: str) -> None:
    errors = schema_errors(value, schema_path)
    if errors:
        raise ExampleCatalogError(f"{label} schema errors:\n" + "\n".join(errors))


def unique(values: list[str], label: str) -> None:
    seen: set[str] = set()
    duplicates: list[str] = []
    for value in values:
        if value in seen and value not in duplicates:
            duplicates.append(value)
        seen.add(value)
    if duplicates:
        raise ExampleCatalogError(f"duplicate {label}: {duplicates}")


def tactic_sort_key(tactic_id: str) -> tuple[int, str]:
    suffix = tactic_id.removeprefix("CT")
    return (int(suffix), tactic_id)


def trusted_source_path(
    declaration: dict[str, Any], source_root: Path
) -> tuple[str, Path]:
    module = declaration["module"]
    source_file = declaration["sourceFile"]
    expected_source_file = module.replace(".", "/") + ".lean"
    if source_file != expected_source_file:
        raise ExampleCatalogError(
            f"{declaration['name']}: sourceFile {source_file!r} does not match "
            f"compiled module {module!r}"
        )

    matching_roots = [
        prefix
        for prefix in TRUSTED_MODULE_ROOTS
        if module == prefix or module.startswith(prefix + ".")
    ]
    if not matching_roots:
        raise ExampleCatalogError(
            f"{declaration['name']}: module {module!r} is not in a trusted package"
        )
    prefix = max(matching_roots, key=len)
    package_root = (source_root / TRUSTED_MODULE_ROOTS[prefix]).resolve()
    try:
        candidate = (package_root / source_file).resolve(strict=True)
    except OSError as error:
        raise ExampleCatalogError(
            f"{declaration['name']}: source file is unavailable: {source_file}"
        ) from error
    try:
        candidate.relative_to(package_root)
    except ValueError as error:
        raise ExampleCatalogError(
            f"{declaration['name']}: source escapes trusted package root: {source_file}"
        ) from error
    if not candidate.is_file():
        raise ExampleCatalogError(
            f"{declaration['name']}: source is not a regular file: {source_file}"
        )
    try:
        relative = candidate.relative_to(source_root.resolve()).as_posix()
    except ValueError as error:
        raise ExampleCatalogError(
            f"{declaration['name']}: trusted package root escapes repository"
        ) from error
    return relative, candidate


def raw_position_key(position: dict[str, int]) -> tuple[int, int]:
    return position["line"], position["column"]


def validate_declaration_range(
    declaration: dict[str, Any], content: str
) -> None:
    name = declaration["name"]
    lines = content.split("\n")
    declaration_range = declaration["range"]
    selection_range = declaration["selectionRange"]
    for label, value in (
        ("range", declaration_range),
        ("selectionRange", selection_range),
    ):
        start = value["start"]
        end = value["end"]
        if raw_position_key(start) > raw_position_key(end):
            raise ExampleCatalogError(f"{name}: reversed {label}")
        for endpoint_label, endpoint in (("start", start), ("end", end)):
            line = endpoint["line"]
            column = endpoint["column"]
            if line > len(lines):
                raise ExampleCatalogError(
                    f"{name}: {label}.{endpoint_label} line {line} exceeds source"
                )
            if column > len(lines[line - 1]):
                raise ExampleCatalogError(
                    f"{name}: {label}.{endpoint_label} column {column} exceeds line {line}"
                )
    if not (
        raw_position_key(declaration_range["start"])
        <= raw_position_key(selection_range["start"])
        <= raw_position_key(selection_range["end"])
        <= raw_position_key(declaration_range["end"])
    ):
        raise ExampleCatalogError(f"{name}: selectionRange is outside declaration range")


class DetailBuilder:
    def __init__(self, source_root: Path) -> None:
        self.source_root = source_root.resolve()
        self.raw_declarations: dict[str, dict[str, Any]] = {}
        self.declarations: dict[str, dict[str, Any]] = {}
        self.sources: dict[str, dict[str, Any]] = {}

    def add_declaration(self, raw: dict[str, Any]) -> str:
        name = raw["name"]
        previous = self.raw_declarations.get(name)
        if previous is not None:
            if previous != raw:
                raise ExampleCatalogError(
                    f"declaration {name!r} has inconsistent compiled metadata"
                )
            return name

        relative_path, source_path = trusted_source_path(raw, self.source_root)
        source_bytes = source_path.read_bytes()
        try:
            content = source_bytes.decode("utf-8")
        except UnicodeDecodeError as error:
            raise ExampleCatalogError(f"{relative_path}: source is not UTF-8") from error
        validate_declaration_range(raw, content)

        source_id = raw["module"]
        source = {
            "sourceId": source_id,
            "moduleName": raw["module"],
            "path": relative_path,
            "sha256": sha256_bytes(source_bytes),
            "content": content,
        }
        existing_source = self.sources.get(source_id)
        if existing_source is not None and existing_source != source:
            raise ExampleCatalogError(
                f"module {source_id!r} resolves to inconsistent source files"
            )
        self.sources[source_id] = source

        declaration_range = raw["range"]
        selection_range = raw["selectionRange"]
        self.raw_declarations[name] = raw
        self.declarations[name] = {
            "declarationId": name,
            "name": name,
            "kind": raw["kind"],
            "type": raw["type"],
            "sourceId": source_id,
            "startLine": declaration_range["start"]["line"],
            "startColumn": declaration_range["start"]["column"] + 1,
            "endLine": declaration_range["end"]["line"],
            "endColumn": declaration_range["end"]["column"] + 1,
            "selectionStartLine": selection_range["start"]["line"],
            "selectionStartColumn": selection_range["start"]["column"] + 1,
            "selectionEndLine": selection_range["end"]["line"],
            "selectionEndColumn": selection_range["end"]["column"] + 1,
        }
        return name

    def declaration_ids(self, declarations: list[dict[str, Any]]) -> list[str]:
        values = [self.add_declaration(declaration) for declaration in declarations]
        unique(values, "declaration references")
        return values


def hydrate_example(
    raw_artifact: dict[str, Any],
    source_root: Path,
    catalog: dict[str, Any],
) -> dict[str, Any]:
    raw = raw_artifact["example"]
    builder = DetailBuilder(source_root)
    tactic_ids_in_catalog = {tactic["tacticId"] for tactic in catalog["tactics"]}
    routes = {route["routeId"]: route for route in catalog["routes"]}
    residual_owner = {
        residual["residualKindId"]: tactic["tacticId"]
        for tactic in catalog["tactics"]
        for residual in tactic["residualKinds"]
    }

    if raw["proofStatus"] == "complete" and any(
        workflow["completion"] == "partial" for workflow in raw["workflows"]
    ):
        raise ExampleCatalogError(
            f"complete example {raw['exampleId']} contains a partial workflow"
        )

    unique([workflow["workflowId"] for workflow in raw["workflows"]], "workflow IDs")
    workflow_values: list[dict[str, Any]] = []
    stages_by_id: dict[str, tuple[str, dict[str, Any]]] = {}
    link_ids: list[str] = []
    referenced_tactics: set[str] = set()

    for workflow in raw["workflows"]:
        stages: list[dict[str, Any]] = []
        for stage in workflow["stages"]:
            stage_id = stage["stageId"]
            if stage_id in stages_by_id:
                raise ExampleCatalogError(f"duplicate stage ID: {stage_id}")
            tactic_id = stage["tacticId"]
            if tactic_id is not None:
                if tactic_id not in tactic_ids_in_catalog:
                    raise ExampleCatalogError(
                        f"stage {stage_id}: unknown tactic {tactic_id}"
                    )
                referenced_tactics.add(tactic_id)
            normalized_stage = {
                "stageId": stage_id,
                "title": stage["title"],
                "summary": stage["summary"],
                "kind": stage["kind"],
                "primaryDeclarationId": builder.add_declaration(
                    stage["primaryDeclaration"]
                ),
                "evidenceDeclarationIds": builder.declaration_ids(
                    stage["evidenceDeclarations"]
                ),
            }
            if tactic_id is not None:
                normalized_stage["tacticId"] = tactic_id
            stages.append(normalized_stage)
            stages_by_id[stage_id] = (workflow["workflowId"], normalized_stage)

        workflow_stage_ids = {stage["stageId"] for stage in stages}
        workflow_stages = {stage["stageId"]: stage for stage in stages}
        links: list[dict[str, Any]] = []
        for link in workflow["links"]:
            link_ids.append(link["linkId"])
            source_id = link["sourceStageId"]
            target_id = link["targetStageId"]
            if source_id not in workflow_stage_ids or target_id not in workflow_stage_ids:
                raise ExampleCatalogError(
                    f"link {link['linkId']}: endpoints must belong to workflow "
                    f"{workflow['workflowId']}"
                )
            if source_id == target_id:
                raise ExampleCatalogError(f"link {link['linkId']}: self-link is invalid")
            route_id = link["routeId"]
            if link["kind"] == "registeredRoute":
                if route_id is None or route_id not in routes:
                    raise ExampleCatalogError(
                        f"link {link['linkId']}: unknown registered route {route_id!r}"
                    )
                route = routes[route_id]
                source_tactic = workflow_stages[source_id].get("tacticId")
                target_tactic = workflow_stages[target_id].get("tacticId")
                expected_source = residual_owner.get(route["sourceResidualKind"])
                if source_tactic != expected_source or target_tactic != route["targetTacticId"]:
                    raise ExampleCatalogError(
                        f"link {link['linkId']}: route {route_id} expects "
                        f"{expected_source} -> {route['targetTacticId']}, got "
                        f"{source_tactic} -> {target_tactic}"
                    )
            elif route_id is not None:
                raise ExampleCatalogError(
                    f"link {link['linkId']}: only registeredRoute links may name a route"
                )

            automation_ids = builder.declaration_ids(
                link["automationDeclarations"]
            )
            source_tactic = workflow_stages[source_id].get("tacticId")
            target_tactic = workflow_stages[target_id].get("tacticId")
            cross_tactic = (
                source_tactic is not None
                and target_tactic is not None
                and source_tactic != target_tactic
            )
            if cross_tactic and not automation_ids:
                raise ExampleCatalogError(
                    f"link {link['linkId']}: cross-CT transition has no framework automation"
                )
            for declaration_id in automation_ids:
                source_module = builder.declarations[declaration_id]["sourceId"]
                if not source_module.startswith("StructuralExhaustion.") or (
                    source_module.startswith("StructuralExhaustion.Graph.External.")
                ):
                    raise ExampleCatalogError(
                        f"link {link['linkId']}: automation declaration "
                        f"{declaration_id} is not framework-owned"
                    )

            normalized_link = {
                "linkId": link["linkId"],
                "sourceStageId": source_id,
                "targetStageId": target_id,
                "kind": link["kind"],
                "label": link["label"],
                "summary": link["description"],
                "automationDeclarationIds": automation_ids,
                "evidenceDeclarationIds": builder.declaration_ids(
                    link["evidenceDeclarations"]
                ),
            }
            if route_id is not None:
                normalized_link["routeId"] = route_id
            links.append(normalized_link)

        workflow_values.append(
            {
                "workflowId": workflow["workflowId"],
                "title": workflow["title"],
                "summary": workflow["purpose"],
                "purpose": workflow["purpose"],
                "completion": workflow["completion"],
                "stages": stages,
                "links": links,
            }
        )
    unique(link_ids, "link IDs")

    unique(
        [binding["bindingId"] for binding in raw["interfaceBindings"]],
        "interface binding IDs",
    )
    bindings: list[dict[str, Any]] = []
    for binding in raw["interfaceBindings"]:
        stage_id = binding["stageId"]
        if stage_id not in stages_by_id:
            raise ExampleCatalogError(
                f"binding {binding['bindingId']}: unknown stage {stage_id}"
            )
        workflow_id, stage = stages_by_id[stage_id]
        tactic_id = binding["tacticId"]
        if tactic_id not in tactic_ids_in_catalog:
            raise ExampleCatalogError(
                f"binding {binding['bindingId']}: unknown tactic {tactic_id}"
            )
        if stage.get("tacticId") != tactic_id:
            raise ExampleCatalogError(
                f"binding {binding['bindingId']}: tactic disagrees with stage {stage_id}"
            )
        referenced_tactics.add(tactic_id)
        bindings.append(
            {
                "bindingId": binding["bindingId"],
                "workflowId": workflow_id,
                "stageId": stage_id,
                "tacticId": tactic_id,
                "role": binding["role"],
                "summary": binding["description"],
                "problemDeclarationId": builder.add_declaration(
                    binding["problemDeclaration"]
                ),
                "frameworkDeclarationId": builder.add_declaration(
                    binding["frameworkDeclaration"]
                ),
            }
        )

    raw_manuscript = raw["manuscript"]
    manuscript: dict[str, Any] | None = None
    if raw_manuscript is not None:
        proof_steps = raw_manuscript["proofSteps"]
        requested_labels = list(dict.fromkeys(
            reference["label"]
            for step in proof_steps
            for reference in step["manuscriptRefs"]
        ))
        try:
            rendered_manuscript = render_manuscript_fragments(
                path=raw_manuscript["path"],
                source_root=source_root,
                requested_labels=requested_labels,
            )
        except ManuscriptRenderError as error:
            raise ExampleCatalogError(str(error)) from error
        known_labels = set(rendered_manuscript["labels"])
        known_nodes = set(rendered_manuscript["nodeIds"])
        unique([step["stepId"] for step in proof_steps], "proof step IDs")
        mapped_stage_ids = [
            step["stageId"] for step in proof_steps if step["stageId"] is not None
        ]
        unique(mapped_stage_ids, "proof-step stage IDs")
        if set(mapped_stage_ids) != set(stages_by_id):
            missing = sorted(set(stages_by_id) - set(mapped_stage_ids))
            extra = sorted(set(mapped_stage_ids) - set(stages_by_id))
            raise ExampleCatalogError(
                f"manuscript stage coverage mismatch; missing={missing}, extra={extra}"
            )

        bindings_by_stage: dict[str, list[dict[str, Any]]] = {}
        for binding in bindings:
            bindings_by_stage.setdefault(binding["stageId"], []).append(binding)
        inbound_link_evidence: dict[str, set[str]] = {}
        for workflow in workflow_values:
            for link in workflow["links"]:
                inbound_link_evidence.setdefault(link["targetStageId"], set()).update(
                    [
                        *link["automationDeclarationIds"],
                        *link["evidenceDeclarationIds"],
                    ]
                )

        normalized_steps: list[dict[str, Any]] = []
        explained_declarations: set[str] = set()
        displayed_declarations: set[str] = set()
        for step in proof_steps:
            stage_id = step["stageId"]
            if step["status"] == "implemented" and stage_id is None:
                raise ExampleCatalogError(
                    f"implemented proof step {step['stepId']} has no stage"
                )
            if step["status"] != "implemented" and stage_id is not None:
                raise ExampleCatalogError(
                    f"unimplemented proof step {step['stepId']} names stage {stage_id}"
                )

            references: list[dict[str, Any]] = []
            for reference in step["manuscriptRefs"]:
                if reference["label"] not in known_labels:
                    raise ExampleCatalogError(
                        f"proof step {step['stepId']}: unknown manuscript label "
                        f"{reference['label']}"
                    )
                unknown_nodes = set(reference["nodeIds"]) - known_nodes
                if unknown_nodes:
                    raise ExampleCatalogError(
                        f"proof step {step['stepId']}: unknown diagram nodes "
                        f"{sorted(unknown_nodes)}"
                    )
                references.append(
                    {
                        "label": reference["label"],
                        "title": reference["title"],
                        "nodeIds": reference["nodeIds"],
                    }
                )

            unique(
                [group["groupId"] for group in step["declarationGroups"]],
                f"declaration group IDs in {step['stepId']}",
            )
            groups: list[dict[str, Any]] = []
            grouped_ids: list[str] = []
            for group in step["declarationGroups"]:
                declaration_ids = builder.declaration_ids(group["declarations"])
                grouped_ids.extend(declaration_ids)
                groups.append(
                    {
                        "groupId": group["groupId"],
                        "title": group["title"],
                        "role": group["role"],
                        "explanation": group["explanation"],
                        "declarationIds": declaration_ids,
                    }
                )
            unique(grouped_ids, f"classified declarations in {step['stepId']}")

            if stage_id is None:
                if grouped_ids:
                    raise ExampleCatalogError(
                        f"unimplemented proof step {step['stepId']} classifies declarations"
                    )
            else:
                _, stage = stages_by_id[stage_id]
                expected_ids = {
                    stage["primaryDeclarationId"],
                    *stage["evidenceDeclarationIds"],
                }
                for binding in bindings_by_stage.get(stage_id, []):
                    expected_ids.add(binding["problemDeclarationId"])
                    expected_ids.add(binding["frameworkDeclarationId"])
                expected_ids.update(inbound_link_evidence.get(stage_id, set()))
                if set(grouped_ids) != expected_ids:
                    raise ExampleCatalogError(
                        f"proof step {step['stepId']} declaration coverage mismatch; "
                        f"missing={sorted(expected_ids - set(grouped_ids))}, "
                        f"extra={sorted(set(grouped_ids) - expected_ids)}"
                    )
                displayed_declarations.update(expected_ids)
                explained_declarations.update(grouped_ids)

            normalized_step = {
                "stepId": step["stepId"],
                "title": step["title"],
                "plainExplanation": step["plainExplanation"],
                "formalStatement": step["formalStatement"],
                "status": step["status"],
                "correspondence": step["correspondence"],
                "manuscriptRefs": references,
                "declarationGroups": groups,
                "scopeNotes": step["scopeNotes"],
                "workBound": step["workBound"],
            }
            if stage_id is not None:
                normalized_step["stageId"] = stage_id
            normalized_steps.append(normalized_step)

        mathematical_object_labels = set(
            rendered_manuscript["mathematicalObjectLabels"]
        )
        implemented_steps = [
            step for step in normalized_steps if step["status"] == "implemented"
        ]
        verified_mathematical_objects = {
            reference["label"]
            for step in implemented_steps
            for reference in step["manuscriptRefs"]
            if reference["label"] in mathematical_object_labels
        }
        verified_diagram_nodes = {
            node_id
            for step in implemented_steps
            for reference in step["manuscriptRefs"]
            for node_id in reference["nodeIds"]
        }

        manuscript = {
            "title": raw_manuscript["title"],
            "path": raw_manuscript["path"],
            "sha256": rendered_manuscript["sha256"],
            "fragments": rendered_manuscript["fragments"],
            "proofSteps": normalized_steps,
            "coverage": {
                "implementedSteps": len(implemented_steps),
                "totalSteps": len(normalized_steps),
                "explainedDeclarations": len(explained_declarations),
                "displayedDeclarations": len(displayed_declarations),
                "verifiedMathematicalObjects": len(
                    verified_mathematical_objects
                ),
                "totalMathematicalObjects": len(mathematical_object_labels),
                "verifiedDiagramNodes": len(verified_diagram_nodes),
                "totalDiagramNodes": len(rendered_manuscript["nodeIds"]),
                "verifiedWorkflowSteps": len(implemented_steps),
            },
        }

    detail = {
        "artifactType": "structuralExhaustionExample",
        "schemaVersion": "1.4.0",
        "sourceOfTruth": raw_artifact["sourceOfTruth"],
        "exampleId": raw["exampleId"],
        "title": raw["title"],
        "summary": raw["summary"],
        "proofStatus": raw["proofStatus"],
        "tacticIds": sorted(referenced_tactics, key=tactic_sort_key),
        "workflows": workflow_values,
        "interfaceBindings": bindings,
        "manuscript": manuscript,
        "declarations": [builder.declarations[key] for key in sorted(builder.declarations)],
        "sources": [builder.sources[key] for key in sorted(builder.sources)],
    }
    return detail


def validate_detail_semantics(detail: dict[str, Any]) -> None:
    declaration_ids = [item["declarationId"] for item in detail["declarations"]]
    source_ids = [item["sourceId"] for item in detail["sources"]]
    unique(declaration_ids, "hydrated declaration IDs")
    unique(source_ids, "hydrated source IDs")
    declaration_set = set(declaration_ids)
    source_set = set(source_ids)
    for declaration in detail["declarations"]:
        if declaration["sourceId"] not in source_set:
            raise ExampleCatalogError(
                f"declaration {declaration['declarationId']}: unknown source"
            )
    for workflow in detail["workflows"]:
        for stage in workflow["stages"]:
            refs = [stage["primaryDeclarationId"], *stage["evidenceDeclarationIds"]]
            if not set(refs) <= declaration_set:
                raise ExampleCatalogError(f"stage {stage['stageId']}: dangling declaration")
        for link in workflow["links"]:
            if not set(
                [
                    *link["automationDeclarationIds"],
                    *link["evidenceDeclarationIds"],
                ]
            ) <= declaration_set:
                raise ExampleCatalogError(f"link {link['linkId']}: dangling declaration")
    for binding in detail["interfaceBindings"]:
        refs = {
            binding["problemDeclarationId"],
            binding["frameworkDeclarationId"],
        }
        if not refs <= declaration_set:
            raise ExampleCatalogError(
                f"binding {binding['bindingId']}: dangling declaration"
            )
    manuscript = detail["manuscript"]
    if manuscript is not None:
        explained: set[str] = set()
        fragment_kinds = {
            fragment["label"]: fragment["environment"]
            for fragment in manuscript["fragments"]
        }
        verified_objects: set[str] = set()
        verified_nodes: set[int] = set()
        implemented_steps = 0
        for step in manuscript["proofSteps"]:
            if step["status"] == "implemented":
                implemented_steps += 1
                for reference in step["manuscriptRefs"]:
                    if fragment_kinds[reference["label"]] in {
                        "theorem", "lemma", "proposition", "corollary",
                        "claim", "definition", "remark",
                    }:
                        verified_objects.add(reference["label"])
                    verified_nodes.update(reference["nodeIds"])
            for group in step["declarationGroups"]:
                if not set(group["declarationIds"]) <= declaration_set:
                    raise ExampleCatalogError(
                        f"declaration group {group['groupId']}: dangling declaration"
                    )
                explained.update(group["declarationIds"])
        coverage = manuscript["coverage"]
        if coverage["explainedDeclarations"] != len(explained):
            raise ExampleCatalogError("manuscript explained-declaration coverage is stale")
        expected_progress = {
            "implementedSteps": implemented_steps,
            "verifiedMathematicalObjects": len(verified_objects),
            "verifiedDiagramNodes": len(verified_nodes),
            "verifiedWorkflowSteps": implemented_steps,
        }
        if any(coverage[key] != value for key, value in expected_progress.items()):
            raise ExampleCatalogError("manuscript proof-progress coverage is stale")
        if explained != declaration_set:
            raise ExampleCatalogError(
                "manuscript does not explain every declaration exposed by the example"
            )


def render_example_catalog(
    *,
    raw_root: Path,
    output_root: Path,
    source_root: Path,
    catalog_path: Path,
    schema_root: Path = SCHEMA_ROOT,
) -> dict[str, Any]:
    raw_paths = sorted(raw_root.resolve().glob("*.json"))
    if not raw_paths:
        raise ExampleCatalogError(f"no raw example descriptors below {raw_root}")
    raw_schema = schema_root / "example-catalog-raw.schema.json"
    detail_schema = schema_root / "example-detail.schema.json"
    index_schema = schema_root / "example-index.schema.json"
    catalog = load_json(catalog_path)

    raw_artifacts: list[dict[str, Any]] = []
    root_modules: list[str] = []
    example_ids: list[str] = []
    for path in raw_paths:
        raw_artifact = load_json(path)
        require_schema(raw_artifact, raw_schema, path.as_posix())
        source = raw_artifact["sourceOfTruth"]
        root_module = source["rootModule"]
        example_id = raw_artifact["example"]["exampleId"]
        expected_example_id = EXPECTED_EXAMPLES.get(root_module)
        if expected_example_id != example_id:
            raise ExampleCatalogError(
                f"{path}: trusted root module {root_module!r} must export "
                f"example {expected_example_id!r}, not {example_id!r}"
            )
        if not source["descriptor"].startswith(root_module + "."):
            raise ExampleCatalogError(
                f"{path}: descriptor is outside root module {root_module!r}"
            )
        root_modules.append(root_module)
        example_ids.append(example_id)
        raw_artifacts.append(raw_artifact)
    unique(root_modules, "root modules")
    unique(example_ids, "example IDs")
    if set(root_modules) != set(EXPECTED_EXAMPLES):
        raise ExampleCatalogError(
            "raw exports do not cover the trusted example packages; "
            f"expected={sorted(EXPECTED_EXAMPLES)}, observed={sorted(root_modules)}"
        )

    pairs = sorted(
        zip(raw_artifacts, example_ids, strict=True), key=lambda item: item[1]
    )
    examples_root = output_root.resolve() / "generated/examples"
    examples_root.mkdir(parents=True, exist_ok=True)
    expected_paths: set[Path] = set()
    summaries: list[dict[str, Any]] = []
    descriptors: list[dict[str, str]] = []
    for raw_artifact, example_id in pairs:
        detail = hydrate_example(raw_artifact, source_root.resolve(), catalog)
        validate_detail_semantics(detail)
        require_schema(detail, detail_schema, f"example {example_id}")
        detail_bytes = canonical_json_bytes(detail)
        detail_file = f"{example_id}.json"
        detail_path = examples_root / detail_file
        detail_path.write_bytes(detail_bytes)
        expected_paths.add(detail_path)
        summaries.append(
            {
                "exampleId": example_id,
                "title": detail["title"],
                "summary": detail["summary"],
                "proofStatus": detail["proofStatus"],
                "tacticIds": detail["tacticIds"],
                "workflowCount": len(detail["workflows"]),
                "workflows": [
                    {
                        "workflowId": workflow["workflowId"],
                        "title": workflow["title"],
                        "purpose": workflow["purpose"],
                        "completion": workflow["completion"],
                    }
                    for workflow in detail["workflows"]
                ],
                "detailFile": detail_file,
                "detailHash": sha256_bytes(detail_bytes),
            }
        )
        source = raw_artifact["sourceOfTruth"]
        descriptors.append(
            {
                "exampleId": example_id,
                "rootModule": source["rootModule"],
                "descriptor": source["descriptor"],
            }
        )

    index = {
        "artifactType": "structuralExhaustionExampleIndex",
        "schemaVersion": "1.0.0",
        "sourceOfTruth": {
            "kind": "compiledLeanEnvironment",
            "descriptors": descriptors,
        },
        "examples": summaries,
    }
    require_schema(index, index_schema, "example index")
    index_path = examples_root / "index.json"
    index_path.write_bytes(canonical_json_bytes(index))
    expected_paths.add(index_path)

    for path in examples_root.rglob("*"):
        if path.is_file() and path not in expected_paths:
            path.unlink()
    return index


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--raw-root", type=Path, default=Path("build/example-exports")
    )
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--source-root", type=Path, default=Path("."))
    parser.add_argument(
        "--catalog", type=Path, default=Path("generated/lean-machines.json")
    )
    parser.add_argument("--schema-root", type=Path, default=SCHEMA_ROOT)
    args = parser.parse_args()
    try:
        index = render_example_catalog(
            raw_root=args.raw_root,
            output_root=args.root,
            source_root=args.source_root,
            catalog_path=args.catalog,
            schema_root=args.schema_root,
        )
    except ExampleCatalogError as error:
        print(f"example catalog rendering failed: {error}", file=sys.stderr)
        return 1
    print(
        f"Rendered {len(index['examples'])} compiled Lean examples to "
        f"{args.root / 'generated/examples'}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
