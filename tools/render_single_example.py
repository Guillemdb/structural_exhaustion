#!/usr/bin/env python3
"""Render one trusted raw example without rebuilding unrelated examples.

The normal mode performs a complete hydration.  ``--status-only-existing`` is
the deliberately narrow recovery mode used when an unrelated stale declaration
range prevents full hydration: it copies only the Lean-owned manuscript status
ledger into the already hydrated detail artifact and recomputes its coverage.
"""

from __future__ import annotations

import argparse
import hashlib
import re
from pathlib import Path

TYPED_MATHEMATICAL_LABEL_PATTERN = re.compile(
    r"\\label\[(?:theorem|lemma|proposition|corollary|claim|definition|remark)\]"
    r"\{([^}]+)\}"
)
ENVIRONMENT_MATHEMATICAL_LABEL_PATTERN = re.compile(
    r"\\begin\{(?:theorem|lemma|proposition|corollary|claim|definition|remark)\}"
    r"(?:\[[^\]]*\])?\s*\\label(?:\[[^\]]+\])?\{([^}]+)\}"
)
DIAGRAM_NODE_PATTERN = re.compile(r"\\textbf\{\[([0-9]+)\]\}")

try:
    from tools.render_example_catalog import (
        SCHEMA_ROOT,
        canonical_json_bytes,
        hydrate_example,
        load_json,
        require_schema,
        sha256_bytes,
        validate_detail_semantics,
    )
except ModuleNotFoundError:
    from render_example_catalog import (  # type: ignore[no-redef]
        SCHEMA_ROOT,
        canonical_json_bytes,
        hydrate_example,
        load_json,
        require_schema,
        sha256_bytes,
        validate_detail_semantics,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--raw", type=Path, required=True)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--source-root", type=Path, default=Path("."))
    parser.add_argument("--catalog", type=Path, default=Path("generated/lean-machines.json"))
    parser.add_argument("--status-only-existing", action="store_true")
    args = parser.parse_args()

    raw_artifact = load_json(args.raw)
    require_schema(raw_artifact, SCHEMA_ROOT / "example-catalog-raw.schema.json", str(args.raw))
    examples_root = args.root.resolve() / "generated/examples"
    example_id = raw_artifact["example"]["exampleId"]
    detail_path = examples_root / f"{example_id}.json"
    if args.status_only_existing:
        detail = load_json(detail_path)
        raw_manuscript = raw_artifact["example"].get("manuscript")
        manuscript = detail.get("manuscript")
        if raw_manuscript is None or manuscript is None:
            raise RuntimeError("status-only rendering requires manuscript data")
        formalized_node_ids = raw_manuscript.get("formalizedNodeIds", [])
        node_obligations = raw_manuscript.get("nodeObligations", [])
        if len(formalized_node_ids) != len(set(formalized_node_ids)):
            raise RuntimeError("formalized node IDs are not unique")
        obligation_ids = [item["obligationId"] for item in node_obligations]
        if len(obligation_ids) != len(set(obligation_ids)):
            raise RuntimeError("node obligation IDs are not unique")
        obligations_by_node: dict[int, list[dict[str, object]]] = {}
        for obligation in node_obligations:
            obligations_by_node.setdefault(obligation["nodeId"], []).append(obligation)
        formalized = set(formalized_node_ids)
        for node_id, obligations in obligations_by_node.items():
            all_proved = all(item["status"] == "proved" for item in obligations)
            if all_proved != (node_id in formalized):
                raise RuntimeError(
                    f"node {node_id} green status disagrees with its obligation ledger"
                )
        manuscript["formalizedNodeIds"] = formalized_node_ids
        manuscript["nodeObligations"] = node_obligations
        manuscript["coverage"]["verifiedDiagramNodes"] = len(formalized_node_ids)

        # The recovery synchronizer may also remove obsolete Lean-owned
        # descriptors.  Project those removals into the hydrated artifact
        # without attempting to hydrate any new declaration range.
        raw_workflows = {
            workflow["workflowId"]: workflow
            for workflow in raw_artifact["example"].get("workflows", [])
        }
        for workflow in detail.get("workflows", []):
            raw_workflow = raw_workflows.get(workflow["workflowId"])
            if raw_workflow is None:
                continue
            live_stage_ids = {
                stage["stageId"] for stage in raw_workflow.get("stages", [])
            }
            live_link_ids = {
                link["linkId"] for link in raw_workflow.get("links", [])
            }
            workflow["stages"] = [
                stage for stage in workflow["stages"]
                if stage["stageId"] in live_stage_ids
            ]
            workflow["links"] = [
                link for link in workflow["links"]
                if link["linkId"] in live_link_ids
            ]
        live_step_ids = {
            step["stepId"] for step in raw_manuscript.get("proofSteps", [])
        }
        manuscript["proofSteps"] = [
            step for step in manuscript["proofSteps"]
            if step["stepId"] in live_step_ids
        ]
        referenced_labels = {
            reference["label"]
            for step in manuscript["proofSteps"]
            for reference in step["manuscriptRefs"]
        }

        manuscript_path = args.source_root.resolve() / raw_manuscript["path"]
        manuscript_bytes = manuscript_path.read_bytes()
        manuscript_source = manuscript_bytes.decode("utf-8")
        live_labels = set(re.findall(
            r"\\label(?:\[[^\]]+\])?\{([^}]+)\}", manuscript_source,
        ))
        manuscript["sha256"] = hashlib.sha256(manuscript_bytes).hexdigest()
        manuscript["fragments"] = [
            fragment for fragment in manuscript["fragments"]
            if fragment["label"] in live_labels
            and fragment["label"] in referenced_labels
        ]

        # Status and obligation data in this recovery mode are parsed directly
        # from the Lean descriptor source.  Refresh that exact provenance hash
        # as well; otherwise the backend correctly rejects the newly projected
        # status as belonging to an older descriptor revision.
        descriptor_source = detail.get("sourceOfTruth", {}).get("descriptorSource")
        if isinstance(descriptor_source, dict):
            descriptor_path = args.source_root.resolve() / descriptor_source["path"]
            descriptor_source["sha256"] = hashlib.sha256(
                descriptor_path.read_bytes()
            ).hexdigest()

        explained_declarations: set[str] = set()
        for step in manuscript["proofSteps"]:
            for group in step["declarationGroups"]:
                explained_declarations.update(group["declarationIds"])
        # Status-only recovery updates the existing hydrated page without
        # hydrating new declaration groups.  Keep the declaration table aligned
        # with manuscript explanations; otherwise workflow-only declarations
        # from stale stages violate the detail invariant that every displayed
        # declaration has a manuscript explanation.
        used_declarations = explained_declarations
        detail["declarations"] = [
            declaration for declaration in detail["declarations"]
            if declaration["declarationId"] in used_declarations
        ]
        for workflow in detail.get("workflows", []):
            workflow["stages"] = [
                stage for stage in workflow["stages"]
                if {
                    stage["primaryDeclarationId"],
                    *stage["evidenceDeclarationIds"],
                } <= used_declarations
            ]
            live_stage_ids = {stage["stageId"] for stage in workflow["stages"]}
            workflow["links"] = [
                link for link in workflow["links"]
                if link["sourceStageId"] in live_stage_ids
                and link["targetStageId"] in live_stage_ids
                and {
                    *link["automationDeclarationIds"],
                    *link["evidenceDeclarationIds"],
                } <= used_declarations
            ]
        detail["interfaceBindings"] = [
            binding for binding in detail.get("interfaceBindings", [])
            if {
                binding["problemDeclarationId"],
                binding["frameworkDeclarationId"],
            } <= used_declarations
        ]

        explained = {
            declaration_id
            for step in manuscript["proofSteps"]
            for group in step["declarationGroups"]
            for declaration_id in group["declarationIds"]
        }
        fragment_kinds = {
            fragment["label"]: fragment["environment"]
            for fragment in manuscript["fragments"]
        }
        implemented_steps = [
            step for step in manuscript["proofSteps"]
            if step["status"] == "implemented"
        ]
        verified_objects = {
            reference["label"]
            for step in implemented_steps
            for reference in step["manuscriptRefs"]
            if fragment_kinds.get(reference["label"]) in {
                "theorem", "lemma", "proposition", "corollary",
                "claim", "definition", "remark",
            }
        }
        manuscript["coverage"].update({
            "implementedSteps": len(implemented_steps),
            "totalSteps": len(manuscript["proofSteps"]),
            "explainedDeclarations": len(explained),
            "displayedDeclarations": len(detail["declarations"]),
            "verifiedMathematicalObjects": len(verified_objects),
            "verifiedDiagramNodes": len(formalized_node_ids),
            "totalMathematicalObjects": len(
                set(TYPED_MATHEMATICAL_LABEL_PATTERN.findall(manuscript_source))
                | set(ENVIRONMENT_MATHEMATICAL_LABEL_PATTERN.findall(manuscript_source))
            ),
            "totalDiagramNodes": len(
                {int(value) for value in DIAGRAM_NODE_PATTERN.findall(manuscript_source)}
            ),
            "verifiedWorkflowSteps": len(implemented_steps),
        })
    else:
        detail = hydrate_example(raw_artifact, args.source_root.resolve(), load_json(args.catalog))
    validate_detail_semantics(detail)
    require_schema(detail, SCHEMA_ROOT / "example-detail.schema.json", detail["exampleId"])

    detail_bytes = canonical_json_bytes(detail)
    detail_path.write_bytes(detail_bytes)

    index_path = examples_root / "index.json"
    index = load_json(index_path)
    replacement = {
        "exampleId": detail["exampleId"],
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
        "detailFile": detail_path.name,
        "detailHash": sha256_bytes(detail_bytes),
    }
    index["examples"] = [
        replacement if item["exampleId"] == detail["exampleId"] else item
        for item in index["examples"]
    ]
    require_schema(index, SCHEMA_ROOT / "example-index.schema.json", "example index")
    index_path.write_bytes(canonical_json_bytes(index))
    print(f'rendered {detail["exampleId"]} with {len(detail["manuscript"]["formalizedNodeIds"])} green nodes')


if __name__ == "__main__":
    main()
