#!/usr/bin/env python3
"""Render exact JSON Schemas from the compiled automation-first Lean catalog."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


DRAFT = "https://json-schema.org/draft/2020-12/schema"
SCHEMA_ORIGIN = "https://structural-exhaustion.dev/schemas/generated"


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )


def source_annotation(tactic: dict) -> dict:
    return {
        "kind": "compiledLeanEnvironment",
        "catalog": "generated/lean-machines.json",
        "tacticId": tactic["tacticId"],
        "apiVersion": tactic["apiVersion"],
        "namespace": tactic["namespace"],
    }


def node_schema(tactic: dict, node: dict) -> dict:
    return {
        "$schema": DRAFT,
        "$id": f"{SCHEMA_ORIGIN}/nodes/{node['nodeId']}.schema.json",
        "title": f"{node['nodeId']} automation-first node contract",
        "description": (
            "An exact projection of the compiled predecessor-indexed Lean node, "
            "including its proof-instance boundary and framework-generated outputs."
        ),
        "allOf": [
            {"$ref": "../../lean-machine-catalog.schema.json#/$defs/nodeSpec"},
            {"const": node},
        ],
        "x-leanSourceOfTruth": source_annotation(tactic),
        "x-automationContract": node["automation"],
        "x-formalContract": node["formalContract"],
    }


def tactic_schema(tactic: dict) -> dict:
    return {
        "$schema": DRAFT,
        "$id": f"{SCHEMA_ORIGIN}/tactics/{tactic['tacticId']}.schema.json",
        "title": f"{tactic['tacticId']} automation-first Lean tactic",
        "description": (
            "The complete compiled graph, general capability API, specialized "
            "capability profiles, node automation contracts, and semantic residual "
            "inventory for this tactic."
        ),
        "allOf": [
            {"$ref": "../../lean-machine-catalog.schema.json#/$defs/tacticSpec"},
            {"const": tactic},
        ],
        "x-leanSourceOfTruth": source_annotation(tactic),
        "x-capability": tactic["capability"],
        "x-capabilityProfiles": tactic["capabilityProfiles"],
        "x-capabilityConcepts": tactic["capabilityConcepts"],
    }


def residual_schema(tactic: dict, residual: dict) -> dict:
    return {
        "$schema": DRAFT,
        "$id": f"{SCHEMA_ORIGIN}/residuals/{residual['residualKindId']}.schema.json",
        "title": f"{residual['residualKindId']} semantic residual",
        "allOf": [
            {"$ref": "../../lean-machine-catalog.schema.json#/$defs/residualKind"},
            {"const": residual},
        ],
        "x-leanSourceOfTruth": source_annotation(tactic),
    }


def safe_filename(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", value)


def transition_profile_schema(profile: dict) -> dict:
    return {
        "$schema": DRAFT,
        "$id": (
            f"{SCHEMA_ORIGIN}/transition-profiles/"
            f"{safe_filename(profile['profileId'])}.schema.json"
        ),
        "title": f"{profile['profileId']} executable transition profile",
        "allOf": [
            {
                "$ref": (
                    "../../lean-machine-catalog.schema.json"
                    "#/$defs/transitionProfile"
                )
            },
            {"const": profile},
        ],
        "x-leanSourceOfTruth": {
            "kind": "compiledLeanEnvironment",
            "catalog": "generated/lean-machines.json",
            "registry": "StructuralExhaustion.Canonical.transitionProfiles",
        },
    }


def transition_family_schema(family: dict) -> dict:
    return {
        "$schema": DRAFT,
        "$id": (
            f"{SCHEMA_ORIGIN}/transition-families/"
            f"{safe_filename(family['familyId'])}.schema.json"
        ),
        "title": f"{family['familyId']} CT transition family",
        "allOf": [
            {
                "$ref": (
                    "../../lean-machine-catalog.schema.json"
                    "#/$defs/transitionFamily"
                )
            },
            {"const": family},
        ],
        "x-leanSourceOfTruth": {
            "kind": "compiledLeanEnvironment",
            "catalog": "generated/lean-machines.json",
            "registry": "StructuralExhaustion.Canonical.transitionFamilies",
        },
    }


def exact_step_schema(edge: dict) -> dict:
    return {
        "type": "object",
        "additionalProperties": False,
        "required": [
            "edgeOrdinal",
            "edgeId",
            "constructor",
            "edgeType",
            "sourceNode",
            "targetNode",
            "evidenceRef",
        ],
        "properties": {
            "edgeOrdinal": {"const": edge["ordinal"]},
            "edgeId": {"const": edge["edgeId"]},
            "constructor": {"const": edge["constructor"]},
            "edgeType": {"const": edge["constructorType"]},
            "sourceNode": {"const": edge["sourceNode"]},
            "targetNode": {"const": edge["targetNode"]},
            "evidenceRef": {
                "oneOf": [
                    {"type": "null"},
                    {"type": "string", "minLength": 1},
                ]
            },
        },
    }


def exact_terminal_schema(terminal: dict) -> dict:
    return {
        "type": "object",
        "additionalProperties": False,
        "required": ["ordinal", "case", "nodeId", "constructor"],
        "properties": {
            "ordinal": {"const": terminal["ordinal"]},
            "case": {"const": terminal["case"]},
            "nodeId": {"const": terminal["nodeId"]},
            "constructor": {"const": terminal["constructor"]},
        },
    }


def run_schema(tactic: dict) -> dict:
    entry = next(node for node in tactic["nodes"] if node["nodeKind"] == "entry")
    execution_refs = [
        declaration["name"]
        for declaration in tactic["apiDeclarations"]
        if declaration["name"].endswith((".run", ".runCore", ".runReference"))
    ]
    return {
        "$schema": DRAFT,
        "$id": f"{SCHEMA_ORIGIN}/runs/{tactic['tacticId']}.run.schema.json",
        "title": f"{tactic['tacticId']} exact sequential run",
        "allOf": [
            {"$ref": "../../machine-artifacts.schema.json#/$defs/machineRun"},
            {
                "properties": {
                    "tacticId": {"const": tactic["tacticId"]},
                    "apiVersion": {"const": tactic["apiVersion"]},
                    "startNode": {"const": entry["nodeId"]},
                    "executionRef": {"enum": execution_refs},
                    "steps": {
                        "type": "array",
                        "minItems": 1,
                        "items": {
                            "oneOf": [
                                exact_step_schema(edge)
                                for edge in tactic["transitions"]
                            ]
                        },
                    },
                    "terminal": {
                        "oneOf": [
                            exact_terminal_schema(terminal)
                            for terminal in tactic["terminals"]
                        ]
                    },
                },
                "required": [
                    "tacticId",
                    "apiVersion",
                    "startNode",
                    "executionRef",
                    "steps",
                    "terminal",
                ],
            },
        ],
        "x-leanSourceOfTruth": source_annotation(tactic),
    }


def verification_schema(tactic: dict) -> dict:
    return {
        "$schema": DRAFT,
        "$id": (
            f"{SCHEMA_ORIGIN}/verifications/"
            f"{tactic['tacticId']}.verification.schema.json"
        ),
        "title": f"{tactic['tacticId']} kernel-verification summary",
        "allOf": [
            {"$ref": "../../machine-artifacts.schema.json#/$defs/tacticVerification"},
            {
                "properties": {
                    "tacticId": {"const": tactic["tacticId"]},
                    "nodeCount": {"const": len(tactic["nodes"])},
                    "transitionCount": {"const": len(tactic["transitions"])},
                    "terminalCount": {"const": len(tactic["terminals"])},
                    "manualObligationCount": {
                        "const": sum(
                            len(node["automation"]["manualObligations"])
                            for node in tactic["nodes"]
                        )
                    },
                },
                "required": [
                    "tacticId",
                    "nodeCount",
                    "transitionCount",
                    "terminalCount",
                    "manualObligationCount",
                ],
            },
        ],
        "x-leanSourceOfTruth": source_annotation(tactic),
    }


def render_schemas(root: Path, catalog: dict) -> dict:
    generated_root = root / "schemas/generated"
    expected: set[Path] = set()
    tactic_index: list[dict] = []
    transition_family_paths: list[str] = []
    transition_profile_paths: list[str] = []

    for tactic in catalog["tactics"]:
        tactic_id = tactic["tacticId"]
        tactic_path = Path(f"schemas/generated/tactics/{tactic_id}.schema.json")
        run_path = Path(f"schemas/generated/runs/{tactic_id}.run.schema.json")
        verification_path = Path(
            f"schemas/generated/verifications/{tactic_id}.verification.schema.json"
        )
        write_json(root / tactic_path, tactic_schema(tactic))
        write_json(root / run_path, run_schema(tactic))
        write_json(root / verification_path, verification_schema(tactic))
        expected.update({root / tactic_path, root / run_path, root / verification_path})

        node_paths: list[str] = []
        for node in tactic["nodes"]:
            path = Path(f"schemas/generated/nodes/{node['nodeId']}.schema.json")
            write_json(root / path, node_schema(tactic, node))
            expected.add(root / path)
            node_paths.append(path.as_posix())

        residual_paths: list[str] = []
        for residual in tactic["residualKinds"]:
            path = Path(
                "schemas/generated/residuals/"
                f"{residual['residualKindId']}.schema.json"
            )
            write_json(root / path, residual_schema(tactic, residual))
            expected.add(root / path)
            residual_paths.append(path.as_posix())

        tactic_index.append(
            {
                "tacticId": tactic_id,
                "apiVersion": tactic["apiVersion"],
                "tacticSchema": tactic_path.as_posix(),
                "runSchema": run_path.as_posix(),
                "verificationSchema": verification_path.as_posix(),
                "nodeSchemas": node_paths,
                "residualSchemas": residual_paths,
            }
        )

    for family in catalog["transitionFamilies"]:
        path = Path(
            "schemas/generated/transition-families/"
            f"{safe_filename(family['familyId'])}.schema.json"
        )
        write_json(root / path, transition_family_schema(family))
        expected.add(root / path)
        transition_family_paths.append(path.as_posix())

    for profile in catalog["transitionProfiles"]:
        path = Path(
            "schemas/generated/transition-profiles/"
            f"{safe_filename(profile['profileId'])}.schema.json"
        )
        write_json(root / path, transition_profile_schema(profile))
        expected.add(root / path)
        transition_profile_paths.append(path.as_posix())

    index = {
        "artifactType": "leanDerivedSchemaIndex",
        "schemaVersion": "3.0.0",
        "canonicalCatalog": "generated/lean-machines.json",
        "genericSchemas": sorted(
            path.relative_to(root).as_posix()
            for path in (root / "schemas").glob("*.schema.json")
        ),
        "tactics": tactic_index,
        "transitionFamilies": transition_family_paths,
        "transitionProfiles": transition_profile_paths,
    }
    index_path = generated_root / "index.json"
    write_json(index_path, index)
    expected.add(index_path)
    if generated_root.exists():
        for path in generated_root.rglob("*"):
            if path.is_file() and path not in expected:
                path.unlink()
    return index


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--catalog", type=Path, default=Path("generated/lean-machines.json")
    )
    parser.add_argument("--root", type=Path, default=Path("."))
    args = parser.parse_args()
    catalog = json.loads(args.catalog.read_text(encoding="utf-8"))
    index = render_schemas(args.root.resolve(), catalog)
    node_count = sum(len(item["nodeSchemas"]) for item in index["tactics"])
    residual_count = sum(len(item["residualSchemas"]) for item in index["tactics"])
    print(
        f"Rendered {node_count} node, {residual_count} residual, "
        f"{len(index['transitionFamilies'])} transition family, "
        f"{len(index['transitionProfiles'])} transition profile, and "
        f"{3 * len(index['tactics'])} "
        "tactic-level schemas from compiled Lean"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
