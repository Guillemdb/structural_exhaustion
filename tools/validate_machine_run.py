#!/usr/bin/env python3
"""Validate one JSON execution record against its compiled Lean machine."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from jsonschema import Draft202012Validator
from referencing import Registry, Resource


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CATALOG = ROOT / "generated/lean-machines.json"


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def registry() -> Registry:
    schemas = [
        load(ROOT / "schemas/lean-machine-catalog.schema.json"),
        load(ROOT / "schemas/machine-artifacts.schema.json"),
    ]
    return Registry().with_resources(
        (schema["$id"], Resource.from_contents(schema)) for schema in schemas
    )


def validate_record(record: dict, catalog_path: Path = DEFAULT_CATALOG) -> list[str]:
    errors: list[str] = []
    catalog = load(catalog_path)
    tactic_id = record.get("tacticId")
    tactic = next(
        (item for item in catalog["tactics"] if item["tacticId"] == tactic_id), None
    )
    if tactic is None:
        return [f"unknown tacticId {tactic_id!r}"]

    schema_path = ROOT / f"schemas/generated/runs/{tactic_id}.run.schema.json"
    if not schema_path.is_file():
        return [f"missing concrete run schema {schema_path.relative_to(ROOT)}"]
    schema = load(schema_path)
    for error in sorted(
        Draft202012Validator(schema, registry=registry()).iter_errors(record),
        key=lambda item: list(item.path),
    ):
        location = ".".join(str(part) for part in error.path) or "<root>"
        errors.append(f"{location}: {error.message}")
    if errors:
        return errors

    expected_hash = hashlib.sha256(catalog_path.read_bytes()).hexdigest()
    if record["catalogHash"] != expected_hash:
        errors.append("catalogHash does not match the current compiled Lean catalog")

    entry = next(
        node["nodeId"]
        for node in tactic["nodes"]
        if node["nodeKind"] == "entry"
    )
    if record["startNode"] != entry:
        errors.append(f"run must start at {entry}")

    edges = {edge["edgeId"]: edge for edge in tactic["transitions"]}
    current = entry
    for index, step in enumerate(record["steps"]):
        edge = edges[step["edgeId"]]
        if step["sourceNode"] != current:
            errors.append(
                f"steps.{index}: source {step['sourceNode']} does not continue from {current}"
            )
        if (
            edge["sourceNode"] != step["sourceNode"]
            or edge["targetNode"] != step["targetNode"]
        ):
            errors.append(f"steps.{index}: endpoints differ from compiled Lean edge")
        current = step["targetNode"]

    terminal = next(
        (item for item in tactic["terminals"] if item["case"] == record["terminal"]["case"]),
        None,
    )
    if terminal is None or record["terminal"] != terminal:
        errors.append("terminal record differs from the compiled Lean terminal constructor")
    elif current != terminal["nodeId"]:
        errors.append(
            f"last edge ends at {current}, not terminal node {terminal['nodeId']}"
        )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("record", type=Path, help="JSON leanMachineRun record")
    parser.add_argument("--catalog", type=Path, default=DEFAULT_CATALOG)
    args = parser.parse_args()
    errors = validate_record(load(args.record), args.catalog)
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    print(f"OK: {args.record} is a legal compiled-Lean machine run")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
