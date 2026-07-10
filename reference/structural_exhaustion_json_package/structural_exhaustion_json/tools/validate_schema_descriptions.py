#!/usr/bin/env python3
"""Check that every declared JSON-instance field has a description."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


def property_schemas(value: Any, path: tuple[str, ...] = ()):
    if isinstance(value, dict):
        properties = value.get("properties")
        if isinstance(properties, dict):
            for name, schema in properties.items():
                field_path = (*path, "properties", name)
                yield field_path, schema
        for key, child in value.items():
            yield from property_schemas(child, (*path, key))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from property_schemas(child, (*path, str(index)))


def main(schema_root: str) -> int:
    root = Path(schema_root)
    files = sorted(root.rglob("*.schema.json")) if root.is_dir() else [root]
    errors: list[str] = []
    field_count = 0

    for file in files:
        try:
            schema = json.loads(file.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            errors.append(f"{file}: cannot parse schema: {exc}")
            continue

        for path, field_schema in property_schemas(schema):
            field_count += 1
            description = field_schema.get("description") if isinstance(field_schema, dict) else None
            if not isinstance(description, str) or not description.strip():
                errors.append(f"{file}#/{'/'.join(path)}: missing nonempty description")

    if errors:
        print("\n".join(errors))
        return 1

    print(f"OK: {len(files)} schemas, {field_count} declared fields, 0 missing descriptions")
    return 0


if __name__ == "__main__":
    default = Path(__file__).resolve().parents[1] / "schemas"
    raise SystemExit(main(sys.argv[1] if len(sys.argv) > 1 else str(default)))
