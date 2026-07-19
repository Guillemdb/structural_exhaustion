#!/usr/bin/env python3
"""Render one trusted raw example without rebuilding unrelated examples.

The normal mode performs a complete hydration.  ``--status-only-existing`` is
the deliberately narrow recovery mode used when an unrelated stale declaration
range prevents full hydration: it copies only the Lean-owned manuscript status
ledger into the already hydrated detail artifact and recomputes its coverage.
"""

from __future__ import annotations

import argparse
from pathlib import Path

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
