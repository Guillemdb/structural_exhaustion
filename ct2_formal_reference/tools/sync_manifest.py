#!/usr/bin/env python3
"""Synchronize the formal-reference manifest with CT1 through CT17 specs."""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TACTIC_IDS = [f"CT{number}" for number in range(1, 18)]


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> int:
    manifest = load(ROOT / "manifest.json")
    tactics = []
    schemas = [item for item in manifest["schemas"] if "/concrete/nodes/" not in item]
    instances: list[str] = []
    generated: list[str] = []
    versions: list[str] = []

    for tactic_id in TACTIC_IDS:
        root = ROOT / "framework" / tactic_id
        tactic = load(root / "tactic.json")
        versions.append(tactic["graphVersion"])
        tactics.append({
            "tacticId": tactic_id,
            "specRef": f"framework/{tactic_id}/tactic.json",
            "contractInventoryRef": f"framework/{tactic_id}/contracts.json",
            "formalizationRef": f"framework/{tactic_id}/formalization.json",
            "nodeDirectory": f"framework/{tactic_id}/nodes",
        })
        schemas.extend(
            f"schemas/concrete/nodes/{Path(node_ref).name.replace('.json', '.schema.json')}"
            for node_ref in tactic["nodeRefs"]
        )
        for coverage in tactic["terminalCoverage"]:
            if coverage["mode"] == "executable_instance":
                ref = coverage["instanceRef"]
                if ref not in instances:
                    instances.append(ref)
        stem = tactic_id.lower()
        generated.extend([
            f"generated/{stem}.cytoscape.json",
            f"generated/{stem}-node-index.csv",
            f"generated/{stem}-lean-verification.json",
        ])

    manifest.update({
        "graphVersion": "+".join(versions),
        "repositoryId": "structural-exhaustion-ct1-ct17-reference",
        "title": "CT1 through CT17 sequential-machine formal reference",
        "tactics": tactics,
        "schemas": schemas,
        "instances": instances,
        "generatedArtifacts": generated,
    })
    (ROOT / "manifest.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(
        f"Synchronized manifest: {len(tactics)} tactics, "
        f"{len(schemas)} schemas, {len(instances)} instances"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
