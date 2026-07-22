from __future__ import annotations

import csv
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

from jsonschema import Draft202012Validator

from tools.build_hypostructure_web_data import (
    build_erdos,
    build_snapshot,
    canonical_bytes,
    discover_sources,
    hydrate_content_block,
    markdown_to_safe_html,
)


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_DIR = ROOT / "generated/hypostructure/web"


def build_isolated_erdos(
    tmp_path: Path,
    *,
    node1_updates: dict[str, str],
    compiled_declaration: bool = True,
    stale_olean: bool = False,
) -> dict[str, object]:
    matrix_source = ROOT / "migration/hypostructure/eg-node-matrix.csv"
    with matrix_source.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        fieldnames = list(reader.fieldnames or [])
        rows = list(reader)
    rows[0].update(node1_updates)
    matrix = tmp_path / "migration/hypostructure/eg-node-matrix.csv"
    matrix.parent.mkdir(parents=True)
    with matrix.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)

    source_path = Path(
        "examples/hypostructure_erdos_64_eg/"
        "HypostructureErdos64EG/Node1.lean"
    )
    source = tmp_path / source_path
    source.parent.mkdir(parents=True)
    source.write_text("def node1 : Nat := 1\n", encoding="utf-8")
    olean = (
        tmp_path
        / "examples/hypostructure_erdos_64_eg/.lake/build/lib/lean/"
        "HypostructureErdos64EG/Node1.olean"
    )
    olean.parent.mkdir(parents=True)
    olean.write_bytes(b"compiled node 1")
    source_time = 2_000_000_000_000_000_000
    os.utime(source, ns=(source_time, source_time))
    olean_time = source_time - 1 if stale_olean else source_time
    os.utime(olean, ns=(olean_time, olean_time))

    module = "HypostructureErdos64EG.Node1"
    sources = [{
        "id": "source-node-1",
        "path": source_path.as_posix(),
        "module": module,
    }]
    declarations = (
        [{
            "id": "declaration-node-1",
            "module": module,
            "short_name": "node1",
            "kind": "definition",
            "summary": "Compiled direct node 1 executor.",
            "url": "/reference/declarations/declaration-node-1",
        }]
        if compiled_declaration
        else []
    )
    return build_erdos(tmp_path, sources, declarations)


def test_source_discovery_is_limited_to_native_public_packages() -> None:
    sources, _path_to_id, _module_to_source = discover_sources(ROOT)

    assert len(sources) > 200
    assert all("/.lake/" not in source["path"] for source in sources)
    assert all("/Canonical/" not in source["path"] for source in sources)
    assert all(
        source["path"].startswith(
            (
                "hypostructure/Hypostructure/",
                "examples/hypostructure_erdos_64_eg/",
                "examples/hypostructure_pde/",
            )
        )
        for source in sources
    )


def test_markdown_renderer_allowlist_sanitizes_active_html() -> None:
    rendered = markdown_to_safe_html(
        "A **verified** `Result`.\n\n<script>alert(1)</script>"
        "<img src=x onerror=alert(2)>"
    )

    assert "<strong>verified</strong>" in rendered
    assert "<code>Result</code>" in rendered
    assert "<script>" not in rendered
    assert "<img" not in rendered
    assert "onerror=" not in rendered
    assert "alert(1)" not in rendered


def test_callout_hydration_preserves_structured_items() -> None:
    hydrated = hydrate_content_block({
        "kind": "callout",
        "tone": "warning",
        "title": "Avoid these shapes",
        "items": ["Caller-selected output", "Replaced predecessor"],
    })

    assert hydrated == {
        "kind": "callout",
        "tone": "warning",
        "title": "Avoid these shapes",
        "body": "",
        "items": ["Caller-selected output", "Replaced predecessor"],
    }


def test_documented_lean_snippets_compile_via_stdin() -> None:
    snippets = ROOT / "web/content/snippets"
    for filename in ("quickstart.lean", "graph_quickstart.lean", "pde_quickstart.lean"):
        source = (snippets / filename).read_text(encoding="utf-8")
        completed = subprocess.run(
            ["lake", "env", "lean", "--stdin"],
            cwd=ROOT / "hypostructure",
            input=source,
            text=True,
            capture_output=True,
            check=False,
        )
        assert completed.returncode == 0, (
            f"{filename} did not compile via the documented stdin command:\n"
            f"{completed.stdout}\n{completed.stderr}"
        )


def test_snapshot_is_deterministic_and_page_view_complete() -> None:
    snapshot, sources = build_snapshot(
        ROOT, ARTIFACT_DIR / "declarations.raw.json"
    )
    rebuilt, rebuilt_sources = build_snapshot(
        ROOT, ARTIFACT_DIR / "declarations.raw.json"
    )

    schema = json.loads(
        (ROOT / "web/contracts/snapshot.schema.json").read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    Draft202012Validator(schema).validate(snapshot)
    assert canonical_bytes(snapshot) == canonical_bytes(rebuilt)
    assert sources == rebuilt_sources
    assert "snapshot_hash" not in snapshot
    assert "snapshot" not in snapshot["site"]
    assert set(snapshot["pages"]) == {
        "home", "start", "core", "cts", "routes", "graph", "pde",
        "examples", "erdos", "reference",
    }
    assert [ct["id"] for ct in snapshot["cts"]] == [
        f"CT{index}" for index in range(1, 18)
    ]
    detail_records = [
        *snapshot["cts"], *snapshot["routes"], *snapshot["examples"],
        *snapshot["modules"], *snapshot["declarations"],
        *snapshot["erdos"]["nodes"],
    ]
    assert all(record["id"] and record["title"] and record["summary"] for record in detail_records)
    assert all(isinstance(record["sections"], list) for record in detail_records)
    source_ids = {source["id"] for source in snapshot["sources"]}
    source_links: list[str] = []
    internal_links: list[str] = []

    def collect_links(value: object) -> None:
        if isinstance(value, dict):
            for key, child in value.items():
                if key in {"href", "sourceHref"} and isinstance(child, str):
                    assert not child.startswith("/api/v2/sources/")
                    if child.startswith("/source/"):
                        source_links.append(child)
                    elif child.startswith("/"):
                        internal_links.append(child)
                collect_links(child)
        elif isinstance(value, list):
            for child in value:
                collect_links(child)

    collect_links(snapshot)
    assert source_links
    assert {
        link.split("?", 1)[0].removeprefix("/source/")
        for link in source_links
    } <= source_ids
    internal_paths = {"/search"}
    internal_paths.update(page["canonicalPath"] for page in snapshot["pages"].values())
    for collection in ("cts", "routes", "examples", "modules", "declarations"):
        internal_paths.update(record["canonicalPath"] for record in snapshot[collection])
    internal_paths.update(
        node["canonicalPath"] for node in snapshot["erdos"]["nodes"]
    )
    assert {
        link.split("?", 1)[0].split("#", 1)[0]
        for link in internal_links
    } <= internal_paths
    declaration_paths = {
        declaration["canonicalPath"] for declaration in snapshot["declarations"]
    }
    dependency_hrefs = {
        item["href"]
        for declaration in snapshot["declarations"]
        for section in declaration["sections"]
        if section["id"].endswith("-dependencies")
        for block in section["blocks"]
        for item in block.get("items", [])
    }
    assert dependency_hrefs <= declaration_paths
    assert all(document["kind"] for document in snapshot["search_documents"])
    searchable_declarations = {
        document["title"]
        for document in snapshot["search_documents"]
        if document["kind"] == "declaration"
    }
    assert not any(
        name.endswith((
            ".casesOn", ".recOn", ".noConfusion", ".elim", ".inj",
            ".injEq", ".congr", ".congr_simp", ".ctorElim",
            ".ctorElimType",
        ))
        for name in searchable_declarations
    )
    undocumented = next(
        declaration
        for declaration in snapshot["declarations"]
        if declaration["provenance"] == "compiled_environment"
        and not declaration["docstring"]
    )
    assert undocumented["name"] in undocumented["summary"]
    assert f"`{undocumented['layer']}` layer" in undocumented["summary"]
    documentation = next(
        section
        for section in undocumented["sections"]
        if section["id"].endswith("-documentation")
    )
    assert "No authored docstring is attached" in documentation["blocks"][0]["html"]
    catalog_facts = next(
        section
        for section in undocumented["sections"]
        if section["id"].endswith("-catalog-facts")
    )["blocks"][0]
    recorded_fields = {row["field"]: row["value"] for row in catalog_facts["rows"]}
    assert recorded_fields["Qualified name"] == undocumented["name"]
    assert recorded_fields["Declaration kind"] == undocumented["kind"]
    assert recorded_fields["Module"] == undocumented["module"]
    assert recorded_fields["Layer"] == undocumented["layer"]
    assert "function-arrow token" in recorded_fields["Elaborated signature shape"]
    assert recorded_fields["Source binding"].startswith("hash-verified lines ")

    module = next(
        module
        for module in snapshot["modules"]
        if module["declaration_ids"]
    )
    declaration_cards = next(
        section
        for section in module["sections"]
        if section["id"].endswith("-declarations")
    )["blocks"][0]["items"]
    declarations_by_path = {
        declaration["canonicalPath"]: declaration
        for declaration in snapshot["declarations"]
    }
    assert all(card["href"] in declarations_by_path for card in declaration_cards)
    assert all(
        card["title"] == declarations_by_path[card["href"]]["name"]
        for card in declaration_cards
    )
    assert all("stable declaration link" in card["meta"] for card in declaration_cards)

    serialized_snapshot = canonical_bytes(snapshot).decode("utf-8").casefold()
    assert "content-addressed" not in serialized_snapshot
    assert "hash-verified" in serialized_snapshot
    assert sum(route["executable"] for route in snapshot["routes"]) == 1
    assert all(
        route["execution_evidence"] is not None
        for route in snapshot["routes"]
        if route["executable"]
    )
    start_blocks = [
        block
        for section in snapshot["pages"]["start"]["sections"]
        for block in section["blocks"]
    ]
    quickstart = next(block for block in start_blocks if block["kind"] == "code")
    assert quickstart["language"] == "lean"
    assert quickstart["code"].startswith("import Hypostructure.CT1.Automation")
    assert "def problem : Core.Problem" in quickstart["code"]
    assert "def PublicTarget" in quickstart["code"]
    assert "CT1.execute spec capability previous" in quickstart["code"]
    assert "Core.Residual.Query" in quickstart["code"]
    assert "Routes.Accumulated.register" in quickstart["code"]
    assert "Routes.Accumulated.advance" in quickstart["code"]
    assert "def execute (source : Source)" in quickstart["code"]
    assert "Fixtures.RouteRegistry" not in quickstart["code"]
    assert any(block["kind"] == "cards" for block in start_blocks)

    modules_by_id = {module["id"]: module for module in snapshot["modules"]}
    examples_by_id = {example["id"]: example for example in snapshot["examples"]}
    rooted_return_module = next(
        module
        for module in snapshot["modules"]
        if module["name"] == "Hypostructure.Fixtures.RootedReturn"
    )
    assert rooted_return_module["id"] in examples_by_id["graph-fixtures"]["module_ids"]
    assert rooted_return_module["id"] not in examples_by_id["core-fixtures"]["module_ids"]
    assert modules_by_id[rooted_return_module["id"]]["layer"] == "fixtures"

    for ct in snapshot["cts"]:
        entrypoint_ids = set(ct["api_entrypoint_declaration_ids"])
        assert entrypoint_ids
        assert entrypoint_ids <= set(ct["declaration_ids"])
        api_section = next(
            section for section in ct["sections"]
            if section["id"] == f"{ct['id'].lower()}-api-entrypoints"
        )
        assert any(block["kind"] == "links" and block["items"] for block in api_section["blocks"])

    ct9_document = next(
        document for document in snapshot["search_documents"]
        if document["id"] == "ct:CT9"
    )
    assert "parity" in ct9_document["keywords"]


def test_erdos_uses_the_complete_immutable_paper_topology() -> None:
    snapshot, _sources = build_snapshot(
        ROOT, ARTIFACT_DIR / "declarations.raw.json"
    )
    erdos = snapshot["erdos"]
    nodes = erdos["nodes"]
    edges = erdos["edges"]

    assert [node["number"] for node in nodes] == list(range(1, 158))
    assert len(edges) == 169
    assert erdos["root_node_ids"] == ["node-1"]
    assert erdos["graph"]["edges"] == edges
    assert all(edge["label"] == "direct predecessor" for edge in edges)
    edge_pairs = {(edge["source"], edge["target"]) for edge in edges}
    assert {
        ("node-66", "node-65"),
        ("node-102", "node-89"),
        ("node-59", "node-60"),
        ("node-59", "node-61"),
    } <= edge_pairs

    nodes_by_number = {node["number"]: node for node in nodes}
    assert nodes_by_number[65]["incoming"] == ["node-64", "node-66"]
    assert nodes_by_number[89]["incoming"] == ["node-88", "node-102"]
    root_predecessor_section = next(
        section
        for section in nodes_by_number[1]["sections"]
        if section["id"] == "node-1-predecessors"
    )
    assert root_predecessor_section["blocks"][0]["kind"] == "callout"

    source_pattern = re.compile(r"/Node(\d+)\.lean$")
    source_node_numbers = {
        int(match.group(1))
        for source in snapshot["sources"]
        if "hypostructure_erdos_64_eg" in source["path"]
        if (match := source_pattern.search(source["path"]))
    }
    evidenced_node_numbers = {
        node["number"] for node in nodes if "source_id" in node
    }
    assert evidenced_node_numbers == source_node_numbers
    assert all(
        "source_id" not in node or node["declaration_ids"]
        for node in nodes
    )

    allowed_cts = {f"CT{number}" for number in range(1, 18)}
    assert all(
        set(node["observed_ct_ids"]) <= allowed_cts
        for node in nodes
    )
    for node in nodes:
        if not node["observed_ct_ids"]:
            continue
        capability_section = next(
            section
            for section in node["sections"]
            if section["id"] == f"node-{node['number']}-capabilities"
        )
        assert {
            item["href"]
            for item in capability_section["blocks"][0]["items"]
        } == {
            f"/core/cts/{ct_id.lower()}"
            for ct_id in node["observed_ct_ids"]
        }

    index_sections = [
        section
        for section in snapshot["pages"]["erdos"]["sections"]
        if section["id"].startswith("erdos-node-index-")
    ]
    assert [len(section["blocks"][0]["items"]) for section in index_sections] == [
        25, 9, 12, 10, 8, 13, 8, 24, 15, 20, 13,
    ]

    search_by_id = {
        document["id"]: document for document in snapshot["search_documents"]
    }
    for node in nodes:
        body = search_by_id[f"erdos:{node['id']}"]["body"]
        assert node["normalized_input"] in body
        assert node["normalized_outcomes"] in body
        assert all(
            ct_id in body for ct_id in node["observed_ct_ids"]
        )


def test_erdos_node_1_closure_and_frontier_use_only_direct_native_evidence(
    tmp_path: Path,
) -> None:
    erdos = build_isolated_erdos(
        tmp_path,
        node1_updates={
            "new_kernel": "fresh",
            "parity_status": "not_run",
            "math_status": "closed",
            "work_status": "captured",
            "status": "migrated_closed",
            "blocker": "",
            "web_evidence": "generated/hypostructure/web/snapshot.json",
        },
    )
    nodes = {node["number"]: node for node in erdos["nodes"]}

    assert nodes[1]["closed"] is True
    assert nodes[1]["presentation_status"] == "closed"
    assert nodes[1]["direct_kernel_fresh"] is True
    assert nodes[1]["has_compiled_direct_declaration"] is True
    assert nodes[1]["parity_status"] == "not_run"
    assert nodes[1]["web_evidence"] == "generated/hypostructure/web/snapshot.json"
    assert nodes[2]["presentation_status"] == "frontier"
    assert nodes[2]["incoming"] == ["node-1"]
    graph_kinds = {node["id"]: node["kind"] for node in erdos["graph"]["nodes"]}
    assert graph_kinds["node-1"] == "closed"
    assert graph_kinds["node-2"] == "frontier"


def test_erdos_closed_claim_is_demoted_without_each_direct_evidence_layer(
    tmp_path: Path,
) -> None:
    reviewed = {
        "new_kernel": "fresh",
        "parity_status": "checked",
        "math_status": "closed",
        "work_status": "captured",
        "status": "migrated_closed",
        "blocker": "",
        "web_evidence": "generated/examples/erdos-64.json",
    }
    stale = build_isolated_erdos(
        tmp_path / "stale",
        node1_updates=reviewed,
        stale_olean=True,
    )
    no_declaration = build_isolated_erdos(
        tmp_path / "no-declaration",
        node1_updates=reviewed,
        compiled_declaration=False,
    )
    parity_only = build_isolated_erdos(
        tmp_path / "parity-only",
        node1_updates={**reviewed, "status": "typechecked"},
    )

    for erdos in (stale, no_declaration, parity_only):
        nodes = {node["number"]: node for node in erdos["nodes"]}
        assert nodes[1]["closed"] is False
        assert nodes[1]["presentation_status"] == "implemented"
        assert nodes[2]["presentation_status"] != "frontier"
    assert stale["nodes"][0]["direct_kernel_fresh"] is False
    assert no_declaration["nodes"][0]["has_compiled_direct_declaration"] is False
    assert parity_only["nodes"][0]["parity_status"] == "checked"


def test_erdos_rejects_invalid_reviewed_status_vocabulary(tmp_path: Path) -> None:
    try:
        build_isolated_erdos(
            tmp_path,
            node1_updates={"math_status": "looks_green"},
        )
    except ValueError as error:
        assert str(error) == "invalid math_status for Erdős node 1: 'looks_green'"
    else:
        raise AssertionError("invalid migration evidence vocabulary was accepted")


def test_written_manifest_hash_and_counts_match_snapshot() -> None:
    snapshot_bytes = (ARTIFACT_DIR / "snapshot.json").read_bytes()
    snapshot = json.loads(snapshot_bytes)
    manifest = json.loads((ARTIFACT_DIR / "manifest.json").read_text())

    assert manifest["snapshot_sha256"] == hashlib.sha256(snapshot_bytes).hexdigest()
    assert manifest["schema_version"] == snapshot["schema_version"]
    assert manifest["counts"]["pages"] == len(snapshot["pages"])
    assert manifest["counts"]["sources"] == len(snapshot["sources"])
    assert manifest["counts"]["declarations"] == len(snapshot["declarations"])
    assert all("content" not in source for source in snapshot["sources"])


def test_generated_artifacts_match_versioned_json_contracts() -> None:
    contracts = ROOT / "web/contracts"
    artifacts = {
        "declarations.schema.json": ARTIFACT_DIR / "declarations.raw.json",
        "snapshot.schema.json": ARTIFACT_DIR / "snapshot.json",
        "manifest.schema.json": ARTIFACT_DIR / "manifest.json",
    }

    for schema_name, artifact_path in artifacts.items():
        schema = json.loads((contracts / schema_name).read_text(encoding="utf-8"))
        artifact = json.loads(artifact_path.read_text(encoding="utf-8"))
        Draft202012Validator.check_schema(schema)
        Draft202012Validator(schema).validate(artifact)
