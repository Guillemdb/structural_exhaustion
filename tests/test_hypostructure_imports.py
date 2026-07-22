from __future__ import annotations

import csv
import json
import re
from pathlib import Path

import pytest

from tools.check_hypostructure_imports import check_repository
from tools.update_hypostructure_migration_records import (
    EG_FIELDS,
    ORIGINAL_EG_PREDECESSORS,
    SUPPLEMENTAL_LEGACY_FIELDS,
    update_eg,
    update_supplemental_legacy,
)


ROOT = Path(__file__).resolve().parents[1]
MIGRATION_ROOT = ROOT / "migration/hypostructure"


def write(root: Path, relative: str, text: str) -> Path:
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def write_allowlist(root: Path, entries: list[dict[str, str]]) -> Path:
    path = root / "migration/hypostructure/trust-allowlist.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps({"schema_version": 1, "allowed_axioms": entries}),
        encoding="utf-8",
    )
    return path


def test_current_repository_passes_hypostructure_firewall() -> None:
    assert check_repository(ROOT) == []


def test_comments_and_strings_do_not_create_false_positives(tmp_path: Path) -> None:
    write(
        tmp_path,
        "hypostructure/Hypostructure/Core/Safe.lean",
        """import Mathlib
/- import StructuralExhaustion
   sorry
   unsafe axiom hidden
-/
def warningText := "admit ExactHandoff Legacy Compat"
theorem checked : True := by trivial
#print axioms checked
""",
    )

    assert check_repository(tmp_path) == []


def test_legacy_and_generated_imports_are_rejected(tmp_path: Path) -> None:
    write(
        tmp_path,
        "hypostructure/Hypostructure/Graph/BadImports.lean",
        """import StructuralExhaustion.Core.Problem
import Erdos64EG.Node1
import Hypostructure.Canonical.GeneratedCatalog
""",
    )

    errors = check_repository(tmp_path)
    assert any("legacy import StructuralExhaustion.Core.Problem" in item for item in errors)
    assert any("legacy import Erdos64EG.Node1" in item for item in errors)
    assert any("generated source import" in item for item in errors)


def test_domain_inversions_and_route_internals_are_rejected(tmp_path: Path) -> None:
    sources = {
        "hypostructure/Hypostructure/Core/Inverted.lean": (
            "import Hypostructure.Graph.Object\n"
        ),
        "hypostructure/Hypostructure/CT1/Inverted.lean": (
            "import Hypostructure.CT2.Automation\n"
        ),
        "hypostructure/Hypostructure/Graph/Inverted.lean": (
            "import Hypostructure.PDE.Model\n"
        ),
        "hypostructure/Hypostructure/PDE/Inverted.lean": (
            "import Hypostructure.Graph.Object\n"
        ),
        "hypostructure/Hypostructure/Graph/ApplicationImport.lean": (
            "import HypostructureErdos64EG.Node1\n"
        ),
        "hypostructure/Hypostructure/Routes/CT1ToCT2.lean": (
            "import Hypostructure.CT1.Search\n"
            "import Hypostructure.CT3.Automation\n"
        ),
        "hypostructure/Hypostructure/Core/Unauthorized.lean": (
            "import IndependentFramework.API\n"
        ),
        "examples/hypostructure_erdos_64_eg/"
        "HypostructureErdos64EG/Inverted.lean": (
            "import HypostructurePDEExamples.Model\n"
        ),
        "examples/hypostructure_erdos_64_eg/"
        "HypostructureErdos64EG/PDEInversion.lean": (
            "import Hypostructure.PDE.Model\n"
        ),
        "examples/hypostructure_erdos_64_eg/"
        "HypostructureErdos64EG/RouteImport.lean": (
            "import Hypostructure.Routes.CT1ToCT2\n"
        ),
        "examples/hypostructure_pde/"
        "HypostructurePDEExamples/GraphInversion.lean": (
            "import Hypostructure.Graph.Object\n"
        ),
    }
    for relative, text in sources.items():
        write(tmp_path, relative, text)

    errors = check_repository(tmp_path)
    expected = (
        "Core imports Graph",
        "producer CT1 imports CT2",
        "Graph imports PDE",
        "PDE imports Graph",
        "generic framework imports eg application",
        "route imports non-public CT1 module Search",
        "route imports CT3 outside its source/target profile",
        "unauthorized external import IndependentFramework.API",
        "eg application imports pde application",
        "eg application imports PDE framework layer",
        "eg application imports framework Routes directly",
        "pde application imports Graph framework layer",
    )
    for fragment in expected:
        assert any(fragment in item for item in errors), fragment


def test_exact_web_exporter_may_consume_compiled_environment(
    tmp_path: Path,
) -> None:
    write(
        tmp_path,
        "hypostructure/Hypostructure/Canonical/WebExport.lean",
        """import Hypostructure
import Hypostructure.PDE.NavierStokes
import Lean
""",
    )

    assert check_repository(tmp_path) == []


def test_web_exporter_exception_does_not_leak_to_other_sources(
    tmp_path: Path,
) -> None:
    write(
        tmp_path,
        "hypostructure/Hypostructure/Canonical/OtherExport.lean",
        """import Hypostructure
import Lean
""",
    )
    write(
        tmp_path,
        "hypostructure/Hypostructure/Graph/WebExport.lean",
        """import Hypostructure
import Lean
""",
    )

    errors = check_repository(tmp_path)
    for relative in (
        "hypostructure/Hypostructure/Canonical/OtherExport.lean",
        "hypostructure/Hypostructure/Graph/WebExport.lean",
    ):
        assert any(
            item.startswith(f"{relative}:1:")
            and "layered source imports the umbrella module" in item
            for item in errors
        )
        assert any(
            item.startswith(f"{relative}:2:")
            and "unauthorized external import Lean" in item
            for item in errors
        )


def test_web_exporter_remains_inside_non_generated_trust_boundary(
    tmp_path: Path,
) -> None:
    write(
        tmp_path,
        "hypostructure/Hypostructure/Canonical/WebExport.lean",
        """import Hypostructure.Canonical.GeneratedCatalog
import HypostructureErdos64EG.Node1
import IndependentFramework.API
axiom exporterShortcut : True
""",
    )

    errors = check_repository(tmp_path)
    expected = (
        "generated source import Hypostructure.Canonical.GeneratedCatalog",
        "generic framework imports eg application HypostructureErdos64EG.Node1",
        "unauthorized external import IndependentFramework.API",
        "axiom exporterShortcut is outside an External boundary",
    )
    for fragment in expected:
        assert any(fragment in item for item in errors), fragment


def test_route_may_import_only_its_public_source_and_target_cts(
    tmp_path: Path,
) -> None:
    write(
        tmp_path,
        "hypostructure/Hypostructure/Routes/CT1ToCT2.lean",
        """import Hypostructure.Core.Routing
import Hypostructure.CT1.Automation
import Hypostructure.CT2.Spec
""",
    )

    assert check_repository(tmp_path) == []


def test_applications_may_import_their_own_domain_and_public_cts(
    tmp_path: Path,
) -> None:
    write(
        tmp_path,
        "examples/hypostructure_erdos_64_eg/"
        "HypostructureErdos64EG/Allowed.lean",
        """import Mathlib
import Hypostructure.Core.Context
import Hypostructure.CT1.Automation
import Hypostructure.Graph.Target
import HypostructureErdos64EG.Problem
""",
    )
    write(
        tmp_path,
        "examples/hypostructure_pde/HypostructurePDEExamples/Allowed.lean",
        """import Mathlib
import Hypostructure.Core.Context
import Hypostructure.CT15.Spec
import Hypostructure.PDE.Model
import HypostructurePDEExamples.Problem
""",
    )

    assert check_repository(tmp_path) == []


def test_forbidden_compatibility_and_handoff_names_are_rejected(
    tmp_path: Path,
) -> None:
    write(
        tmp_path,
        "hypostructure/Hypostructure/Core/LegacyBridge.lean",
        "def contextCompatible := True\n",
    )
    write(
        tmp_path,
        "hypostructure/Hypostructure/Core/Bridge.lean",
        (
            "def exactHandoff := True\n"
            "def CompatibilityBridge := True\n"
            "namespace Future\nend Future\n"
        ),
    )
    write(
        tmp_path,
        "hypostructure/Hypostructure/Core/StateCompat.lean",
        "def ordinaryResult := True\n",
    )

    errors = check_repository(tmp_path)
    assert any("forbidden legacy source path component" in item for item in errors)
    assert any("forbidden handoff declaration name exactHandoff" in item for item in errors)
    assert any(
        "forbidden compatibility declaration name CompatibilityBridge" in item
        for item in errors
    )
    assert any("forbidden future namespace name Future" in item for item in errors)
    assert any("forbidden compatibility alias source path" in item for item in errors)
    assert not any("contextCompatible" in item for item in errors)


@pytest.mark.parametrize(
    ("relative", "source", "fragment"),
    [
        (
            "hypostructure/Hypostructure/Core/Sorry.lean",
            "theorem gap : True := by sorry\n",
            "forbidden sorry admission",
        ),
        (
            "hypostructure/Hypostructure/Core/Admit.lean",
            "theorem gap : True := by admit\n",
            "forbidden admit admission",
        ),
        (
            "hypostructure/Hypostructure/Core/Unsafe.lean",
            "unsafe def unchecked : Nat := 0\n",
            "forbidden unsafe admission",
        ),
        (
            "hypostructure/Hypostructure/Graph/External/Unknown.lean",
            "@[simp]\naxiom\nunknownTheorem : True\n",
            "unauthorized axiom unknownTheorem",
        ),
        (
            "hypostructure/Hypostructure/Graph/External/Plural.lean",
            "axioms first second : True\n",
            "plural axioms declarations cannot be allowlisted",
        ),
        (
            "hypostructure/Hypostructure/PDE/External/Constant.lean",
            "constant hiddenInput : True\n",
            "constant declaration hiddenInput is forbidden",
        ),
    ],
)
def test_authored_admission_forms_are_rejected(
    tmp_path: Path,
    relative: str,
    source: str,
    fragment: str,
) -> None:
    write(tmp_path, relative, source)
    assert any(fragment in item for item in check_repository(tmp_path))


def test_exact_external_axiom_allowlist_is_enforced(tmp_path: Path) -> None:
    relative = "hypostructure/Hypostructure/Graph/External/Trusted.lean"
    write(tmp_path, relative, "axiom trustedTheorem : True\n")
    write_allowlist(
        tmp_path,
        [
            {
                "path": relative,
                "declaration": "trustedTheorem",
                "source_id": "paper:trusted-theorem",
            }
        ],
    )

    assert check_repository(tmp_path) == []

    write(
        tmp_path,
        relative,
        "axiom trustedTheorem : True\naxiom widenedTheorem : True\n",
    )
    assert any(
        "unauthorized axiom widenedTheorem" in item
        for item in check_repository(tmp_path)
    )


def test_stale_or_misplaced_allowlist_entries_fail_closed(tmp_path: Path) -> None:
    external = "hypostructure/Hypostructure/PDE/External/Missing.lean"
    write(tmp_path, external, "theorem actual : True := by trivial\n")
    write_allowlist(
        tmp_path,
        [
            {
                "path": external,
                "declaration": "missingTheorem",
                "source_id": "paper:missing-theorem",
            },
            {
                "path": "hypostructure/Hypostructure/Core/Bad.lean",
                "declaration": "badAxiom",
                "source_id": "invalid-boundary",
            },
        ],
    )

    errors = check_repository(tmp_path)
    assert any("must occur exactly once; found 0" in item for item in errors)
    assert any("outside Hypostructure Graph/PDE External" in item for item in errors)


def test_allowlist_rejects_duplicate_exact_axiom_keys(tmp_path: Path) -> None:
    relative = "hypostructure/Hypostructure/Graph/External/Trusted.lean"
    write(tmp_path, relative, "axiom trustedTheorem : True\n")
    write_allowlist(
        tmp_path,
        [
            {
                "path": relative,
                "declaration": "trustedTheorem",
                "source_id": "paper:first-citation",
            },
            {
                "path": relative,
                "declaration": "trustedTheorem",
                "source_id": "paper:second-citation",
            },
        ],
    )

    assert any(
        "duplicates exact axiom key" in item
        for item in check_repository(tmp_path)
    )


def test_legacy_production_cannot_import_hypostructure(tmp_path: Path) -> None:
    write(
        tmp_path,
        "lean/StructuralExhaustion/Frozen.lean",
        "import Hypostructure.Core.Problem\n",
    )

    assert any(
        "legacy production imports Hypostructure module" in item
        for item in check_repository(tmp_path)
    )


def read_csv(name: str) -> list[dict[str, str]]:
    with (MIGRATION_ROOT / name).open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def original_eg_diagram_predecessors() -> dict[int, tuple[int, ...]]:
    source = (ROOT / "original_erdos_64_proof.tex").read_text(encoding="utf-8")
    diagram = source[
        source.index(r"\subsection*{Proof-dependency diagram}") : source.index(
            r"\subsection*{Detailed dependency table}"
        )
    ]
    blocks = re.findall(
        r"\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}",
        diagram,
        flags=re.DOTALL,
    )
    predecessors = {node_id: set() for node_id in range(1, 158)}
    seen_nodes: set[int] = set()

    for block in blocks:
        aliases = {
            alias: int(node_id)
            for alias, node_id in re.findall(
                r"\\node\[[^\]]+\]\s*\((\w+)\).*?"
                r"\\textbf\{\[(\d+)\]\}",
                block,
            )
        }
        seen_nodes.update(aliases.values())
        for arrow in re.findall(
            r"\\draw\[arrow(?:,[^\]]*)?\](.*?);", block, flags=re.DOTALL
        ):
            path_aliases = [
                alias
                for alias in re.findall(r"\((\w+)(?:\.[^)]+)?\)", arrow)
                if alias in aliases
            ]
            assert len(path_aliases) >= 2
            source_node = aliases[path_aliases[0]]
            target_node = aliases[path_aliases[-1]]
            predecessors[target_node].add(source_node)

    # The original captions identify these cross-panel continuation inputs.
    continuations = {
        26: {25},
        35: {33},
        47: {34},
        57: {56},
        65: {64},
        66: {108},
        78: {68},
        86: {63},
        110: {77, 109},
        125: {20},
        145: {24},
    }
    for node_id, incoming in continuations.items():
        predecessors[node_id].update(incoming)

    assert len(blocks) == 11
    assert seen_nodes == set(range(1, 158))
    return {
        node_id: tuple(sorted(incoming))
        for node_id, incoming in predecessors.items()
    }


def test_migrated_node6_split_uses_original_source_topology() -> None:
    source_root = (
        ROOT
        / "examples/hypostructure_erdos_64_eg/HypostructureErdos64EG"
    )
    node7 = (source_root / "Node7.lean").read_text(encoding="utf-8")
    node8 = (source_root / "Node8.lean").read_text(encoding="utf-8")

    assert "import HypostructureErdos64EG.Node6" in node7
    assert "import HypostructureErdos64EG.Node6" in node8
    assert "import HypostructureErdos64EG.Node7" not in node8
    assert "Node7Stage" not in node7
    assert "Node7Focus" not in node7
    assert "Node6AvoidingStage" in node8


def test_api_feature_matrix_has_required_owners_and_statuses() -> None:
    rows = read_csv("api-feature-matrix.csv")
    expected_header = [
        "feature_id",
        "owner",
        "spec_section",
        "legacy_sources",
        "new_module",
        "first_graph_consumer",
        "first_pde_consumer",
        "fixtures",
        "status",
        "notes",
    ]
    assert list(rows[0]) == expected_header
    assert len({row["feature_id"] for row in rows}) == len(rows)
    feature_ids = {row["feature_id"] for row in rows}
    assert {f"ct.ct{number}" for number in range(1, 18)} <= feature_ids
    assert {f"graph.ct{number}" for number in range(1, 18)} <= feature_ids
    assert {
        "routes.registry",
        "route.ct1-to-ct2",
        "route.ct1-to-ct12",
        "route.ct2-to-ct3",
        "route.ct2-to-ct10",
        "route.ct5-to-ct14",
        "route.ct6-to-ct9",
        "route.ct9-to-ct7",
        "route.ct14-refinement",
    } <= feature_ids
    assert {"Core", "CT", "Routes", "Graph", "PDE"} <= {
        row["owner"] for row in rows
    }
    assert {row["status"] for row in rows} <= {
        "planned",
        "specified",
        "implemented",
        "kernel_checked",
        "integration_checked",
        "cutover",
    }


def test_eg_node_matrix_covers_exact_original_authority_topology() -> None:
    rows = read_csv("eg-node-matrix.csv")
    assert list(rows[0]) == EG_FIELDS
    assert {int(row["node_id"]) for row in rows} == set(range(1, 158))
    assert len({row["node_id"] for row in rows}) == len(rows)
    assert {row["status"] for row in rows} <= {
        "inventoried",
        "scaffolded",
        "typechecked",
        "parity_checked",
        "migrated_open",
        "migrated_closed",
        "published",
        "cutover",
    }
    assert all(row["paper_ref"] for row in rows)
    assert all(
        not row["legacy_files"]
        for row in rows
        if 65 <= int(row["node_id"]) <= 144
    )

    by_id = {int(row["node_id"]): row for row in rows}
    reviewed_fresh = {
        "typechecked",
        "parity_checked",
        "migrated_open",
        "migrated_closed",
        "published",
        "cutover",
    }
    for row in rows:
        if row["new_kernel"] == "fresh":
            assert row["status"] in reviewed_fresh
        elif row["new_kernel"] == "stale":
            assert row["status"] == "scaffolded"
        else:
            assert row["status"] == "inventoried"
    assert set(ORIGINAL_EG_PREDECESSORS) == set(range(1, 158))
    assert ORIGINAL_EG_PREDECESSORS == original_eg_diagram_predecessors()
    for node_id, predecessors in ORIGINAL_EG_PREDECESSORS.items():
        assert by_id[node_id]["direct_predecessors"] == "|".join(
            map(str, predecessors)
        )

    # These are intentional original/source-import divergences and guard
    # against silently restoring source-derived topology.
    expected_divergences = {
        4: "2",
        8: "6",
        17: "15",
        21: "19",
        24: "22",
        34: "32",
        35: "33",
        38: "36",
        40: "38",
        43: "41",
        47: "34",
        53: "50",
        54: "52|53",
        55: "53",
        61: "59",
        63: "62",
        65: "64|66",
        66: "108",
        89: "88|102",
        110: "77|109",
        137: "131|136",
        144: "140|142|143",
        157: "154",
    }
    assert {
        node_id: by_id[node_id]["direct_predecessors"]
        for node_id in expected_divergences
    } == expected_divergences

    # Preserve reviewed local obligations independently of parity.
    assert by_id[3]["math_status"] == "closed"
    assert by_id[3]["work_status"] == "captured"
    assert by_id[3]["web_evidence"] == ""
    assert by_id[3]["parity_status"] == "not_run"
    assert by_id[3]["status"] == "typechecked"
    assert by_id[3]["blocker"] == "semantic parity baseline not frozen"

    reviewed_prefix_features = {
        4: "core.focus-selection-work|core.progress|graph.progress",
        5: "core.focus-selection-work|graph.rooted-return",
        6: (
            "core.focus-selection-work|ct.ct1|graph.ct1|"
            "graph.rooted-return"
        ),
        7: "core.closure|ct.ct1|graph.ct1|graph.rooted-return",
        8: (
            "core.focus-selection-work|core.progress|"
            "graph.proper-subgraph-minimality"
        ),
        9: "core.focus-selection-work|graph.deletion-criticality",
        10: "core.focus-selection-work|graph.deletion-criticality",
    }
    for node_id, required_features in reviewed_prefix_features.items():
        assert by_id[node_id]["required_features"] == required_features
        assert by_id[node_id]["math_status"] == "closed"
        assert by_id[node_id]["work_status"] == "captured"
        assert by_id[node_id]["web_evidence"] == ""
        assert by_id[node_id]["parity_status"] == "not_run"
        assert by_id[node_id]["status"] == "typechecked"
        assert by_id[node_id]["blocker"] == (
            "semantic parity baseline not frozen"
        )

    assert by_id[4]["direct_predecessors"] == "2"
    assert by_id[5]["observed_legacy_ct_ids"] == ""
    assert by_id[6]["observed_legacy_ct_ids"] == "CT1"
    assert by_id[7]["observed_legacy_ct_ids"] == ""
    assert by_id[8]["observed_legacy_ct_ids"] == "CT1"
    for node_id in (9, 10):
        assert by_id[node_id]["observed_legacy_ct_ids"] == ""

    assert by_id[11]["math_status"] == "closed"
    assert by_id[11]["work_status"] == "captured"
    assert by_id[11]["web_evidence"] == ""
    assert by_id[11]["parity_status"] == "not_run"
    assert by_id[11]["status"] == "typechecked"
    assert by_id[11]["blocker"] == "semantic parity baseline not frozen"

    assert by_id[12]["observed_legacy_ct_ids"] == ""
    assert by_id[12]["required_features"] == (
        "core.proof-projection|graph.atom-response-coordinates|"
        "graph.boundaried-atom-profile"
    )
    assert by_id[12]["math_status"] == "closed"
    assert by_id[12]["work_status"] == "captured"
    assert by_id[12]["web_evidence"] == ""
    assert by_id[12]["parity_status"] == "not_run"
    assert by_id[12]["status"] == "typechecked"
    assert by_id[12]["blocker"] == "semantic parity baseline not frozen"

    assert by_id[13]["math_status"] == "open"
    assert by_id[13]["web_evidence"] == ""
    assert by_id[13]["status"] == "inventoried"
    assert by_id[13]["blocker"] == (
        "original Node 13 boundary-overlap implication is false under "
        "stated union gluing; explicit correction required"
    )


def test_supplemental_legacy_inventory_is_not_a_paper_status_ledger() -> None:
    rows = read_csv("supplemental-legacy-evidence.csv")
    assert list(rows[0]) == SUPPLEMENTAL_LEGACY_FIELDS
    assert [int(row["legacy_node_id"]) for row in rows] == list(
        range(158, 165)
    )
    assert len({row["legacy_node_id"] for row in rows}) == len(rows)
    assert {
        int(row["legacy_node_id"]): row["observed_imports"] for row in rows
    } == {
        158: "157",
        159: "158",
        160: "159",
        161: "160",
        162: "160",
        163: "161",
        164: "163",
    }
    assert {
        int(row["legacy_node_id"]): row["observed_ct_ids"] for row in rows
    } == {
        158: "",
        159: "CT3",
        160: "CT3",
        161: "",
        162: "CT3",
        163: "CT3",
        164: "CT3",
    }
    assert all("excluded from the original EG DAG" in row["notes"] for row in rows)
    assert "status" not in rows[0]
    assert "direct_predecessors" not in rows[0]
    assert "parity_status" not in rows[0]
    assert "math_status" not in rows[0]


def test_eg_updater_never_derives_paper_edges_from_legacy_imports(
    tmp_path: Path,
) -> None:
    write(
        tmp_path,
        "examples/erdos_64_eg/Erdos64EG/Node4.lean",
        "import Erdos64EG.Node3\n",
    )
    write(
        tmp_path,
        "examples/erdos_64_eg/Erdos64EG/Node8.lean",
        "import Erdos64EG.Node7\n",
    )
    write(
        tmp_path,
        "examples/erdos_64_eg/Erdos64EG/Node158.lean",
        "import Erdos64EG.Node157\n",
    )
    matrix = tmp_path / "migration/hypostructure/eg-node-matrix.csv"
    supplemental = (
        tmp_path / "migration/hypostructure/supplemental-legacy-evidence.csv"
    )
    matrix.parent.mkdir(parents=True, exist_ok=True)
    with matrix.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=EG_FIELDS, lineterminator="\n")
        writer.writeheader()
        node11 = {field: "" for field in EG_FIELDS}
        node11.update(
            {
                "node_id": "11",
                "math_status": "open",
                "work_status": "not_captured",
                "blocker": "reviewed Node 11 blocker",
            }
        )
        source_only = {field: "" for field in EG_FIELDS}
        source_only.update(
            {
                "node_id": "160",
                "normalized_input": "reviewed source-only input",
                "normalized_outcomes": "reviewed source-only outcome",
                "observed_legacy_ct_ids": "CT3",
            }
        )
        writer.writerows((node11, source_only))

    update_supplemental_legacy(tmp_path, supplemental, matrix)
    update_eg(tmp_path, matrix)

    with matrix.open(newline="", encoding="utf-8") as handle:
        by_id = {
            int(row["node_id"]): row for row in csv.DictReader(handle)
        }
    with supplemental.open(newline="", encoding="utf-8") as handle:
        supplemental_by_id = {
            int(row["legacy_node_id"]): row for row in csv.DictReader(handle)
        }

    assert by_id[4]["direct_predecessors"] == "2"
    assert by_id[8]["direct_predecessors"] == "6"
    assert by_id[11]["math_status"] == "open"
    assert by_id[11]["work_status"] == "not_captured"
    assert by_id[11]["blocker"] == "reviewed Node 11 blocker"
    assert 158 not in by_id
    assert supplemental_by_id[158]["observed_imports"] == "157"
    assert supplemental_by_id[160]["normalized_input"] == (
        "reviewed source-only input"
    )
    assert supplemental_by_id[160]["normalized_outcomes"] == (
        "reviewed source-only outcome"
    )
    assert supplemental_by_id[160]["observed_ct_ids"] == "CT3"


def test_pde_row_matrix_covers_rows_one_through_eighteen_and_17b() -> None:
    rows = read_csv("pde-row-matrix.csv")
    expected_header = [
        "row_id",
        "notebook_source",
        "required_capabilities",
        "ct_chain",
        "axiom_free_fixture",
        "ns2d_instance",
        "complementary_residual",
        "kernel_status",
        "integration_status",
        "notes",
    ]
    assert list(rows[0]) == expected_header
    assert [row["row_id"] for row in rows] == [
        *[str(number) for number in range(1, 18)],
        "17b",
        "18",
    ]
    assert {row["kernel_status"] for row in rows} <= {
        "not_checked",
        "kernel_checked",
    }
    assert {row["integration_status"] for row in rows} <= {
        "not_checked",
        "fixture_checked",
        "integration_checked",
    }
    by_id = {row["row_id"]: row for row in rows}
    for row_id in ("1", "2", "3", "4"):
        assert by_id[row_id]["kernel_status"] == "kernel_checked"
        assert by_id[row_id]["integration_status"] == "fixture_checked"

    assert by_id["2"]["ns2d_instance"] == "not_started"
    assert "RepresentedNS2DGeneratorFormPacket" in by_id["2"][
        "axiom_free_fixture"
    ]
    assert "valid represented equation state" in by_id["2"]["notes"]
    assert "full continuum admissibility is not encoded" in by_id["2"][
        "notes"
    ]

    assert by_id["3"]["ns2d_instance"] == "not_started"
    assert "RepresentedNS2DResourceBudgetPacket" in by_id["3"][
        "axiom_free_fixture"
    ]
    assert "proves no NSE energy estimate" in by_id["3"]["notes"]

    assert by_id["4"]["ns2d_instance"] == "not_started"
    assert "RepresentedNS2DQuotientDefectPacket" in by_id["4"][
        "axiom_free_fixture"
    ]
    assert "typed query preserved across row 3" in by_id["4"]["notes"]
    assert "prove no continuum q/U" in by_id["4"]["notes"]


def test_baseline_and_decision_templates_are_machine_usable() -> None:
    baseline = json.loads(
        (MIGRATION_ROOT / "baseline/manifest.template.json").read_text(
            encoding="utf-8"
        )
    )
    assert baseline["schema_version"] == 1
    assert baseline["baseline"]["commit"] is None
    assert baseline["baseline"]["clean_worktree"] is None
    assert all(artifact["sha256"] is None for artifact in baseline["artifacts"])

    allowlist = json.loads(
        (MIGRATION_ROOT / "trust-allowlist.json").read_text(encoding="utf-8")
    )
    assert allowlist["schema_version"] == 1
    assert allowlist["allowed_axioms"] == []

    decision = (MIGRATION_ROOT / "decisions/0000-template.md").read_text(
        encoding="utf-8"
    )
    for heading in (
        "## Missing Use Case",
        "## Ownership",
        "## Public Author Inputs",
        "## Framework Outputs",
        "## Residual Branches",
        "## Both-Sides Test",
        "## Fixtures",
        "## Compatibility Impact",
    ):
        assert heading in decision

    readme = (MIGRATION_ROOT / "README.md").read_text(encoding="utf-8")
    assert "key-preserving merge" in readme
    assert "No parity baseline is frozen" in readme
