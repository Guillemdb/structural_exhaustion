from __future__ import annotations

import csv
import json
from pathlib import Path

import pytest

from tools.check_hypostructure_imports import check_repository


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


def test_eg_node_matrix_covers_manuscript_and_source_only_nodes() -> None:
    rows = read_csv("eg-node-matrix.csv")
    expected_header = [
        "node_id",
        "paper_ref",
        "direct_predecessors",
        "legacy_files",
        "legacy_declarations",
        "normalized_input",
        "normalized_outcomes",
        "ct_ids",
        "required_features",
        "new_file",
        "parity_module",
        "legacy_kernel",
        "new_kernel",
        "parity_status",
        "math_status",
        "work_status",
        "web_evidence",
        "status",
        "blocker",
    ]
    assert list(rows[0]) == expected_header
    assert {int(row["node_id"]) for row in rows} == set(range(1, 165))
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
    assert all(row["paper_ref"] for row in rows if int(row["node_id"]) <= 157)
    assert all(not row["paper_ref"] for row in rows if int(row["node_id"]) > 157)
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
    assert by_id[65]["direct_predecessors"] == "64|66"
    assert by_id[66]["direct_predecessors"] == "108"
    assert by_id[89]["direct_predecessors"] == "88|102"
    assert by_id[110]["direct_predecessors"] == "77|109"
    assert by_id[137]["direct_predecessors"] == "131|136"
    assert by_id[144]["direct_predecessors"] == "140|142|143"


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
