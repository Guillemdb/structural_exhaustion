from __future__ import annotations

import csv
import os
from pathlib import Path

import pytest

from tools.update_hypostructure_migration_records import PDE_FIELDS, update_pde


FRAMEWORK_FIXTURE = "Hypostructure.Fixtures.PDERows1To4"
EXAMPLE_FIXTURE = (
    "HypostructurePDEExamples.RepresentedNS2DLocalTailPacket"
)


def module_paths(root: Path, module: str) -> tuple[Path, Path]:
    package = (
        root / "hypostructure"
        if module.startswith("Hypostructure.")
        else root / "examples/hypostructure_pde"
    )
    relative = Path(*module.split(".")).with_suffix(".lean")
    return (
        package / relative,
        package / ".lake/build/lib/lean" / relative.with_suffix(".olean"),
    )


def write_module_artifact(
    root: Path,
    module: str,
    *,
    source_mtime_ns: int,
    olean_mtime_ns: int | None,
) -> None:
    source, olean = module_paths(root, module)
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text("theorem checked : True := by trivial\n", encoding="utf-8")
    os.utime(source, ns=(source_mtime_ns, source_mtime_ns))
    if olean_mtime_ns is not None:
        olean.parent.mkdir(parents=True, exist_ok=True)
        olean.write_bytes(b"test artifact")
        os.utime(olean, ns=(olean_mtime_ns, olean_mtime_ns))


def write_reviewed_row(matrix: Path, fixture_spec: str) -> None:
    matrix.parent.mkdir(parents=True, exist_ok=True)
    row = {field: "" for field in PDE_FIELDS}
    row.update(
        {
            "row_id": "1",
            "axiom_free_fixture": fixture_spec,
            "ns2d_instance": "not_started",
            "kernel_status": "kernel_checked",
            "integration_status": "integration_checked",
        }
    )
    with matrix.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=PDE_FIELDS, lineterminator="\n")
        writer.writeheader()
        writer.writerow(row)


def read_row(matrix: Path, row_id: str) -> dict[str, str]:
    with matrix.open(newline="", encoding="utf-8") as stream:
        return next(row for row in csv.DictReader(stream) if row["row_id"] == row_id)


def test_pde_updater_derives_checked_statuses_from_fresh_artifacts(
    tmp_path: Path,
) -> None:
    matrix = tmp_path / "migration/hypostructure/pde-row-matrix.csv"
    write_reviewed_row(matrix, f"{FRAMEWORK_FIXTURE};{EXAMPLE_FIXTURE}")
    write_module_artifact(
        tmp_path,
        FRAMEWORK_FIXTURE,
        source_mtime_ns=100,
        olean_mtime_ns=200,
    )
    write_module_artifact(
        tmp_path,
        EXAMPLE_FIXTURE,
        source_mtime_ns=100,
        olean_mtime_ns=200,
    )

    update_pde(tmp_path, matrix)

    row = read_row(matrix, "1")
    assert row["kernel_status"] == "kernel_checked"
    assert row["integration_status"] == "fixture_checked"
    assert row["ns2d_instance"] == "not_started"


@pytest.mark.parametrize(
    ("framework_olean_ns", "example_olean_ns", "kernel", "integration"),
    [
        (None, 200, "not_checked", "not_checked"),
        (50, 200, "not_checked", "not_checked"),
        (200, None, "kernel_checked", "not_checked"),
        (200, 50, "kernel_checked", "not_checked"),
    ],
)
def test_pde_updater_demotes_status_for_missing_or_stale_artifacts(
    tmp_path: Path,
    framework_olean_ns: int | None,
    example_olean_ns: int | None,
    kernel: str,
    integration: str,
) -> None:
    matrix = tmp_path / "migration/hypostructure/pde-row-matrix.csv"
    write_reviewed_row(matrix, f"{FRAMEWORK_FIXTURE};{EXAMPLE_FIXTURE}")
    write_module_artifact(
        tmp_path,
        FRAMEWORK_FIXTURE,
        source_mtime_ns=100,
        olean_mtime_ns=framework_olean_ns,
    )
    write_module_artifact(
        tmp_path,
        EXAMPLE_FIXTURE,
        source_mtime_ns=100,
        olean_mtime_ns=example_olean_ns,
    )

    update_pde(tmp_path, matrix)

    row = read_row(matrix, "1")
    assert row["kernel_status"] == kernel
    assert row["integration_status"] == integration
    assert row["ns2d_instance"] == "not_started"


def test_pde_updater_rejects_non_module_fixture_labels(tmp_path: Path) -> None:
    matrix = tmp_path / "migration/hypostructure/pde-row-matrix.csv"
    write_reviewed_row(matrix, "finite-dimensional linear operator")

    update_pde(tmp_path, matrix)

    row = read_row(matrix, "1")
    assert row["kernel_status"] == "not_checked"
    assert row["integration_status"] == "not_checked"
    assert row["ns2d_instance"] == "not_started"
