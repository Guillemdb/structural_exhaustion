from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator, FormatChecker

from tools.update_erdos_proof_history import (
    ErdosProofHistoryError,
    canonical_json_bytes,
    derive_snapshot,
    update_history,
    validate_history,
)


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_PATH = ROOT / "generated/examples/erdos-64.json"
HISTORY_PATH = ROOT / "generated/examples/erdos-64-history.json"
SCHEMA_PATH = ROOT / "schemas/erdos-proof-history.schema.json"


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def evidence_without_provenance(snapshot: dict) -> dict:
    return {key: value for key, value in snapshot.items() if key != "provenance"}


def all_keys(value: object) -> set[str]:
    if isinstance(value, dict):
        return set(value) | {
            nested_key
            for nested_value in value.values()
            for nested_key in all_keys(nested_value)
        }
    if isinstance(value, list):
        return {
            nested_key for nested_value in value for nested_key in all_keys(nested_value)
        }
    return set()


def test_initial_history_matches_the_current_hydrated_artifact() -> None:
    history = read_json(HISTORY_PATH)
    schema = read_json(SCHEMA_PATH)
    errors = sorted(
        Draft202012Validator(schema, format_checker=FormatChecker()).iter_errors(
            history
        ),
        key=lambda error: list(error.absolute_path),
    )
    assert errors == []
    validate_history(history)

    assert len(history["snapshots"]) == 1
    snapshot = history["snapshots"][0]
    artifact_bytes = ARTIFACT_PATH.read_bytes()
    derived = derive_snapshot(artifact_bytes, snapshot["provenance"])
    assert derived == snapshot
    assert snapshot["artifactSha256"] == hashlib.sha256(artifact_bytes).hexdigest()
    assert snapshot["formalizedNodeCount"] == 34
    assert snapshot["obligations"] == {"proved": 71, "total": 71}
    assert snapshot["implementedWorkflowSteps"] == 126
    assert snapshot["frameworkLeverage"] == {
        "automatedLinkCount": 73,
        "registeredTransitionCount": 5,
        "interfaceBindingCount": 29,
        "declarationFootprint": {
            "framework": 591,
            "author": 935,
            "external": 1,
            "total": 1527,
        },
    }


def test_update_is_source_date_epoch_deterministic_and_deduplicates(
    tmp_path: Path,
) -> None:
    artifact_path = tmp_path / "erdos-64.json"
    artifact_path.write_bytes(ARTIFACT_PATH.read_bytes())
    history_path = tmp_path / "history.json"
    environment = {"SOURCE_DATE_EPOCH": "1700000000"}

    first, appended = update_history(
        artifact_path, history_path, repo_root=tmp_path, environ=environment
    )
    assert appended is True
    first_bytes = history_path.read_bytes()
    assert first["snapshots"][0]["provenance"] == {
        "recordedAt": "2023-11-14T22:13:20Z",
        "gitCommit": None,
        "workingTree": "unknown",
        "sourceDateEpoch": 1700000000,
    }

    duplicate, appended = update_history(
        artifact_path,
        history_path,
        repo_root=tmp_path,
        environ={"SOURCE_DATE_EPOCH": "1800000000"},
    )
    assert appended is False
    assert duplicate == first
    assert history_path.read_bytes() == first_bytes

    replay_path = tmp_path / "replay.json"
    replay, replay_appended = update_history(
        artifact_path, replay_path, repo_root=tmp_path, environ=environment
    )
    assert replay_appended is True
    assert replay == first
    assert replay_path.read_bytes() == first_bytes


def test_update_appends_new_artifacts_without_rewriting_prior_snapshots(
    tmp_path: Path,
) -> None:
    artifact_path = tmp_path / "erdos-64.json"
    artifact_path.write_bytes(ARTIFACT_PATH.read_bytes())
    history_path = tmp_path / "history.json"
    first, _ = update_history(
        artifact_path,
        history_path,
        repo_root=tmp_path,
        environ={"SOURCE_DATE_EPOCH": "1700000000"},
    )
    original_snapshot = copy.deepcopy(first["snapshots"][0])

    changed_artifact = read_json(artifact_path)
    changed_artifact["summary"] += " A byte-distinct renderer fixture."
    artifact_path.write_bytes(canonical_json_bytes(changed_artifact))
    second, appended = update_history(
        artifact_path,
        history_path,
        repo_root=tmp_path,
        environ={"SOURCE_DATE_EPOCH": "1700000001"},
    )

    assert appended is True
    assert len(second["snapshots"]) == 2
    assert second["snapshots"][0] == original_snapshot
    assert (
        second["snapshots"][1]["artifactSha256"]
        != original_snapshot["artifactSha256"]
    )
    assert evidence_without_provenance(second["snapshots"][1]) | {
        "artifactSha256": original_snapshot["artifactSha256"]
    } == evidence_without_provenance(original_snapshot)
    prohibited = {key.casefold() for key in all_keys(second)}
    assert "timesaved" not in prohibited
    assert "speedup" not in prohibited


def test_history_validator_rejects_inconsistent_counts_and_duplicate_hashes() -> None:
    history = read_json(HISTORY_PATH)
    inconsistent = copy.deepcopy(history)
    inconsistent["snapshots"][0]["formalizedNodeCount"] += 1
    with pytest.raises(ErdosProofHistoryError, match="formalizedNodeCount"):
        validate_history(inconsistent)

    duplicated = copy.deepcopy(history)
    duplicated["snapshots"].append(copy.deepcopy(duplicated["snapshots"][0]))
    with pytest.raises(ErdosProofHistoryError, match="duplicate artifact hashes"):
        validate_history(duplicated)


def test_derivation_rejects_declarations_outside_framework_and_erdos_packages() -> None:
    artifact = read_json(ARTIFACT_PATH)
    artifact["declarations"][0]["sourceId"] = "Unowned.Experiment"
    with pytest.raises(ErdosProofHistoryError, match="no supported owner"):
        derive_snapshot(
            canonical_json_bytes(artifact),
            {
                "recordedAt": "2023-11-14T22:13:20Z",
                "gitCommit": None,
                "workingTree": "unknown",
                "sourceDateEpoch": 1700000000,
            },
        )
