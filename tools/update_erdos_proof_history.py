#!/usr/bin/env python3
"""Append an auditable snapshot of the hydrated Erdős proof artifact.

The history deliberately records only facts present in the generated artifact
and repository provenance.  Declaration and automation counts are reuse
evidence; this module never estimates elapsed time or a hypothetical manual
formalization cost.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ARTIFACT = ROOT / "generated/examples/erdos-64.json"
DEFAULT_HISTORY = ROOT / "generated/examples/erdos-64-history.json"
SCHEMA_VERSION = "1.0.0"
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
GIT_SHA_RE = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")
UTC_TIMESTAMP_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")


class ErdosProofHistoryError(ValueError):
    """The source artifact or append-only history violates its contract."""


def canonical_json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def _load_json_bytes(raw: bytes, label: str) -> dict[str, Any]:
    try:
        value = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ErdosProofHistoryError(f"cannot decode {label}: {error}") from error
    if not isinstance(value, dict):
        raise ErdosProofHistoryError(f"{label}: expected a JSON object")
    return value


def load_json(path: Path) -> dict[str, Any]:
    try:
        return _load_json_bytes(path.read_bytes(), str(path))
    except OSError as error:
        raise ErdosProofHistoryError(f"cannot read {path}: {error}") from error


def _object(value: object, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ErdosProofHistoryError(f"{label}: expected an object")
    return value


def _array(value: object, label: str) -> list[Any]:
    if not isinstance(value, list):
        raise ErdosProofHistoryError(f"{label}: expected an array")
    return value


def _string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise ErdosProofHistoryError(f"{label}: expected a nonempty string")
    return value


def _nonnegative_integer(value: object, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ErdosProofHistoryError(f"{label}: expected a nonnegative integer")
    return value


def _unique_strings(values: list[Any], label: str) -> list[str]:
    strings = [_string(value, f"{label}[{index}]") for index, value in enumerate(values)]
    if len(strings) != len(set(strings)):
        raise ErdosProofHistoryError(f"{label}: duplicate values")
    return strings


def _timestamp(environ: Mapping[str, str]) -> tuple[str, int | None]:
    raw_epoch = environ.get("SOURCE_DATE_EPOCH")
    if raw_epoch is None:
        moment = datetime.now(timezone.utc).replace(microsecond=0)
        epoch = None
    else:
        try:
            epoch = int(raw_epoch, 10)
        except ValueError as error:
            raise ErdosProofHistoryError(
                "SOURCE_DATE_EPOCH must be a nonnegative base-10 integer"
            ) from error
        if epoch < 0:
            raise ErdosProofHistoryError("SOURCE_DATE_EPOCH must be nonnegative")
        try:
            moment = datetime.fromtimestamp(epoch, timezone.utc)
        except (OverflowError, OSError, ValueError) as error:
            raise ErdosProofHistoryError("SOURCE_DATE_EPOCH is out of range") from error
    return moment.isoformat(timespec="seconds").replace("+00:00", "Z"), epoch


def _git_output(repo_root: Path, *arguments: str) -> str | None:
    try:
        result = subprocess.run(
            ["git", "-C", str(repo_root), *arguments],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return None
    return result.stdout.strip()


def collect_provenance(
    repo_root: Path, environ: Mapping[str, str] | None = None
) -> dict[str, Any]:
    environment = os.environ if environ is None else environ
    recorded_at, source_date_epoch = _timestamp(environment)
    commit = _git_output(repo_root, "rev-parse", "--verify", "HEAD")
    if commit is not None and GIT_SHA_RE.fullmatch(commit) is None:
        raise ErdosProofHistoryError(f"git returned an invalid commit id: {commit!r}")
    status = _git_output(repo_root, "status", "--porcelain=v1", "--untracked-files=normal")
    provenance: dict[str, Any] = {
        "recordedAt": recorded_at,
        "gitCommit": commit,
        "workingTree": "unknown" if status is None else ("dirty" if status else "clean"),
    }
    if source_date_epoch is not None:
        provenance["sourceDateEpoch"] = source_date_epoch
    return provenance


def _validate_artifact_identity(artifact: dict[str, Any]) -> dict[str, Any]:
    if artifact.get("artifactType") != "structuralExhaustionExample":
        raise ErdosProofHistoryError("artifactType must be structuralExhaustionExample")
    if artifact.get("exampleId") != "erdos-64":
        raise ErdosProofHistoryError("exampleId must be erdos-64")
    manuscript = _object(artifact.get("manuscript"), "manuscript")
    manuscript_sha = _string(manuscript.get("sha256"), "manuscript.sha256")
    if SHA256_RE.fullmatch(manuscript_sha) is None:
        raise ErdosProofHistoryError("manuscript.sha256 must be a lowercase SHA-256")
    return manuscript


def _formalized_nodes(manuscript: dict[str, Any]) -> list[int]:
    raw_ids = _array(manuscript.get("formalizedNodeIds"), "manuscript.formalizedNodeIds")
    node_ids: list[int] = []
    for index, value in enumerate(raw_ids):
        node_id = _nonnegative_integer(value, f"manuscript.formalizedNodeIds[{index}]")
        if node_id == 0:
            raise ErdosProofHistoryError("formalized node ids must be positive")
        node_ids.append(node_id)
    if len(node_ids) != len(set(node_ids)):
        raise ErdosProofHistoryError("manuscript.formalizedNodeIds contains duplicates")
    return sorted(node_ids)


def _obligation_counts(manuscript: dict[str, Any]) -> tuple[int, int]:
    obligations = _array(manuscript.get("nodeObligations"), "manuscript.nodeObligations")
    proved = 0
    seen_ids: set[str] = set()
    for index, raw in enumerate(obligations):
        obligation = _object(raw, f"manuscript.nodeObligations[{index}]")
        obligation_id = _string(
            obligation.get("obligationId"),
            f"manuscript.nodeObligations[{index}].obligationId",
        )
        if obligation_id in seen_ids:
            raise ErdosProofHistoryError(f"duplicate obligation id: {obligation_id}")
        seen_ids.add(obligation_id)
        status = _string(
            obligation.get("status"), f"manuscript.nodeObligations[{index}].status"
        )
        if status not in {"proved", "partial", "missing"}:
            raise ErdosProofHistoryError(
                f"manuscript.nodeObligations[{index}].status is invalid: {status!r}"
            )
        proved += status == "proved"
    return proved, len(obligations)


def _implemented_workflow_steps(
    artifact: dict[str, Any], manuscript: dict[str, Any]
) -> int:
    workflows = _array(artifact.get("workflows"), "workflows")
    workflow_stage_ids: list[str] = []
    for workflow_index, raw_workflow in enumerate(workflows):
        workflow = _object(raw_workflow, f"workflows[{workflow_index}]")
        stages = _array(workflow.get("stages"), f"workflows[{workflow_index}].stages")
        for stage_index, raw_stage in enumerate(stages):
            stage = _object(raw_stage, f"workflows[{workflow_index}].stages[{stage_index}]")
            workflow_stage_ids.append(
                _string(
                    stage.get("stageId"),
                    f"workflows[{workflow_index}].stages[{stage_index}].stageId",
                )
            )
    if len(workflow_stage_ids) != len(set(workflow_stage_ids)):
        raise ErdosProofHistoryError("workflow stage ids must be globally unique")

    proof_steps = _array(manuscript.get("proofSteps"), "manuscript.proofSteps")
    implemented_ids: list[str] = []
    for index, raw_step in enumerate(proof_steps):
        step = _object(raw_step, f"manuscript.proofSteps[{index}]")
        status = _string(step.get("status"), f"manuscript.proofSteps[{index}].status")
        if status not in {"implemented", "next", "notStarted"}:
            raise ErdosProofHistoryError(
                f"manuscript.proofSteps[{index}].status is invalid: {status!r}"
            )
        if status == "implemented":
            implemented_ids.append(
                _string(step.get("stageId"), f"manuscript.proofSteps[{index}].stageId")
            )
    if len(implemented_ids) != len(set(implemented_ids)):
        raise ErdosProofHistoryError("implemented proof steps contain duplicate stage ids")
    missing = sorted(set(implemented_ids) - set(workflow_stage_ids))
    if missing:
        raise ErdosProofHistoryError(
            f"implemented proof steps reference absent workflow stages: {missing}"
        )
    if set(implemented_ids) != set(workflow_stage_ids):
        unaccounted = sorted(set(workflow_stage_ids) - set(implemented_ids))
        raise ErdosProofHistoryError(
            f"workflow stages lack implemented proof-step evidence: {unaccounted}"
        )

    coverage = _object(manuscript.get("coverage"), "manuscript.coverage")
    exported_count = _nonnegative_integer(
        coverage.get("verifiedWorkflowSteps"),
        "manuscript.coverage.verifiedWorkflowSteps",
    )
    if exported_count != len(implemented_ids):
        raise ErdosProofHistoryError(
            "verifiedWorkflowSteps disagrees with implemented proof-step stages"
        )
    implemented_count = _nonnegative_integer(
        coverage.get("implementedSteps"), "manuscript.coverage.implementedSteps"
    )
    if implemented_count != len(implemented_ids):
        raise ErdosProofHistoryError(
            "implementedSteps disagrees with implemented proof-step stages"
        )
    return len(implemented_ids)


def _framework_leverage(artifact: dict[str, Any]) -> dict[str, Any]:
    workflows = _array(artifact.get("workflows"), "workflows")
    automated_links = 0
    transition_profile_ids: set[str] = set()
    link_ids: list[str] = []
    for workflow_index, raw_workflow in enumerate(workflows):
        workflow = _object(raw_workflow, f"workflows[{workflow_index}]")
        links = _array(workflow.get("links"), f"workflows[{workflow_index}].links")
        for link_index, raw_link in enumerate(links):
            link = _object(raw_link, f"workflows[{workflow_index}].links[{link_index}]")
            link_ids.append(
                _string(
                    link.get("linkId"),
                    f"workflows[{workflow_index}].links[{link_index}].linkId",
                )
            )
            automation = _array(
                link.get("automationDeclarationIds"),
                f"workflows[{workflow_index}].links[{link_index}].automationDeclarationIds",
            )
            _unique_strings(
                automation,
                f"workflows[{workflow_index}].links[{link_index}].automationDeclarationIds",
            )
            automated_links += bool(automation)
            transition_profile_id = link.get("transitionProfileId")
            if transition_profile_id is not None:
                transition_profile_ids.add(
                    _string(
                        transition_profile_id,
                        "workflows"
                        f"[{workflow_index}].links[{link_index}]"
                        ".transitionProfileId",
                    )
                )
    if len(link_ids) != len(set(link_ids)):
        raise ErdosProofHistoryError("workflow link ids must be globally unique")

    bindings = _array(artifact.get("interfaceBindings"), "interfaceBindings")
    binding_ids: list[str] = []
    for index, raw_binding in enumerate(bindings):
        binding = _object(raw_binding, f"interfaceBindings[{index}]")
        binding_ids.append(
            _string(binding.get("bindingId"), f"interfaceBindings[{index}].bindingId")
        )
    if len(binding_ids) != len(set(binding_ids)):
        raise ErdosProofHistoryError("interface binding ids must be unique")

    declarations = _array(artifact.get("declarations"), "declarations")
    declaration_ids: list[str] = []
    framework_declarations = 0
    author_declarations = 0
    external_declarations = 0
    for index, raw_declaration in enumerate(declarations):
        declaration = _object(raw_declaration, f"declarations[{index}]")
        declaration_ids.append(
            _string(
                declaration.get("declarationId"),
                f"declarations[{index}].declarationId",
            )
        )
        source_id = _string(
            declaration.get("sourceId"), f"declarations[{index}].sourceId"
        )
        if "External" in source_id.split("."):
            external_declarations += 1
        elif source_id == "StructuralExhaustion" or source_id.startswith(
            "StructuralExhaustion."
        ):
            framework_declarations += 1
        elif source_id == "Erdos64EG" or source_id.startswith("Erdos64EG."):
            author_declarations += 1
        else:
            raise ErdosProofHistoryError(
                f"declarations[{index}].sourceId has no supported owner: {source_id!r}"
            )
    if len(declaration_ids) != len(set(declaration_ids)):
        raise ErdosProofHistoryError("declaration ids must be unique")

    return {
        "automatedLinkCount": automated_links,
        "registeredTransitionCount": len(transition_profile_ids),
        "interfaceBindingCount": len(bindings),
        "declarationFootprint": {
            "framework": framework_declarations,
            "author": author_declarations,
            "external": external_declarations,
            "total": len(declarations),
        },
    }


def derive_snapshot(
    artifact_bytes: bytes, provenance: dict[str, Any]
) -> dict[str, Any]:
    artifact = _load_json_bytes(artifact_bytes, "Erdős artifact")
    manuscript = _validate_artifact_identity(artifact)
    node_ids = _formalized_nodes(manuscript)
    obligations_proved, obligations_total = _obligation_counts(manuscript)
    snapshot = {
        "artifactSha256": hashlib.sha256(artifact_bytes).hexdigest(),
        "manuscriptSha256": manuscript["sha256"],
        "formalizedNodeIds": node_ids,
        "formalizedNodeCount": len(node_ids),
        "obligations": {
            "proved": obligations_proved,
            "total": obligations_total,
        },
        "implementedWorkflowSteps": _implemented_workflow_steps(
            artifact, manuscript
        ),
        "frameworkLeverage": _framework_leverage(artifact),
        "provenance": provenance,
    }
    validate_snapshot(snapshot, "derived snapshot")
    return snapshot


def _require_exact_keys(
    value: dict[str, Any], required: set[str], optional: set[str], label: str
) -> None:
    missing = sorted(required - value.keys())
    extra = sorted(value.keys() - required - optional)
    if missing:
        raise ErdosProofHistoryError(f"{label}: missing fields {missing}")
    if extra:
        raise ErdosProofHistoryError(f"{label}: unexpected fields {extra}")


def validate_snapshot(snapshot: object, label: str = "snapshot") -> None:
    value = _object(snapshot, label)
    _require_exact_keys(
        value,
        {
            "artifactSha256",
            "manuscriptSha256",
            "formalizedNodeIds",
            "formalizedNodeCount",
            "obligations",
            "implementedWorkflowSteps",
            "frameworkLeverage",
            "provenance",
        },
        set(),
        label,
    )
    for field in ("artifactSha256", "manuscriptSha256"):
        digest = _string(value[field], f"{label}.{field}")
        if SHA256_RE.fullmatch(digest) is None:
            raise ErdosProofHistoryError(f"{label}.{field}: invalid SHA-256")

    node_values = _array(value["formalizedNodeIds"], f"{label}.formalizedNodeIds")
    node_ids: list[int] = []
    for index, raw_node_id in enumerate(node_values):
        node_id = _nonnegative_integer(
            raw_node_id, f"{label}.formalizedNodeIds[{index}]"
        )
        if node_id == 0:
            raise ErdosProofHistoryError(f"{label}: node ids must be positive")
        node_ids.append(node_id)
    if node_ids != sorted(set(node_ids)):
        raise ErdosProofHistoryError(f"{label}.formalizedNodeIds must be sorted and unique")
    node_count = _nonnegative_integer(
        value["formalizedNodeCount"], f"{label}.formalizedNodeCount"
    )
    if node_count != len(node_ids):
        raise ErdosProofHistoryError(f"{label}: formalizedNodeCount disagrees with ids")

    obligations = _object(value["obligations"], f"{label}.obligations")
    _require_exact_keys(obligations, {"proved", "total"}, set(), f"{label}.obligations")
    proved = _nonnegative_integer(obligations["proved"], f"{label}.obligations.proved")
    total = _nonnegative_integer(obligations["total"], f"{label}.obligations.total")
    if proved > total:
        raise ErdosProofHistoryError(f"{label}: proved obligations exceed total")
    _nonnegative_integer(
        value["implementedWorkflowSteps"], f"{label}.implementedWorkflowSteps"
    )

    leverage = _object(value["frameworkLeverage"], f"{label}.frameworkLeverage")
    _require_exact_keys(
        leverage,
        {
            "automatedLinkCount",
            "registeredTransitionCount",
            "interfaceBindingCount",
            "declarationFootprint",
        },
        set(),
        f"{label}.frameworkLeverage",
    )
    for field in (
        "automatedLinkCount",
        "registeredTransitionCount",
        "interfaceBindingCount",
    ):
        _nonnegative_integer(leverage[field], f"{label}.frameworkLeverage.{field}")
    footprint = _object(
        leverage["declarationFootprint"],
        f"{label}.frameworkLeverage.declarationFootprint",
    )
    _require_exact_keys(
        footprint,
        {"framework", "author", "external", "total"},
        set(),
        f"{label}.frameworkLeverage.declarationFootprint",
    )
    framework = _nonnegative_integer(
        footprint["framework"],
        f"{label}.frameworkLeverage.declarationFootprint.framework",
    )
    author = _nonnegative_integer(
        footprint["author"], f"{label}.frameworkLeverage.declarationFootprint.author"
    )
    external = _nonnegative_integer(
        footprint["external"],
        f"{label}.frameworkLeverage.declarationFootprint.external",
    )
    declaration_total = _nonnegative_integer(
        footprint["total"], f"{label}.frameworkLeverage.declarationFootprint.total"
    )
    if framework + author + external != declaration_total:
        raise ErdosProofHistoryError(f"{label}: declaration footprint does not add up")

    provenance = _object(value["provenance"], f"{label}.provenance")
    _require_exact_keys(
        provenance,
        {"recordedAt", "gitCommit", "workingTree"},
        {"sourceDateEpoch"},
        f"{label}.provenance",
    )
    recorded_at = _string(provenance["recordedAt"], f"{label}.provenance.recordedAt")
    if UTC_TIMESTAMP_RE.fullmatch(recorded_at) is None:
        raise ErdosProofHistoryError(
            f"{label}.provenance.recordedAt must use UTC with second precision"
        )
    try:
        datetime.fromisoformat(recorded_at.removesuffix("Z") + "+00:00")
    except ValueError as error:
        raise ErdosProofHistoryError(
            f"{label}.provenance.recordedAt is not an ISO timestamp"
        ) from error
    commit = provenance["gitCommit"]
    if commit is not None and (
        not isinstance(commit, str) or GIT_SHA_RE.fullmatch(commit) is None
    ):
        raise ErdosProofHistoryError(f"{label}.provenance.gitCommit is invalid")
    if provenance["workingTree"] not in {"clean", "dirty", "unknown"}:
        raise ErdosProofHistoryError(f"{label}.provenance.workingTree is invalid")
    if "sourceDateEpoch" in provenance:
        epoch = _nonnegative_integer(
            provenance["sourceDateEpoch"], f"{label}.provenance.sourceDateEpoch"
        )
        try:
            expected = datetime.fromtimestamp(epoch, timezone.utc).isoformat(
                timespec="seconds"
            ).replace("+00:00", "Z")
        except (OverflowError, OSError, ValueError) as error:
            raise ErdosProofHistoryError(
                f"{label}.provenance.sourceDateEpoch is out of range"
            ) from error
        if expected != recorded_at:
            raise ErdosProofHistoryError(
                f"{label}: recordedAt disagrees with sourceDateEpoch"
            )


def empty_history() -> dict[str, Any]:
    return {
        "artifactType": "erdosProofHistory",
        "schemaVersion": SCHEMA_VERSION,
        "exampleId": "erdos-64",
        "snapshots": [],
    }


def validate_history(history: object) -> None:
    value = _object(history, "history")
    _require_exact_keys(
        value,
        {"artifactType", "schemaVersion", "exampleId", "snapshots"},
        set(),
        "history",
    )
    if value["artifactType"] != "erdosProofHistory":
        raise ErdosProofHistoryError("history.artifactType must be erdosProofHistory")
    if value["schemaVersion"] != SCHEMA_VERSION:
        raise ErdosProofHistoryError(
            f"history.schemaVersion must be {SCHEMA_VERSION}"
        )
    if value["exampleId"] != "erdos-64":
        raise ErdosProofHistoryError("history.exampleId must be erdos-64")
    snapshots = _array(value["snapshots"], "history.snapshots")
    hashes: list[str] = []
    for index, snapshot in enumerate(snapshots):
        validate_snapshot(snapshot, f"history.snapshots[{index}]")
        hashes.append(snapshot["artifactSha256"])
    if len(hashes) != len(set(hashes)):
        raise ErdosProofHistoryError("history contains duplicate artifact hashes")


def _same_artifact_evidence(existing: dict[str, Any], candidate: dict[str, Any]) -> bool:
    fields = (
        "artifactSha256",
        "manuscriptSha256",
        "formalizedNodeIds",
        "formalizedNodeCount",
        "obligations",
        "implementedWorkflowSteps",
        "frameworkLeverage",
    )
    return all(existing[field] == candidate[field] for field in fields)


def update_history(
    artifact_path: Path = DEFAULT_ARTIFACT,
    history_path: Path = DEFAULT_HISTORY,
    repo_root: Path = ROOT,
    environ: Mapping[str, str] | None = None,
) -> tuple[dict[str, Any], bool]:
    try:
        artifact_bytes = artifact_path.read_bytes()
    except OSError as error:
        raise ErdosProofHistoryError(f"cannot read {artifact_path}: {error}") from error
    candidate = derive_snapshot(
        artifact_bytes, collect_provenance(repo_root, environ=environ)
    )

    if history_path.exists():
        history = load_json(history_path)
    else:
        history = empty_history()
    validate_history(history)

    for existing in history["snapshots"]:
        if existing["artifactSha256"] == candidate["artifactSha256"]:
            if not _same_artifact_evidence(existing, candidate):
                raise ErdosProofHistoryError(
                    "existing snapshot disagrees with the artifact carrying its hash"
                )
            return history, False

    updated = {
        **history,
        "snapshots": [*history["snapshots"], candidate],
    }
    validate_history(updated)
    history_path.parent.mkdir(parents=True, exist_ok=True)
    history_path.write_bytes(canonical_json_bytes(updated))
    return updated, True


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact", type=Path, default=DEFAULT_ARTIFACT)
    parser.add_argument("--history", type=Path, default=DEFAULT_HISTORY)
    parser.add_argument("--repo-root", type=Path, default=ROOT)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    arguments = parse_args(argv)
    try:
        history, appended = update_history(
            artifact_path=arguments.artifact,
            history_path=arguments.history,
            repo_root=arguments.repo_root,
        )
    except ErdosProofHistoryError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    action = "appended" if appended else "already recorded"
    print(
        f"{action}: {history['snapshots'][-1]['artifactSha256']} "
        f"({len(history['snapshots'])} snapshot(s))"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
