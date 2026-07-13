"""Load immutable web projections from framework-generated artifacts."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
from typing import Any


class ArtifactError(RuntimeError):
    """Raised when a required generated artifact is missing or malformed."""


def _load_object(path: Path) -> dict[str, Any]:
    if not path.is_file():
        raise ArtifactError(f"required generated artifact is missing: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ArtifactError(f"cannot load generated artifact {path}: {error}") from error
    if not isinstance(value, dict):
        raise ArtifactError(f"generated artifact must be a JSON object: {path}")
    return value


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def verification_view(
    catalog_hash: str, verification: dict[str, Any]
) -> dict[str, Any]:
    """Project kernel verification into a freshness-aware UI status."""

    reported = str(verification.get("status", "failed"))
    verified_hash = str(verification.get("catalogHash", ""))
    if reported == "failed":
        state = "failed"
        message = "The latest recorded kernel verification failed."
    elif reported == "kernel_checked" and verified_hash == catalog_hash:
        state = "verified"
        message = "The displayed catalog matches the kernel-checked artifact."
    else:
        state = "stale"
        message = "The catalog has changed since the recorded kernel verification."

    toolchain = verification.get("toolchain", {})
    aggregate = verification.get("aggregate", {})
    if not isinstance(toolchain, dict) or not isinstance(aggregate, dict):
        raise ArtifactError("kernel verification toolchain and aggregate must be objects")
    return {
        "state": state,
        "reportedStatus": reported,
        "catalogHash": catalog_hash,
        "verificationCatalogHash": verified_hash,
        "message": message,
        "toolchain": toolchain,
        "aggregate": aggregate,
    }


def example_verification_view(
    catalog_hash: str, verification: dict[str, Any]
) -> dict[str, Any]:
    """Project example-catalog verification independently of the CT catalog."""

    reported = str(verification.get("status", "failed"))
    verified_hash = str(verification.get("exampleCatalogHash", ""))
    if reported == "failed":
        state = "failed"
        message = "The latest recorded example verification failed."
    elif reported == "kernel_checked" and verified_hash == catalog_hash:
        state = "verified"
        message = "The displayed examples match the kernel-checked artifacts."
    else:
        state = "stale"
        message = "The examples have changed since the recorded kernel verification."
    return {
        "state": state,
        "reportedStatus": reported,
        "exampleCatalogHash": catalog_hash,
        "verificationExampleCatalogHash": verified_hash,
        "message": message,
    }


class ArtifactRepository:
    """In-memory, read-only access to the Lean-derived catalog and diagrams."""

    def __init__(self, root: Path | None = None) -> None:
        configured = os.environ.get("STRUCTURAL_EXHAUSTION_ROOT")
        self.root = (
            root
            if root is not None
            else Path(configured).expanduser()
            if configured
            else Path(__file__).resolve().parents[3]
        ).resolve()
        self.catalog_path = self.root / "generated/lean-machines.json"
        self.catalog = _load_object(self.catalog_path)
        self.catalog_hash = _sha256(self.catalog_path)
        self.verification = _load_object(
            self.root / "generated/kernel-verification.json"
        )
        self.verification_status = verification_view(
            self.catalog_hash, self.verification
        )

        tactics = self.catalog.get("tactics")
        routes = self.catalog.get("routes")
        if not isinstance(tactics, list) or not tactics:
            raise ArtifactError("compiled catalog has no tactic list")
        if not isinstance(routes, list):
            raise ArtifactError("compiled catalog has no route list")

        self.tactics: dict[str, dict[str, Any]] = {}
        self.graphs: dict[str, dict[str, Any]] = {}
        for tactic in tactics:
            if not isinstance(tactic, dict) or not isinstance(
                tactic.get("tacticId"), str
            ):
                raise ArtifactError("compiled catalog contains an invalid tactic")
            tactic_id = tactic["tacticId"]
            if tactic_id in self.tactics:
                raise ArtifactError(f"compiled catalog repeats tactic {tactic_id}")
            graph = _load_object(
                self.root / f"generated/cytoscape/{tactic_id}.json"
            )
            if graph.get("tacticId") != tactic_id or not isinstance(
                graph.get("elements"), list
            ):
                raise ArtifactError(f"invalid generated Cytoscape graph for {tactic_id}")
            self.tactics[tactic_id] = tactic
            self.graphs[tactic_id] = graph

        self.residual_owner = {
            residual["residualKindId"]: tactic_id
            for tactic_id, tactic in self.tactics.items()
            for residual in tactic.get("residualKinds", [])
            if isinstance(residual, dict)
            and isinstance(residual.get("residualKindId"), str)
        }
        self.routes = [self._route_view(route) for route in routes]
        self.route_by_id = {route["routeId"]: route for route in self.routes}

        self.example_root = (self.root / "generated/examples").resolve()
        self.example_index_path = self.example_root / "index.json"
        self.example_index = _load_object(self.example_index_path)
        self.example_catalog_hash = _sha256(self.example_index_path)
        self.example_verification_status = example_verification_view(
            self.example_catalog_hash, self.verification
        )
        raw_examples = self.example_index.get("examples")
        source_of_truth = self.example_index.get("sourceOfTruth")
        if not isinstance(raw_examples, list) or not raw_examples:
            raise ArtifactError("generated example index has no example list")
        if not isinstance(source_of_truth, dict):
            raise ArtifactError("example index sourceOfTruth must be an object")

        self.example_summaries_by_id: dict[str, dict[str, Any]] = {}
        self.examples: dict[str, dict[str, Any]] = {}
        for raw_summary in raw_examples:
            self._load_example(raw_summary)

    def _route_view(self, route: Any) -> dict[str, Any]:
        if not isinstance(route, dict):
            raise ArtifactError("compiled catalog contains an invalid route")
        residual = route.get("sourceResidualKind")
        target = route.get("targetTacticId")
        owner = self.residual_owner.get(residual)
        if owner is None or target not in self.tactics:
            raise ArtifactError(
                f"route {route.get('routeId', '<unknown>')} has invalid endpoints"
            )
        return {**route, "sourceTacticId": owner}

    def _load_example(self, raw_summary: Any) -> None:
        if not isinstance(raw_summary, dict):
            raise ArtifactError("example index contains a non-object summary")
        example_id = raw_summary.get("exampleId")
        detail_file = raw_summary.get("detailFile")
        expected_hash = raw_summary.get("detailHash")
        if not all(isinstance(value, str) and value for value in (
            example_id, detail_file, expected_hash
        )):
            raise ArtifactError("example summary lacks an id, detail file, or hash")
        if example_id in self.examples:
            raise ArtifactError(f"example index repeats {example_id}")
        detail_path = (self.example_root / detail_file).resolve()
        if self.example_root not in detail_path.parents or detail_path.suffix != ".json":
            raise ArtifactError(f"example {example_id} has an unsafe detail path")
        observed_hash = _sha256(detail_path)
        if observed_hash != expected_hash:
            raise ArtifactError(f"example {example_id} detail hash does not match its index")
        detail = _load_object(detail_path)
        if detail.get("exampleId") != example_id:
            raise ArtifactError(f"example detail id does not match {example_id}")
        self._validate_example_detail(detail)
        self.example_summaries_by_id[example_id] = self._example_summary(raw_summary)
        self.examples[example_id] = detail

    def _example_summary(self, value: dict[str, Any]) -> dict[str, Any]:
        workflows = value.get("workflows", [])
        if not isinstance(workflows, list):
            raise ArtifactError(f"example {value.get('exampleId')} workflows must be a list")
        projected_workflows: list[dict[str, str]] = []
        for workflow in workflows:
            if not isinstance(workflow, dict):
                raise ArtifactError("example workflow summary must be an object")
            projected_workflows.append(
                {
                    "workflowId": str(workflow.get("workflowId", "")),
                    "title": str(workflow.get("title", "")),
                    "purpose": str(workflow.get("purpose", "")),
                    "completion": str(workflow.get("completion", "")),
                }
            )
        tactic_ids = value.get("tacticIds", [])
        if not isinstance(tactic_ids, list) or not all(
            isinstance(tactic_id, str) and tactic_id in self.tactics
            for tactic_id in tactic_ids
        ):
            raise ArtifactError(f"example {value.get('exampleId')} has invalid tactic IDs")
        proof_status = value.get("proofStatus")
        if proof_status not in {"complete", "partial"}:
            raise ArtifactError(f"example {value.get('exampleId')} has invalid proof status")
        expected_count = value.get("workflowCount")
        if expected_count != len(projected_workflows):
            raise ArtifactError(f"example {value.get('exampleId')} workflow count is stale")
        return {
            "exampleId": value.get("exampleId"),
            "title": value.get("title"),
            "summary": value.get("summary"),
            "proofStatus": proof_status,
            "tacticIds": tactic_ids,
            "workflowCount": expected_count,
            "workflows": projected_workflows,
        }

    def _validate_example_detail(self, detail: dict[str, Any]) -> None:
        example_id = str(detail.get("exampleId", "<unknown>"))
        tactic_ids = detail.get("tacticIds")
        workflows = detail.get("workflows")
        declarations = detail.get("declarations")
        sources = detail.get("sources")
        bindings = detail.get("interfaceBindings", [])
        if not isinstance(tactic_ids, list) or not all(
            isinstance(item, str) and item in self.tactics for item in tactic_ids
        ):
            raise ArtifactError(f"example {example_id} references an unknown tactic")
        if not all(isinstance(value, list) for value in (
            workflows, declarations, sources, bindings
        )):
            raise ArtifactError(f"example {example_id} has malformed collections")

        source_ids: set[str] = set()
        source_line_counts: dict[str, int] = {}
        for source in sources:
            if not isinstance(source, dict):
                raise ArtifactError(f"example {example_id} has an invalid source")
            source_id = source.get("sourceId")
            path = source.get("path")
            content = source.get("content")
            digest = source.get("sha256")
            if not all(isinstance(value, str) for value in (
                source_id, path, content, digest
            )):
                raise ArtifactError(f"example {example_id} has malformed source data")
            source_path = Path(path)
            if source_path.is_absolute() or ".." in source_path.parts:
                raise ArtifactError(f"example {example_id} exposes an unsafe source path")
            if digest != _sha256_text(content):
                raise ArtifactError(f"example {example_id} source hash mismatch for {path}")
            if source_id in source_ids:
                raise ArtifactError(f"example {example_id} repeats source {source_id}")
            source_ids.add(source_id)
            source_line_counts[source_id] = len(content.splitlines())

        declaration_ids: set[str] = set()
        for declaration in declarations:
            if not isinstance(declaration, dict):
                raise ArtifactError(f"example {example_id} has an invalid declaration")
            declaration_id = declaration.get("declarationId")
            source_id = declaration.get("sourceId")
            if not isinstance(declaration_id, str) or declaration_id in declaration_ids:
                raise ArtifactError(f"example {example_id} repeats a declaration id")
            if source_id not in source_ids:
                raise ArtifactError(f"example {example_id} declaration has no source")
            start_line = declaration.get("startLine")
            end_line = declaration.get("endLine")
            if not isinstance(start_line, int) or not isinstance(end_line, int):
                raise ArtifactError(f"example {example_id} declaration has no range")
            if start_line < 1 or end_line < start_line:
                raise ArtifactError(f"example {example_id} declaration range is invalid")
            if end_line > source_line_counts[source_id]:
                raise ArtifactError(f"example {example_id} declaration exceeds its source")
            declaration_ids.add(declaration_id)

        stage_ids: set[str] = set()
        stage_by_id: dict[str, dict[str, Any]] = {}
        workflow_by_stage: dict[str, str] = {}
        for workflow in workflows:
            if not isinstance(workflow, dict) or not isinstance(
                workflow.get("stages"), list
            ) or not isinstance(workflow.get("links"), list):
                raise ArtifactError(f"example {example_id} has a malformed workflow")
            local_stage_ids: set[str] = set()
            for stage in workflow["stages"]:
                if not isinstance(stage, dict):
                    raise ArtifactError(f"example {example_id} has a malformed stage")
                stage_id = stage.get("stageId")
                if not isinstance(stage_id, str) or stage_id in stage_ids:
                    raise ArtifactError(f"example {example_id} repeats stage {stage_id}")
                tactic_id = stage.get("tacticId")
                if tactic_id is not None and tactic_id not in self.tactics:
                    raise ArtifactError(f"example {example_id} stage has unknown tactic")
                primary = stage.get("primaryDeclarationId")
                evidence = stage.get("evidenceDeclarationIds", [])
                if primary not in declaration_ids or not isinstance(evidence, list) or not set(
                    evidence
                ).issubset(declaration_ids):
                    raise ArtifactError(f"example {example_id} stage has invalid declarations")
                stage_ids.add(stage_id)
                local_stage_ids.add(stage_id)
                stage_by_id[stage_id] = stage
                workflow_by_stage[stage_id] = str(workflow.get("workflowId", ""))
            link_ids: set[str] = set()
            for link in workflow["links"]:
                if not isinstance(link, dict):
                    raise ArtifactError(f"example {example_id} has a malformed link")
                link_id = link.get("linkId")
                if not isinstance(link_id, str) or link_id in link_ids:
                    raise ArtifactError(f"example {example_id} repeats link {link_id}")
                if link.get("sourceStageId") not in local_stage_ids or link.get(
                    "targetStageId"
                ) not in local_stage_ids:
                    raise ArtifactError(f"example {example_id} link has invalid endpoints")
                evidence = link.get("evidenceDeclarationIds", [])
                if not isinstance(evidence, list) or not set(evidence).issubset(
                    declaration_ids
                ):
                    raise ArtifactError(f"example {example_id} link has invalid evidence")
                if link.get("kind") == "registeredRoute":
                    route = self.route_by_id.get(link.get("routeId"))
                    if route is None:
                        raise ArtifactError(f"example {example_id} has an unknown route")
                    source_stage = stage_by_id[link["sourceStageId"]]
                    target_stage = stage_by_id[link["targetStageId"]]
                    if source_stage.get("tacticId") not in (None, route["sourceTacticId"]):
                        raise ArtifactError(f"example {example_id} route source disagrees")
                    if target_stage.get("tacticId") not in (None, route["targetTacticId"]):
                        raise ArtifactError(f"example {example_id} route target disagrees")
                link_ids.add(link_id)

        for binding in bindings:
            if not isinstance(binding, dict) or binding.get("stageId") not in stage_ids:
                raise ArtifactError(f"example {example_id} binding has invalid stage")
            if binding.get("workflowId") != workflow_by_stage[binding["stageId"]]:
                raise ArtifactError(f"example {example_id} binding has invalid workflow")
            refs = {
                binding.get("problemDeclarationId"),
                binding.get("frameworkDeclarationId"),
            }
            if not refs.issubset(declaration_ids):
                raise ArtifactError(f"example {example_id} binding has invalid declarations")

    @property
    def catalog_view(self) -> dict[str, Any]:
        source = self.catalog.get("sourceOfTruth", {})
        if not isinstance(source, dict):
            raise ArtifactError("catalog sourceOfTruth must be an object")
        return {
            "schemaVersion": str(self.catalog.get("schemaVersion", "")),
            "catalogHash": self.catalog_hash,
            "sourceOfTruth": source,
        }

    @property
    def example_catalog_view(self) -> dict[str, Any]:
        source = self.example_index.get("sourceOfTruth", {})
        if not isinstance(source, dict):
            raise ArtifactError("example catalog sourceOfTruth must be an object")
        return {
            "schemaVersion": str(self.example_index.get("schemaVersion", "")),
            "catalogHash": self.example_catalog_hash,
            "sourceOfTruth": source,
        }

    def tactic_summaries(self) -> list[dict[str, Any]]:
        summaries: list[dict[str, Any]] = []
        for tactic in self.tactics.values():
            manual = sum(
                len(node.get("automation", {}).get("manualObligations", []))
                for node in tactic.get("nodes", [])
            )
            summaries.append(
                {
                    "tacticId": tactic["tacticId"],
                    "title": tactic["title"],
                    "apiVersion": tactic["apiVersion"],
                    "namespace": tactic["namespace"],
                    "nodeCount": len(tactic.get("nodes", [])),
                    "transitionCount": len(tactic.get("transitions", [])),
                    "terminalCount": len(tactic.get("terminals", [])),
                    "residualCount": len(tactic.get("residualKinds", [])),
                    "manualObligationCount": manual,
                }
            )
        return summaries

    def example_summaries(self) -> list[dict[str, Any]]:
        return list(self.example_summaries_by_id.values())

    def framework_response(self) -> dict[str, Any]:
        summaries = self.tactic_summaries()
        return {
            "artifactType": "frameworkExplorer",
            "catalog": self.catalog_view,
            "verification": self.verification_status,
            "totals": {
                "tactics": len(summaries),
                "nodes": sum(item["nodeCount"] for item in summaries),
                "transitions": sum(item["transitionCount"] for item in summaries),
                "terminals": sum(item["terminalCount"] for item in summaries),
                "residualKinds": sum(item["residualCount"] for item in summaries),
                "routes": len(self.routes),
                "manualObligations": sum(
                    item["manualObligationCount"] for item in summaries
                ),
            },
            "tactics": summaries,
            "routes": self.routes,
        }

    def tactic_response(self, tactic_id: str) -> dict[str, Any] | None:
        tactic = self.tactics.get(tactic_id)
        if tactic is None:
            return None
        return {
            "artifactType": "frameworkExplorerTactic",
            "catalogHash": self.catalog_hash,
            "verification": self.verification_status,
            "tactic": tactic,
            "graph": self.graphs[tactic_id],
            "inboundRoutes": [
                route for route in self.routes if route["targetTacticId"] == tactic_id
            ],
            "outboundRoutes": [
                route for route in self.routes if route["sourceTacticId"] == tactic_id
            ],
        }

    def examples_response(self) -> dict[str, Any]:
        return {
            "artifactType": "frameworkExplorerExamples",
            "catalog": self.example_catalog_view,
            "verification": self.example_verification_status,
            "examples": self.example_summaries(),
        }

    def example_response(self, example_id: str) -> dict[str, Any] | None:
        example = self.examples.get(example_id)
        if example is None:
            return None
        summaries = {item["tacticId"]: item for item in self.tactic_summaries()}
        return {
            "artifactType": "frameworkExplorerExample",
            "catalogHash": self.example_catalog_hash,
            "frameworkCatalogHash": self.catalog_hash,
            "verification": self.example_verification_status,
            "example": example,
            "tactics": [
                summaries[tactic_id] for tactic_id in example.get("tacticIds", [])
            ],
        }
