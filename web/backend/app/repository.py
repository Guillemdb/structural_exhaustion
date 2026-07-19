"""Load immutable web projections from framework-generated artifacts."""

from __future__ import annotations

import hashlib
import json
import logging
import os
import re
import xml.etree.ElementTree as ET
from datetime import datetime
from pathlib import Path
from typing import Any, Callable


LOGGER = logging.getLogger("structural_exhaustion.web")
MATHEMATICAL_OBJECT_KINDS = {
    "theorem",
    "lemma",
    "proposition",
    "corollary",
    "claim",
    "definition",
    "remark",
}
TYPED_MATHEMATICAL_LABEL_PATTERN = re.compile(
    r"\\label\[(?:theorem|lemma|proposition|corollary|claim|definition|remark)\]"
    r"\{([^}]+)\}"
)
ENVIRONMENT_MATHEMATICAL_LABEL_PATTERN = re.compile(
    r"\\begin\{(?:theorem|lemma|proposition|corollary|claim|definition|remark)\}"
    r"(?:\[[^\]]*\])?\s*\\label(?:\[[^\]]+\])?\{([^}]+)\}"
)
DIAGRAM_NODE_PATTERN = re.compile(r"\\textbf\{\[([0-9]+)\]\}")
SHA256_PATTERN = re.compile(r"^[0-9a-f]{64}$")
GIT_COMMIT_PATTERN = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")
UTC_TIMESTAMP_PATTERN = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$"
)


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


def _canonical_object_hash(value: object) -> str:
    payload = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _validate_erdos_proof_history(value: dict[str, Any]) -> None:
    """Validate append-only engineering telemetry without deriving proof status."""

    def exact_keys(
        item: Any,
        required: set[str],
        label: str,
        optional: set[str] | None = None,
    ) -> dict[str, Any]:
        if not isinstance(item, dict):
            raise ArtifactError(f"{label} must be an object")
        allowed = required | (optional or set())
        if set(item) != allowed and not (
            required <= set(item) and set(item) <= allowed
        ):
            raise ArtifactError(f"{label} has malformed fields")
        return item

    def natural(item: Any, label: str) -> int:
        if not isinstance(item, int) or isinstance(item, bool) or item < 0:
            raise ArtifactError(f"{label} must be a nonnegative integer")
        return item

    exact_keys(
        value,
        {"artifactType", "schemaVersion", "exampleId", "snapshots"},
        "Erdos proof history",
    )
    if (
        value.get("artifactType") != "erdosProofHistory"
        or value.get("schemaVersion") != "1.0.0"
        or value.get("exampleId") != "erdos-64"
    ):
        raise ArtifactError("Erdos proof history has an unsupported identity")
    snapshots = value.get("snapshots")
    if not isinstance(snapshots, list):
        raise ArtifactError("Erdos proof history snapshots must be a list")

    artifact_hashes: set[str] = set()
    for index, raw_snapshot in enumerate(snapshots):
        label = f"Erdos proof history snapshot {index}"
        snapshot = exact_keys(
            raw_snapshot,
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
            label,
        )
        artifact_hash = snapshot.get("artifactSha256")
        manuscript_hash = snapshot.get("manuscriptSha256")
        if not isinstance(artifact_hash, str) or not SHA256_PATTERN.fullmatch(
            artifact_hash
        ):
            raise ArtifactError(f"{label} has an invalid artifact hash")
        if artifact_hash in artifact_hashes:
            raise ArtifactError("Erdos proof history repeats an artifact hash")
        artifact_hashes.add(artifact_hash)
        if not isinstance(manuscript_hash, str) or not SHA256_PATTERN.fullmatch(
            manuscript_hash
        ):
            raise ArtifactError(f"{label} has an invalid manuscript hash")

        node_ids = snapshot.get("formalizedNodeIds")
        if not isinstance(node_ids, list) or any(
            not isinstance(node_id, int)
            or isinstance(node_id, bool)
            or node_id < 1
            for node_id in node_ids
        ):
            raise ArtifactError(f"{label} has invalid formalized node IDs")
        if node_ids != sorted(set(node_ids)):
            raise ArtifactError(f"{label} formalized node IDs must be sorted and unique")
        if natural(snapshot.get("formalizedNodeCount"), f"{label} node count") != len(
            node_ids
        ):
            raise ArtifactError(f"{label} formalized node count disagrees with its IDs")

        obligations = exact_keys(
            snapshot.get("obligations"), {"proved", "total"}, f"{label} obligations"
        )
        proved = natural(obligations.get("proved"), f"{label} proved obligations")
        total = natural(obligations.get("total"), f"{label} total obligations")
        if proved > total:
            raise ArtifactError(f"{label} proves more obligations than it records")
        natural(
            snapshot.get("implementedWorkflowSteps"),
            f"{label} implemented workflow steps",
        )

        leverage = exact_keys(
            snapshot.get("frameworkLeverage"),
            {
                "automatedLinkCount",
                "registeredTransitionCount",
                "interfaceBindingCount",
                "declarationFootprint",
            },
            f"{label} framework leverage",
        )
        for field in (
            "automatedLinkCount",
            "registeredTransitionCount",
            "interfaceBindingCount",
        ):
            natural(leverage.get(field), f"{label} {field}")
        footprint = exact_keys(
            leverage.get("declarationFootprint"),
            {"framework", "author", "external", "total"},
            f"{label} declaration footprint",
        )
        framework_count = natural(
            footprint.get("framework"), f"{label} framework declaration count"
        )
        author_count = natural(
            footprint.get("author"), f"{label} author declaration count"
        )
        external_count = natural(
            footprint.get("external"), f"{label} external declaration count"
        )
        declaration_total = natural(
            footprint.get("total"), f"{label} total declaration count"
        )
        if framework_count + author_count + external_count != declaration_total:
            raise ArtifactError(f"{label} declaration footprint does not add up")

        provenance = exact_keys(
            snapshot.get("provenance"),
            {"recordedAt", "gitCommit", "workingTree"},
            f"{label} provenance",
            {"sourceDateEpoch"},
        )
        recorded_at = provenance.get("recordedAt")
        if not isinstance(recorded_at, str) or not UTC_TIMESTAMP_PATTERN.fullmatch(
            recorded_at
        ):
            raise ArtifactError(f"{label} has an invalid recorded timestamp")
        try:
            datetime.fromisoformat(recorded_at.removesuffix("Z") + "+00:00")
        except ValueError as error:
            raise ArtifactError(f"{label} has an invalid recorded timestamp") from error
        git_commit = provenance.get("gitCommit")
        if git_commit is not None and (
            not isinstance(git_commit, str)
            or not GIT_COMMIT_PATTERN.fullmatch(git_commit)
        ):
            raise ArtifactError(f"{label} has an invalid Git commit")
        if provenance.get("workingTree") not in {"clean", "dirty", "unknown"}:
            raise ArtifactError(f"{label} has an invalid working-tree state")
        if "sourceDateEpoch" in provenance:
            natural(provenance["sourceDateEpoch"], f"{label} source date epoch")


def _xml_local_name(value: str) -> str:
    return value.rsplit("}", 1)[-1] if "}" in value else value


def _validate_manuscript_svg(
    label: str,
    svg: Any,
    digest: Any,
    on_stale_hash: Callable[[str], None] | None = None,
) -> None:
    if not isinstance(svg, str) or not isinstance(digest, str):
        raise ArtifactError(f"manuscript figure {label} has malformed SVG data")
    if _sha256_text(svg) != digest:
        message = f"manuscript figure {label} SVG hash mismatch"
        if on_stale_hash is None:
            raise ArtifactError(message)
        on_stale_hash(message)
    try:
        root = ET.fromstring(svg)
    except ET.ParseError as error:
        raise ArtifactError(f"manuscript figure {label} has malformed SVG") from error
    allowed = {
        "svg", "defs", "font", "font-face", "font-face-src", "font-face-name",
        "glyph", "missing-glyph", "g", "path", "style", "text", "tspan",
        "use", "clipPath", "rect", "circle", "ellipse", "line", "polyline",
        "polygon",
    }
    for element in root.iter():
        name = _xml_local_name(element.tag)
        if name not in allowed:
            raise ArtifactError(
                f"manuscript figure {label} contains unsafe SVG element {name}"
            )
        for attribute, value in element.attrib.items():
            attribute_name = _xml_local_name(attribute).lower()
            if attribute_name.startswith("on"):
                raise ArtifactError(
                    f"manuscript figure {label} contains an SVG event handler"
                )
            if attribute_name == "href" and not value.startswith("#"):
                raise ArtifactError(
                    f"manuscript figure {label} contains an external SVG reference"
                )
            if any(token in value.lower() for token in (
                "javascript:", "data:", "file:", "http://", "https://"
            )):
                raise ArtifactError(
                    f"manuscript figure {label} contains an unsafe SVG URL"
                )
        if name == "style" and element.text:
            lowered = element.text.lower()
            if any(token in lowered for token in (
                "javascript:", "data:", "file:", "http://", "https://"
            )):
                raise ArtifactError(
                    f"manuscript figure {label} contains unsafe SVG style content"
                )


def _validate_manuscript_blocks(
    blocks: Any,
    on_stale_hash: Callable[[str], None] | None = None,
) -> None:
    if not isinstance(blocks, list) or not blocks:
        raise ArtifactError("manuscript fragment has no rendered blocks")
    for block in blocks:
        if not isinstance(block, dict):
            raise ArtifactError("manuscript fragment contains a malformed block")
        if block.get("kind") == "figure":
            label = block.get("label")
            if not isinstance(label, str):
                raise ArtifactError("manuscript fragment contains an unlabeled figure")
            _validate_manuscript_svg(
                label,
                block.get("svg"),
                block.get("svgSha256"),
                on_stale_hash,
            )
        for field in ("blocks", "caption"):
            children = block.get(field)
            if children is not None:
                _validate_manuscript_blocks(children, on_stale_hash)
        items = block.get("items")
        if items is not None:
            if not isinstance(items, list):
                raise ArtifactError("manuscript fragment contains malformed list items")
            for item in items:
                _validate_manuscript_blocks(item, on_stale_hash)


def _validate_source_range(
    declaration_name: str,
    range_name: str,
    value: Any,
    content: str,
) -> None:
    if value is None:
        return
    if not isinstance(value, dict):
        raise ArtifactError(f"{declaration_name} has a malformed {range_name}")
    positions: list[tuple[int, int]] = []
    for endpoint in ("start", "end"):
        position = value.get(endpoint)
        if not isinstance(position, dict):
            raise ArtifactError(f"{declaration_name} has a malformed {range_name}")
        line = position.get("line")
        column = position.get("column")
        if (
            not isinstance(line, int)
            or isinstance(line, bool)
            or not isinstance(column, int)
            or isinstance(column, bool)
            or line < 0
            or column < 0
        ):
            raise ArtifactError(f"{declaration_name} has an invalid {range_name}")
        positions.append((line, column))
    if positions[0] > positions[1]:
        raise ArtifactError(f"{declaration_name} has a reversed {range_name}")
    line_count = len(content.split("\n"))
    if any(line >= line_count for line, _column in positions):
        raise ArtifactError(f"{declaration_name} has an out-of-bounds {range_name}")


def _transition_graph_data(edge: dict[str, Any]) -> dict[str, Any]:
    constructor = edge.get("constructor")
    if not isinstance(constructor, str):
        raise ArtifactError("compiled transition lacks a Lean constructor")
    return {
        "id": edge.get("edgeId"),
        "label": constructor.rsplit(".", 1)[-1],
        "kind": "ctTransition",
        "ordinal": edge.get("ordinal"),
        "source": edge.get("sourceNode"),
        "target": edge.get("targetNode"),
        "constructor": constructor,
        "constructorType": edge.get("constructorType"),
        "provision": edge.get("provision"),
    }


def _validate_tactic_graph(
    tactic: dict[str, Any], graph: dict[str, Any]
) -> None:
    tactic_id = tactic["tacticId"]
    elements = graph.get("elements")
    if graph.get("tacticId") != tactic_id or not isinstance(elements, list):
        raise ArtifactError(f"invalid generated Cytoscape graph for {tactic_id}")
    data_items: list[dict[str, Any]] = []
    for element in elements:
        data = element.get("data") if isinstance(element, dict) else None
        if not isinstance(data, dict) or not isinstance(data.get("id"), str):
            raise ArtifactError(f"{tactic_id} Cytoscape graph has a malformed element")
        data_items.append(data)
    element_ids = [data["id"] for data in data_items]
    if len(element_ids) != len(set(element_ids)):
        raise ArtifactError(f"{tactic_id} Cytoscape graph repeats an element ID")

    expected_nodes = {
        node["nodeId"]: {
            "id": node["nodeId"],
            "label": node["nodeId"],
            "kind": node["nodeKind"],
            "automation": node["automation"],
            "formalContract": node["formalContract"],
        }
        for node in tactic.get("nodes", [])
    }
    actual_nodes = {
        data["id"]: data
        for data in data_items
        if "source" not in data
        and "target" not in data
        and data.get("kind") != "transitionProfile"
    }
    if actual_nodes != expected_nodes:
        raise ArtifactError(
            f"{tactic_id} Cytoscape nodes disagree with the compiled catalog"
        )

    expected_transitions = {
        edge["edgeId"]: _transition_graph_data(edge)
        for edge in tactic.get("transitions", [])
    }
    actual_transitions = {
        data["id"]: data
        for data in data_items
        if "source" in data or "target" in data
    }
    if actual_transitions != expected_transitions:
        missing = sorted(set(expected_transitions) - set(actual_transitions))
        extra = sorted(set(actual_transitions) - set(expected_transitions))
        changed = sorted(
            edge_id
            for edge_id in set(expected_transitions) & set(actual_transitions)
            if expected_transitions[edge_id] != actual_transitions[edge_id]
        )
        raise ArtifactError(
            f"{tactic_id} Cytoscape transitions disagree with the compiled catalog: "
            f"missing={missing}, extra={extra}, changed={changed}"
        )


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

    def __init__(
        self,
        root: Path | None = None,
        *,
        allow_stale_hashes: bool | None = None,
    ) -> None:
        if allow_stale_hashes is None:
            allow_stale_hashes = os.environ.get(
                "STRUCTURAL_EXHAUSTION_ALLOW_STALE_HASHES", ""
            ).lower() in {"1", "true", "yes"}
        self.allow_stale_hashes = allow_stale_hashes
        self.artifact_warnings: list[dict[str, str]] = []
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
        if self.catalog.get("schemaVersion") != "9.0.0" or set(self.catalog) != {
            "artifactType",
            "schemaVersion",
            "sourceOfTruth",
            "provisionTaxonomy",
            "tactics",
            "transitionFamilies",
            "transitionProfiles",
        }:
            raise ArtifactError("web explorer requires the schema-9 transition catalog")
        self.catalog_hash = _sha256(self.catalog_path)
        self.documentation_path = self.root / "generated/framework-documentation.json"
        self.documentation = _load_object(self.documentation_path)
        self.documentation_hash = _sha256(self.documentation_path)
        self.manifest = _load_object(self.root / "generated/manifest.json")
        self.verification = _load_object(
            self.root / "generated/kernel-verification.json"
        )
        self.verification_status = verification_view(
            self.catalog_hash, self.verification
        )

        tactics = self.catalog.get("tactics")
        transition_families = self.catalog.get("transitionFamilies")
        transition_profiles = self.catalog.get("transitionProfiles")
        if not isinstance(tactics, list) or not tactics:
            raise ArtifactError("compiled catalog has no tactic list")
        if not isinstance(transition_families, list) or not transition_families:
            raise ArtifactError("compiled catalog has no transition-family list")
        if not isinstance(transition_profiles, list) or not transition_profiles:
            raise ArtifactError("compiled catalog has no transition-profile list")

        self.tactics: dict[str, dict[str, Any]] = {}
        self.graphs: dict[str, dict[str, Any]] = {}
        self.internal_paths: dict[str, Path] = {}
        self._internals: dict[str, dict[str, Any]] = {}
        manifest_tactics = self.manifest.get("tactics")
        if not isinstance(manifest_tactics, list):
            raise ArtifactError("generated manifest has no tactic list")
        manifest_by_id = {
            item.get("tacticId"): item
            for item in manifest_tactics
            if isinstance(item, dict) and isinstance(item.get("tacticId"), str)
        }
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
            _validate_tactic_graph(tactic, graph)
            self.tactics[tactic_id] = tactic
            self.graphs[tactic_id] = graph
            manifest_tactic = manifest_by_id.get(tactic_id)
            internal_ref = (
                manifest_tactic.get("internals")
                if isinstance(manifest_tactic, dict)
                else None
            )
            if not isinstance(internal_ref, str):
                raise ArtifactError(f"manifest lacks node internals for {tactic_id}")
            internal_path = (self.root / internal_ref).resolve()
            internal_root = (self.root / "generated/internals").resolve()
            if internal_root not in internal_path.parents or internal_path.suffix != ".json":
                raise ArtifactError(f"manifest has an unsafe internals path for {tactic_id}")
            self.internal_paths[tactic_id] = internal_path

        self.residual_owner = {
            residual["residualKindId"]: tactic_id
            for tactic_id, tactic in self.tactics.items()
            for residual in tactic.get("residualKinds", [])
            if isinstance(residual, dict)
            and isinstance(residual.get("residualKindId"), str)
        }
        self.transition_profiles = [
            self._transition_profile_view(profile)
            for profile in transition_profiles
        ]
        self.transition_profile_by_id = {
            profile["profileId"]: profile for profile in self.transition_profiles
        }
        if len(self.transition_profile_by_id) != len(self.transition_profiles):
            raise ArtifactError("compiled catalog repeats a transition profile")
        self.transition_families = [
            self._transition_family_view(family)
            for family in transition_families
        ]
        if len({family["familyId"] for family in self.transition_families}) != len(
            self.transition_families
        ):
            raise ArtifactError("compiled catalog repeats a transition family")

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
        self.erdos_proof_history_path = self.example_root / "erdos-64-history.json"
        if self.erdos_proof_history_path.is_file():
            self.erdos_proof_history = _load_object(self.erdos_proof_history_path)
            _validate_erdos_proof_history(self.erdos_proof_history)
            erdos_detail_path = self.example_root / "erdos-64.json"
            snapshots = self.erdos_proof_history["snapshots"]
            if not snapshots or snapshots[-1]["artifactSha256"] != _sha256(
                erdos_detail_path
            ):
                self._handle_stale_hash(
                    "Erdos proof history does not record the current example artifact"
                )
        else:
            self.erdos_proof_history = {
                "artifactType": "erdosProofHistory",
                "schemaVersion": "1.0.0",
                "exampleId": "erdos-64",
                "snapshots": [],
            }
        self.implemented_transitions = self._implemented_transition_views()
        self.documentation_capabilities, self.documentation_tactic_guides = (
            self._validate_documentation()
        )

    def _validate_documentation(
        self,
    ) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        if (
            self.documentation.get("artifactType")
            != "structuralExhaustionFrameworkDocumentation"
            or self.documentation.get("schemaVersion") != "1.0.0"
        ):
            raise ArtifactError("framework documentation has an unsupported schema")
        source = self.documentation.get("sourceOfTruth")
        capabilities = self.documentation.get("capabilities")
        guides = self.documentation.get("tacticGuides")
        if not isinstance(source, dict) or not isinstance(capabilities, list) or not isinstance(guides, list):
            raise ArtifactError("framework documentation has malformed top-level data")
        capability_ids: set[str] = set()
        projected: list[dict[str, Any]] = []
        for capability in capabilities:
            if not isinstance(capability, dict):
                raise ArtifactError("framework documentation contains a non-object capability")
            capability_id = capability.get("capabilityId")
            layer = capability.get("layer")
            declarations = capability.get("declarations")
            related_tactics = capability.get("relatedTacticIds")
            related_capabilities = capability.get("relatedCapabilityIds")
            references = capability.get("examples")
            if (
                not isinstance(capability_id, str)
                or not capability_id
                or capability_id in capability_ids
                or layer not in {"core", "graph"}
                or not isinstance(declarations, list)
                or not declarations
                or not all(isinstance(item, str) and item for item in declarations)
                or not isinstance(related_tactics, list)
                or not set(related_tactics).issubset(self.tactics)
                or not isinstance(related_capabilities, list)
                or not isinstance(references, list)
            ):
                raise ArtifactError("framework documentation has an invalid capability")
            capability_ids.add(capability_id)
            enriched_references: list[dict[str, Any]] = []
            for reference in references:
                if not isinstance(reference, dict):
                    raise ArtifactError(f"documentation capability {capability_id} has an invalid example")
                example_id = reference.get("exampleId")
                workflow_id = reference.get("workflowId")
                if example_id == "erdos-64":
                    raise ArtifactError("general framework documentation must not embed the Erdos proof")
                example = self.examples.get(example_id)
                if example is None:
                    self._handle_stale_hash(
                        f"documentation capability {capability_id} references an unknown example"
                    )
                    continue
                workflow = next(
                    (
                        item
                        for item in example.get("workflows", [])
                        if item.get("workflowId") == workflow_id
                    ),
                    None,
                )
                if workflow is None:
                    self._handle_stale_hash(
                        f"documentation capability {capability_id} references an unknown workflow"
                    )
                    continue
                enriched_references.append(
                    {
                        **reference,
                        "exampleTitle": example.get("title"),
                        "workflow": workflow,
                    }
                )
            projected.append({**capability, "examples": enriched_references})
        for capability in projected:
            if not set(capability["relatedCapabilityIds"]).issubset(capability_ids):
                raise ArtifactError(
                    f"documentation capability {capability['capabilityId']} has a dangling relationship"
                )
        guide_ids = [guide.get("tacticId") for guide in guides if isinstance(guide, dict)]
        if len(guide_ids) != len(guides) or len(set(guide_ids)) != len(guide_ids) or set(guide_ids) != set(self.tactics):
            raise ArtifactError("framework documentation tactic guides do not cover CT1-CT17")
        return projected, guides

    def _handle_stale_hash(self, message: str) -> None:
        """Reject stale hashes normally, but retain safe embedded data in web-dev mode."""

        if not self.allow_stale_hashes:
            raise ArtifactError(message)
        warning = {
            "code": "staleHash",
            "message": (
                f"{message}. Showing the last generated embedded content; "
                "run make generate when the source changes are complete."
            ),
        }
        if warning in self.artifact_warnings:
            return
        self.artifact_warnings.append(warning)
        LOGGER.warning("STALE ARTIFACT: %s", warning["message"])

    def _transition_profile_view(self, profile: Any) -> dict[str, Any]:
        if not isinstance(profile, dict):
            raise ArtifactError("compiled catalog contains an invalid transition profile")
        profile_id = profile.get("profileId")
        residual = profile.get("sourceResidualKind")
        source = profile.get("sourceTacticId")
        target = profile.get("targetTacticId")
        owner = self.residual_owner.get(residual)
        family_id = f"{source}->{target}"
        target_interface = profile.get("targetExecutableInterface")
        constructor = profile.get("transitionConstructor")
        advance = profile.get("advanceExecutor")
        if (
            not isinstance(profile_id, str)
            or owner != source
            or target not in self.tactics
            or profile.get("familyId") != family_id
            or not isinstance(target_interface, str)
            or not target_interface.startswith(f"StructuralExhaustion.{target}.")
            or not target_interface.endswith("executableInterface")
            or not isinstance(constructor, str)
            or not constructor.startswith("StructuralExhaustion.Routes.")
            or not constructor.endswith(".transition")
            or not isinstance(advance, str)
            or not advance.startswith("StructuralExhaustion.Routes.")
            or not advance.endswith(".advance")
        ):
            raise ArtifactError(
                f"transition profile {profile_id or '<unknown>'} is malformed"
            )
        return profile

    def _transition_family_view(self, family: Any) -> dict[str, Any]:
        if not isinstance(family, dict):
            raise ArtifactError("compiled catalog contains an invalid transition family")
        source = family.get("sourceTacticId")
        target = family.get("targetTacticId")
        family_id = family.get("familyId")
        profile_ids = family.get("profileIds")
        expected_ids = [
            profile["profileId"]
            for profile in self.transition_profiles
            if profile["familyId"] == family_id
        ]
        if (
            source not in self.tactics
            or target not in self.tactics
            or family_id != f"{source}->{target}"
            or not isinstance(profile_ids, list)
            or profile_ids != expected_ids
        ):
            raise ArtifactError(
                f"transition family {family_id or '<unknown>'} is malformed"
            )
        return family

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
            self._handle_stale_hash(
                f"example {example_id} detail hash does not match its index"
            )
        detail = _load_object(detail_path)
        if detail.get("exampleId") != example_id:
            raise ArtifactError(f"example detail id does not match {example_id}")
        source_of_truth = detail.get("sourceOfTruth")
        descriptor_source = (
            source_of_truth.get("descriptorSource")
            if isinstance(source_of_truth, dict)
            else None
        )
        if descriptor_source is not None:
            if not isinstance(descriptor_source, dict):
                raise ArtifactError(f"example {example_id} has malformed descriptor provenance")
            descriptor_path = descriptor_source.get("path")
            descriptor_hash = descriptor_source.get("sha256")
            if not isinstance(descriptor_path, str) or not isinstance(descriptor_hash, str):
                raise ArtifactError(f"example {example_id} has malformed descriptor provenance")
            candidate = (self.root / descriptor_path).resolve()
            if (
                candidate != self.root
                and self.root not in candidate.parents
            ) or candidate.suffix != ".lean" or not candidate.is_file():
                raise ArtifactError(f"example {example_id} has an unsafe descriptor source")
            if _sha256(candidate) != descriptor_hash:
                self._handle_stale_hash(
                    f"example {example_id} descriptor source has changed since export"
                )
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

    def _implemented_transition_views(self) -> list[dict[str, Any]]:
        """Project every compiled workflow link whose endpoints are distinct CTs."""

        allowed_kinds = {
            "registeredRoute",
            "registeredTransition",
            "frameworkComposition",
            "proofData",
            "validation",
            "scheduleAudit",
            "sharedProblem",
        }
        projected: list[dict[str, Any]] = []
        transition_ids: set[str] = set()
        for example_id, example in self.examples.items():
            for workflow in example.get("workflows", []):
                workflow_id = workflow.get("workflowId")
                if not isinstance(workflow_id, str):
                    raise ArtifactError(
                        f"example {example_id} has a workflow without an ID"
                    )
                stages = {
                    stage["stageId"]: stage for stage in workflow.get("stages", [])
                }
                for link in workflow.get("links", []):
                    source = stages[link["sourceStageId"]]
                    target = stages[link["targetStageId"]]
                    source_tactic = source.get("tacticId")
                    target_tactic = target.get("tacticId")
                    if (
                        not isinstance(source_tactic, str)
                        or not isinstance(target_tactic, str)
                        or source_tactic == target_tactic
                    ):
                        continue
                    relationship_kind = link.get("kind")
                    if relationship_kind not in allowed_kinds:
                        raise ArtifactError(
                            f"example {example_id} has an unsupported CT relationship"
                        )
                    projected_relationship_kind = (
                        "registeredTransition"
                        if relationship_kind == "registeredRoute"
                        else relationship_kind
                    )
                    transition_id = (
                        f"implemented:{example_id}:{workflow_id}:{link['linkId']}"
                    )
                    if transition_id in transition_ids:
                        raise ArtifactError(
                            f"compiled examples repeat transition {transition_id}"
                        )
                    transition_ids.add(transition_id)
                    projected.append(
                        {
                            "transitionId": transition_id,
                            "sourceTacticId": source_tactic,
                            "targetTacticId": target_tactic,
                            "relationshipKind": projected_relationship_kind,
                            "automationClass": (
                                "registeredTransition"
                                if relationship_kind in {
                                    "registeredRoute",
                                    "registeredTransition",
                                }
                                else "frameworkAudit"
                                if relationship_kind == "scheduleAudit"
                                else "frameworkExecutor"
                            ),
                            "frameworkAutomated": True,
                            "automationDeclarationIds": link.get(
                                "automationDeclarationIds", []
                            ),
                            "label": link.get("label"),
                            "summary": link.get("summary"),
                            "exampleId": example_id,
                            "exampleTitle": example.get("title"),
                            "workflowId": workflow_id,
                            "workflowTitle": workflow.get("title"),
                            "workflowCompletion": workflow.get("completion"),
                            "linkId": link["linkId"],
                            "sourceStageId": source["stageId"],
                            "sourceStageTitle": source.get("title"),
                            "sourceDeclarationId": source.get(
                                "primaryDeclarationId"
                            ),
                            "targetStageId": target["stageId"],
                            "targetStageTitle": target.get("title"),
                            "targetDeclarationId": target.get(
                                "primaryDeclarationId"
                            ),
                            "transitionProfileId": link.get(
                                "transitionProfileId", link.get("routeId")
                            ),
                            "evidenceDeclarationIds": link.get(
                                "evidenceDeclarationIds", []
                            ),
                        }
                    )
        return projected

    def _validate_example_detail(self, detail: dict[str, Any]) -> None:
        example_id = str(detail.get("exampleId", "<unknown>"))
        if detail.get("schemaVersion") != "1.4.0":
            raise ArtifactError(f"example {example_id} has an unsupported detail schema")
        tactic_ids = detail.get("tacticIds")
        workflows = detail.get("workflows")
        declarations = detail.get("declarations")
        sources = detail.get("sources")
        bindings = detail.get("interfaceBindings", [])
        manuscript = detail.get("manuscript")
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
                self._handle_stale_hash(
                    f"example {example_id} source hash mismatch for {path}"
                )
            if source_id in source_ids:
                raise ArtifactError(f"example {example_id} repeats source {source_id}")
            source_ids.add(source_id)
            source_line_counts[source_id] = len(content.splitlines())

        declaration_ids: set[str] = set()
        declaration_sources: dict[str, str] = {}
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
            declaration_sources[declaration_id] = source_id

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
                relationship_kind = link.get("kind")
                if relationship_kind not in {
                    "registeredRoute",
                    "registeredTransition",
                    "frameworkComposition",
                    "proofData",
                    "validation",
                    "scheduleAudit",
                    "sharedProblem",
                }:
                    raise ArtifactError(
                        f"example {example_id} has an unsupported link kind"
                    )
                expected_link_fields = {
                    "linkId",
                    "sourceStageId",
                    "targetStageId",
                    "kind",
                    "label",
                    "summary",
                    "automationDeclarationIds",
                    "evidenceDeclarationIds",
                }
                if relationship_kind == "registeredTransition":
                    expected_link_fields.add("transitionProfileId")
                if relationship_kind == "registeredRoute":
                    expected_link_fields.add("routeId")
                if set(link) != expected_link_fields:
                    raise ArtifactError(
                        f"example {example_id} link fields do not match its kind"
                    )
                link_id = link.get("linkId")
                if not isinstance(link_id, str) or link_id in link_ids:
                    raise ArtifactError(f"example {example_id} repeats link {link_id}")
                if link.get("sourceStageId") not in local_stage_ids or link.get(
                    "targetStageId"
                ) not in local_stage_ids:
                    raise ArtifactError(f"example {example_id} link has invalid endpoints")
                automation = link.get("automationDeclarationIds", [])
                evidence = link.get("evidenceDeclarationIds", [])
                if not isinstance(automation, list) or not set(automation).issubset(
                    declaration_ids
                ):
                    raise ArtifactError(
                        f"example {example_id} link has invalid automation declarations"
                    )
                if not isinstance(evidence, list) or not set(evidence).issubset(
                    declaration_ids
                ):
                    raise ArtifactError(f"example {example_id} link has invalid evidence")
                source_stage = stage_by_id[link["sourceStageId"]]
                target_stage = stage_by_id[link["targetStageId"]]
                source_tactic = source_stage.get("tacticId")
                target_tactic = target_stage.get("tacticId")
                if (
                    isinstance(source_tactic, str)
                    and isinstance(target_tactic, str)
                    and source_tactic != target_tactic
                    and not automation
                ):
                    raise ArtifactError(
                        f"example {example_id} cross-CT link lacks framework automation"
                    )
                if any(
                    not declaration_sources[declaration_id].startswith(
                        "StructuralExhaustion."
                    )
                    or declaration_sources[declaration_id].startswith(
                        "StructuralExhaustion.Graph.External."
                    )
                    for declaration_id in automation
                ):
                    raise ArtifactError(
                        f"example {example_id} link automation is not framework-owned"
                    )
                if relationship_kind == "registeredTransition":
                    profile = self.transition_profile_by_id.get(
                        link.get("transitionProfileId")
                    )
                    if profile is None:
                        raise ArtifactError(
                            f"example {example_id} has an unknown transition profile"
                        )
                    if source_stage.get("tacticId") != profile["sourceTacticId"]:
                        raise ArtifactError(
                            f"example {example_id} transition source disagrees"
                        )
                    if target_stage.get("tacticId") != profile["targetTacticId"]:
                        raise ArtifactError(
                            f"example {example_id} transition target disagrees"
                        )
                    if automation != [profile["advanceExecutor"]]:
                        raise ArtifactError(
                            f"example {example_id} transition does not use its "
                            "canonical full-ledger advance executor"
                        )
                elif relationship_kind == "registeredRoute":
                    # Compatibility for committed example artifacts produced by
                    # schema 1.3.  Route IDs became transition-profile IDs in
                    # schema 1.4; the endpoints must still agree with the
                    # current compiled profile.  Legacy routes deliberately do
                    # not claim the newer full-ledger `advance` executor.
                    profile = self.transition_profile_by_id.get(link.get("routeId"))
                    if profile is None:
                        raise ArtifactError(
                            f"example {example_id} has an unknown legacy route"
                        )
                    if source_stage.get("tacticId") != profile["sourceTacticId"]:
                        raise ArtifactError(
                            f"example {example_id} legacy route source disagrees"
                        )
                    if target_stage.get("tacticId") != profile["targetTacticId"]:
                        raise ArtifactError(
                            f"example {example_id} legacy route target disagrees"
                        )
                elif "transitionProfileId" in link:
                    raise ArtifactError(
                        f"example {example_id} non-transition link names a profile"
                    )
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

        if manuscript is not None:
            if not isinstance(manuscript, dict) or not isinstance(
                manuscript.get("proofSteps"), list
            ):
                raise ArtifactError(f"example {example_id} has a malformed manuscript")
            manuscript_path_value = manuscript.get("path")
            manuscript_digest = manuscript.get("sha256")
            fragments = manuscript.get("fragments")
            if (
                not isinstance(manuscript_path_value, str)
                or not isinstance(manuscript_digest, str)
                or not isinstance(fragments, list)
            ):
                raise ArtifactError(f"example {example_id} has malformed manuscript data")
            manuscript_relative = Path(manuscript_path_value)
            if (
                manuscript_relative.is_absolute()
                or ".." in manuscript_relative.parts
                or manuscript_relative.suffix != ".tex"
            ):
                raise ArtifactError(f"example {example_id} has an unsafe manuscript path")
            try:
                manuscript_path = (self.root / manuscript_relative).resolve(strict=True)
                manuscript_path.relative_to(self.root)
            except (OSError, ValueError) as error:
                raise ArtifactError(
                    f"example {example_id} manuscript is unavailable"
                ) from error
            manuscript_is_stale = _sha256(manuscript_path) != manuscript_digest
            if manuscript_is_stale:
                self._handle_stale_hash(
                    f"example {example_id} manuscript hash is stale"
                )
            manuscript_source = manuscript_path.read_text(encoding="utf-8")
            manuscript_line_count = len(manuscript_source.splitlines())
            fragment_labels: set[str] = set()
            fragment_kinds: dict[str, str] = {}
            for fragment in fragments:
                if not isinstance(fragment, dict):
                    raise ArtifactError(
                        f"example {example_id} has a malformed manuscript fragment"
                    )
                label = fragment.get("label")
                source_line = fragment.get("sourceLine")
                blocks = fragment.get("blocks")
                if not isinstance(label, str) or label in fragment_labels:
                    raise ArtifactError(
                        f"example {example_id} repeats a manuscript fragment"
                    )
                if (
                    not isinstance(source_line, int)
                    or isinstance(source_line, bool)
                    or source_line < 1
                    or (
                        source_line > manuscript_line_count
                        and not (self.allow_stale_hashes and manuscript_is_stale)
                    )
                ):
                    raise ArtifactError(
                        f"example {example_id} manuscript fragment has an invalid line"
                    )
                if fragment.get("contentSha256") != _canonical_object_hash(blocks):
                    self._handle_stale_hash(
                        f"example {example_id} manuscript fragment hash mismatch"
                    )
                _validate_manuscript_blocks(blocks, self._handle_stale_hash)
                fragment_labels.add(label)
                environment = fragment.get("environment")
                if not isinstance(environment, str):
                    raise ArtifactError(
                        f"example {example_id} manuscript fragment has no environment"
                    )
                fragment_kinds[label] = environment
            proof_step_ids: set[str] = set()
            mapped_stage_ids: set[str] = set()
            explained_declarations: set[str] = set()
            referenced_labels: set[str] = set()
            verified_mathematical_objects: set[str] = set()
            formalized_node_ids = manuscript.get("formalizedNodeIds")
            if (
                not isinstance(formalized_node_ids, list)
                or any(
                    not isinstance(node_id, int)
                    or isinstance(node_id, bool)
                    or node_id < 1
                    for node_id in formalized_node_ids
                )
                or len(set(formalized_node_ids)) != len(formalized_node_ids)
            ):
                raise ArtifactError(
                    f"example {example_id} has invalid formalized diagram nodes"
                )
            formalized_diagram_nodes = set(formalized_node_ids)
            implemented_reference_nodes: set[int] = set()
            implemented_step_count = 0
            for step in manuscript["proofSteps"]:
                if not isinstance(step, dict):
                    raise ArtifactError(f"example {example_id} has a malformed proof step")
                step_id = step.get("stepId")
                if not isinstance(step_id, str) or step_id in proof_step_ids:
                    raise ArtifactError(f"example {example_id} repeats proof step {step_id}")
                stage_id = step.get("stageId")
                status = step.get("status")
                if status == "implemented":
                    if stage_id not in stage_ids or stage_id in mapped_stage_ids:
                        raise ArtifactError(
                            f"example {example_id} proof step has invalid stage"
                        )
                    mapped_stage_ids.add(stage_id)
                    implemented_step_count += 1
                elif stage_id is not None:
                    raise ArtifactError(
                        f"example {example_id} unimplemented proof step has a stage"
                    )
                groups = step.get("declarationGroups")
                manuscript_refs = step.get("manuscriptRefs")
                if not isinstance(groups, list):
                    raise ArtifactError(
                        f"example {example_id} proof step has malformed groups"
                    )
                if not isinstance(manuscript_refs, list):
                    raise ArtifactError(
                        f"example {example_id} proof step has malformed manuscript refs"
                    )
                local_labels: set[str] = set()
                for reference in manuscript_refs:
                    label = reference.get("label") if isinstance(reference, dict) else None
                    if not isinstance(label, str) or label in local_labels:
                        raise ArtifactError(
                            f"example {example_id} proof step repeats a manuscript label"
                        )
                    local_labels.add(label)
                    referenced_labels.add(label)
                    node_ids = reference.get("nodeIds")
                    if not isinstance(node_ids, list) or not all(
                        isinstance(node_id, int) and not isinstance(node_id, bool)
                        for node_id in node_ids
                    ):
                        raise ArtifactError(
                            f"example {example_id} proof step has invalid diagram nodes"
                        )
                    if status == "implemented":
                        if fragment_kinds.get(label) in MATHEMATICAL_OBJECT_KINDS:
                            verified_mathematical_objects.add(label)
                        implemented_reference_nodes.update(node_ids)
                local_declarations: set[str] = set()
                for group in groups:
                    ids = group.get("declarationIds") if isinstance(group, dict) else None
                    if not isinstance(ids, list) or not set(ids).issubset(declaration_ids):
                        raise ArtifactError(
                            f"example {example_id} proof step has invalid declarations"
                        )
                    if local_declarations.intersection(ids):
                        raise ArtifactError(
                            f"example {example_id} classifies a declaration twice"
                        )
                    local_declarations.update(ids)
                explained_declarations.update(local_declarations)
                proof_step_ids.add(step_id)
            node_obligations = manuscript.get("nodeObligations", [])
            if not isinstance(node_obligations, list):
                raise ArtifactError(
                    f"example {example_id} has malformed node obligations"
                )
            obligation_ids: set[str] = set()
            obligations_by_node: dict[int, list[dict[str, Any]]] = {}
            proof_steps_by_id = {
                step.get("stepId"): step
                for step in manuscript["proofSteps"]
                if isinstance(step, dict)
            }
            for obligation in node_obligations:
                if not isinstance(obligation, dict):
                    raise ArtifactError(
                        f"example {example_id} has a malformed node obligation"
                    )
                node_id = obligation.get("nodeId")
                obligation_id = obligation.get("obligationId")
                status = obligation.get("status")
                evidence_step_ids = obligation.get("evidenceStepIds")
                if (
                    not isinstance(node_id, int)
                    or isinstance(node_id, bool)
                    or node_id < 1
                    or not isinstance(obligation_id, str)
                    or not obligation_id
                    or obligation_id in obligation_ids
                    or status not in {"proved", "partial", "missing"}
                    or not isinstance(evidence_step_ids, list)
                    or len(set(evidence_step_ids)) != len(evidence_step_ids)
                ):
                    raise ArtifactError(
                        f"example {example_id} has an invalid node obligation"
                    )
                obligation_ids.add(obligation_id)
                if status == "missing" and evidence_step_ids:
                    raise ArtifactError(
                        f"example {example_id} missing obligation claims evidence"
                    )
                if status != "missing" and not evidence_step_ids:
                    raise ArtifactError(
                        f"example {example_id} non-missing obligation lacks evidence"
                    )
                for step_id in evidence_step_ids:
                    step = proof_steps_by_id.get(step_id)
                    if not isinstance(step_id, str) or step is None:
                        raise ArtifactError(
                            f"example {example_id} obligation has dangling evidence"
                        )
                    if status != "missing" and step.get("status") != "implemented":
                        raise ArtifactError(
                            f"example {example_id} non-missing obligation uses unfinished evidence"
                        )
                    if not any(
                        node_id in reference.get("nodeIds", [])
                        for reference in step.get("manuscriptRefs", [])
                        if isinstance(reference, dict)
                    ):
                        raise ArtifactError(
                            f"example {example_id} obligation evidence cites another node"
                        )
                obligations_by_node.setdefault(node_id, []).append(obligation)
            for node_id, obligations in obligations_by_node.items():
                all_proved = all(
                    obligation["status"] == "proved" for obligation in obligations
                )
                if all_proved != (node_id in formalized_diagram_nodes):
                    raise ArtifactError(
                        f"example {example_id} node status disagrees with obligations"
                    )
            if referenced_labels != fragment_labels:
                raise ArtifactError(
                    f"example {example_id} rendered manuscript label coverage is stale"
                )
            if mapped_stage_ids != stage_ids:
                raise ArtifactError(
                    f"example {example_id} manuscript does not cover every stage"
                )
            if not formalized_diagram_nodes <= implemented_reference_nodes:
                raise ArtifactError(
                    f"example {example_id} formalized nodes lack Lean evidence"
                )
            coverage = manuscript.get("coverage")
            expected_coverage = {
                "implementedSteps": implemented_step_count,
                "totalSteps": len(proof_step_ids),
                "explainedDeclarations": len(explained_declarations),
                "displayedDeclarations": len(declaration_ids),
                "verifiedMathematicalObjects": len(
                    verified_mathematical_objects
                ),
                "verifiedDiagramNodes": len(formalized_diagram_nodes),
                "verifiedWorkflowSteps": implemented_step_count,
            }
            if not isinstance(coverage, dict) or any(
                coverage.get(key) != value
                for key, value in expected_coverage.items()
            ):
                raise ArtifactError(f"example {example_id} manuscript coverage is stale")
            total_objects = coverage.get("totalMathematicalObjects")
            total_nodes = coverage.get("totalDiagramNodes")
            if (
                not isinstance(total_objects, int)
                or isinstance(total_objects, bool)
                or total_objects < len(verified_mathematical_objects)
                or not isinstance(total_nodes, int)
                or isinstance(total_nodes, bool)
                or total_nodes < len(formalized_diagram_nodes)
            ):
                raise ArtifactError(f"example {example_id} manuscript totals are invalid")
            if not manuscript_is_stale:
                source_object_labels = set(
                    TYPED_MATHEMATICAL_LABEL_PATTERN.findall(manuscript_source)
                ) | set(
                    ENVIRONMENT_MATHEMATICAL_LABEL_PATTERN.findall(manuscript_source)
                )
                source_diagram_nodes = {
                    int(value) for value in DIAGRAM_NODE_PATTERN.findall(manuscript_source)
                }
                if (
                    total_objects != len(source_object_labels)
                    or total_nodes != len(source_diagram_nodes)
                ):
                    raise ArtifactError(
                        f"example {example_id} manuscript total coverage is stale"
                    )
            if explained_declarations != declaration_ids:
                raise ArtifactError(
                    f"example {example_id} manuscript leaves declarations unexplained"
                )

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
            "artifactWarnings": self.artifact_warnings,
            "catalog": self.catalog_view,
            "verification": self.verification_status,
            "exampleCatalog": self.example_catalog_view,
            "exampleVerification": self.example_verification_status,
            "totals": {
                "tactics": len(summaries),
                "nodes": sum(item["nodeCount"] for item in summaries),
                "transitions": sum(item["transitionCount"] for item in summaries),
                "terminals": sum(item["terminalCount"] for item in summaries),
                "residualKinds": sum(item["residualCount"] for item in summaries),
                "transitionFamilies": len(self.transition_families),
                "transitionProfiles": len(self.transition_profiles),
                "implementedTransitions": len(self.implemented_transitions),
                "manualObligations": sum(
                    item["manualObligationCount"] for item in summaries
                ),
            },
            "tactics": summaries,
            "transitionFamilies": self.transition_families,
            "transitionProfiles": self.transition_profiles,
            "implementedTransitions": self.implemented_transitions,
        }

    def documentation_response(self) -> dict[str, Any]:
        return {
            "artifactType": "frameworkExplorerDocumentation",
            "artifactWarnings": self.artifact_warnings,
            "schemaVersion": self.documentation["schemaVersion"],
            "catalogHash": self.documentation_hash,
            "sourceOfTruth": self.documentation["sourceOfTruth"],
            "verification": self.verification_status,
            "capabilities": self.documentation_capabilities,
            "tacticGuides": self.documentation_tactic_guides,
        }

    def tactic_response(self, tactic_id: str) -> dict[str, Any] | None:
        tactic = self.tactics.get(tactic_id)
        if tactic is None:
            return None
        # The declaration closure and source text are intentionally served by the
        # lazy internals endpoint.  Keeping them out of overview responses preserves
        # the existing fast, high-level browsing path.
        overview_tactic = {
            key: value for key, value in tactic.items() if key != "internalDeclarations"
        }
        return {
            "artifactType": "frameworkExplorerTactic",
            "artifactWarnings": self.artifact_warnings,
            "catalogHash": self.catalog_hash,
            "verification": self.verification_status,
            "tactic": overview_tactic,
            "graph": self.graphs[tactic_id],
            "inboundTransitionProfiles": [
                profile
                for profile in self.transition_profiles
                if profile["targetTacticId"] == tactic_id
            ],
            "outboundTransitionProfiles": [
                profile
                for profile in self.transition_profiles
                if profile["sourceTacticId"] == tactic_id
            ],
        }

    def _load_tactic_internals(self, tactic_id: str) -> dict[str, Any]:
        cached = self._internals.get(tactic_id)
        if cached is not None:
            return cached
        tactic = self.tactics[tactic_id]
        value = _load_object(self.internal_paths[tactic_id])
        if value.get("artifactType") != "structuralExhaustionNodeInternals":
            raise ArtifactError(f"invalid node-internals artifact type for {tactic_id}")
        if value.get("schemaVersion") != "1.0.0":
            raise ArtifactError(f"unsupported node-internals schema for {tactic_id}")
        if value.get("tacticId") != tactic_id or value.get("apiVersion") != tactic.get(
            "apiVersion"
        ):
            raise ArtifactError(f"node internals do not match {tactic_id}'s API")

        raw_nodes = value.get("nodes")
        expected_nodes = tactic.get("nodes", [])
        if not isinstance(raw_nodes, list) or len(raw_nodes) != len(expected_nodes):
            raise ArtifactError(f"node internals do not cover every {tactic_id} node")
        flows_by_id: dict[str, Any] = {}
        for item in raw_nodes:
            if not isinstance(item, dict) or not isinstance(item.get("nodeId"), str):
                raise ArtifactError(f"{tactic_id} has a malformed internal node record")
            node_id = item["nodeId"]
            if node_id in flows_by_id or item.get("internalFlow", {}).get(
                "nodeId"
            ) != node_id:
                raise ArtifactError(f"{tactic_id} has inconsistent internal node IDs")
            flows_by_id[node_id] = item.get("internalFlow")
        if set(flows_by_id) != {node["nodeId"] for node in expected_nodes}:
            raise ArtifactError(f"node internals have stale {tactic_id} node IDs")
        for node in expected_nodes:
            if flows_by_id[node["nodeId"]] != node.get("internalFlow"):
                raise ArtifactError(
                    f"node internals disagree with compiled flow {node['nodeId']}"
                )

        raw_declarations = value.get("declarations")
        expected_declarations = tactic.get("internalDeclarations")
        if not isinstance(raw_declarations, list) or not isinstance(
            expected_declarations, list
        ) or len(raw_declarations) != len(expected_declarations):
            raise ArtifactError(f"node internals have stale declarations for {tactic_id}")
        declaration_by_name: dict[str, dict[str, Any]] = {}
        for actual, expected in zip(raw_declarations, expected_declarations, strict=True):
            if not isinstance(actual, dict):
                raise ArtifactError(f"{tactic_id} has a malformed internal declaration")
            compiled_view = {
                key: value
                for key, value in actual.items()
                if key not in {"projectLocal", "sourceId"}
            }
            if compiled_view != expected:
                raise ArtifactError(
                    f"node internals disagree with declaration {expected.get('name')}"
                )
            name = actual.get("name")
            if not isinstance(name, str) or name in declaration_by_name:
                raise ArtifactError(f"{tactic_id} repeats an internal declaration")
            project_local = name.startswith("StructuralExhaustion.")
            if actual.get("projectLocal") is not project_local:
                raise ArtifactError(f"{name} has an invalid project-local marker")
            declaration_by_name[name] = actual
        for declaration in raw_declarations:
            for dependency in declaration.get("typeDependencies", []) + declaration.get(
                "bodyDependencies", []
            ):
                if dependency.startswith("StructuralExhaustion.") and dependency not in declaration_by_name:
                    raise ArtifactError(
                        f"{declaration['name']} has an unexported project dependency {dependency}"
                    )

        raw_sources = value.get("sources")
        if not isinstance(raw_sources, list):
            raise ArtifactError(f"{tactic_id} internal sources must be a list")
        source_by_id: dict[str, dict[str, Any]] = {}
        lean_root = (self.root / "lean").resolve()
        for source in raw_sources:
            if not isinstance(source, dict) or not isinstance(source.get("sourceId"), str):
                raise ArtifactError(f"{tactic_id} has a malformed internal source")
            source_id = source["sourceId"]
            if source_id in source_by_id or not source_id.startswith(
                "StructuralExhaustion/"
            ):
                raise ArtifactError(f"{tactic_id} has an unsafe or repeated source ID")
            source_path = (lean_root / source_id).resolve()
            if lean_root not in source_path.parents or not source_path.is_file():
                raise ArtifactError(f"{tactic_id} source {source_id} is unavailable")
            content = source.get("content")
            if not isinstance(content, str):
                raise ArtifactError(f"{tactic_id} source {source_id} has malformed content")
            if source.get("sha256") != _sha256_text(content):
                self._handle_stale_hash(
                    f"{tactic_id} source {source_id} has a bad hash"
                )
            if source.get("path") != f"lean/{source_id}":
                raise ArtifactError(f"{tactic_id} source {source_id} has an invalid path")
            if content != source_path.read_text(encoding="utf-8"):
                self._handle_stale_hash(f"{tactic_id} source {source_id} is stale")
            source_by_id[source_id] = source
        for declaration in raw_declarations:
            source_id = declaration.get("sourceId")
            if source_id is not None and source_id not in source_by_id:
                raise ArtifactError(
                    f"{declaration['name']} references an unavailable source"
                )
            if source_id is not None and source_id != declaration.get("sourceFile"):
                raise ArtifactError(f"{declaration['name']} has a mismatched source ID")
            if source_id is not None:
                content = source_by_id[source_id]["content"]
                _validate_source_range(
                    declaration["name"], "range", declaration.get("range"), content
                )
                _validate_source_range(
                    declaration["name"],
                    "selection range",
                    declaration.get("selectionRange"),
                    content,
                )

        self._internals[tactic_id] = value
        return value

    def tactic_internals_response(self, tactic_id: str) -> dict[str, Any] | None:
        if tactic_id not in self.tactics:
            return None
        internals = self._load_tactic_internals(tactic_id)
        return {
            "artifactType": "frameworkExplorerTacticInternals",
            "artifactWarnings": self.artifact_warnings,
            "catalogHash": self.catalog_hash,
            "verification": self.verification_status,
            "internals": internals,
        }

    def examples_response(self) -> dict[str, Any]:
        return {
            "artifactType": "frameworkExplorerExamples",
            "artifactWarnings": self.artifact_warnings,
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
            "artifactWarnings": self.artifact_warnings,
            "catalogHash": self.example_catalog_hash,
            "frameworkCatalogHash": self.catalog_hash,
            "verification": self.example_verification_status,
            "example": example,
            "tactics": [
                summaries[tactic_id] for tactic_id in example.get("tacticIds", [])
            ],
        }

    def erdos_proof_history_response(self) -> dict[str, Any]:
        return {
            "artifactType": "frameworkExplorerErdosProofHistory",
            "artifactWarnings": self.artifact_warnings,
            "schemaVersion": self.erdos_proof_history["schemaVersion"],
            "exampleId": self.erdos_proof_history["exampleId"],
            "snapshots": self.erdos_proof_history["snapshots"],
        }
