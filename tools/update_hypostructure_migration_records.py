#!/usr/bin/env python3
"""Create and refresh machine-readable Hypostructure migration inventories."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path

try:
    from tools.extract_eg_original_node_anchors import (
        AnchorExtractionError,
        extract_registry,
        render_registry,
    )
except ModuleNotFoundError:
    from extract_eg_original_node_anchors import (  # type: ignore[no-redef]
        AnchorExtractionError,
        extract_registry,
        render_registry,
    )


NODE_FILE = re.compile(r"Node(?P<node>[0-9]+)\.lean$")
LEGACY_NODE_IMPORT = re.compile(
    r"^import Erdos64EG\.Node(?P<node>[0-9]+)\s*$", re.MULTILINE
)
CT_IMPORT = re.compile(
    r"^import StructuralExhaustion\.CT(?P<ct>[1-9]|1[0-7])(?:\.|$)",
    re.MULTILINE,
)

AUTHORITY_MANIFEST = Path("migration/hypostructure/source-authority.json")
ORIGINAL_NODE_ANCHOR_REGISTRY = Path(
    "migration/hypostructure/eg-original-node-anchors.json"
)
ORIGINAL_NODE_ANCHOR_GENERATOR = "tools/extract_eg_original_node_anchors.py"
ORIGINAL_EG_SOURCE = "original_erdos_64_proof.tex"
ORIGINAL_EG_BYTE_SIZE = 835801
ORIGINAL_EG_SHA256 = (
    "215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10"
)
LIVING_EG_SOURCE = "proofs/erdos_64_eg/erdos_64_proof.tex"
LEGACY_EG_PATHS = [
    "lean/StructuralExhaustion",
    "examples/erdos_64_eg/Erdos64EG/Node*.lean",
]
ORIGINAL_FIRST_STEP = (
    "extract and freeze the exact quantified node contract and original DAG edges"
)
LEGACY_SECOND_STEP = (
    "consult the matching kernel-checked legacy NodeX.lean dependency cone as "
    "implementation and parity evidence"
)
DISCREPANCY_POLICY = (
    "record an issue and block the affected node pending explicit source correction"
)
REQUIRED_PROHIBITED_REQUIREMENTS_SOURCES = {
    LIVING_EG_SOURCE,
    "Future Lean files",
    "generated metadata",
    "legacy Lean imports",
}


class SourceAuthorityError(RuntimeError):
    """Raised before migration writes when the EG authority contract is invalid."""


def _require_authority(condition: bool, detail: str) -> None:
    if not condition:
        raise SourceAuthorityError(
            f"EG source-authority preflight failed: {detail}"
        )


def _authority_section(
    authority: dict[str, object], name: str
) -> dict[str, object]:
    section = authority.get(name)
    _require_authority(
        isinstance(section, dict),
        f"{name} must be a JSON object",
    )
    return section


def validate_eg_source_authority(root: Path) -> None:
    """Validate the immutable EG authority contract without writing anything."""
    manifest_path = root / AUTHORITY_MANIFEST
    try:
        encoded_manifest = manifest_path.read_text(encoding="utf-8")
    except OSError as error:
        raise SourceAuthorityError(
            "EG source-authority preflight failed: cannot read "
            f"{AUTHORITY_MANIFEST}: {error}"
        ) from error

    try:
        loaded = json.loads(encoded_manifest)
    except json.JSONDecodeError as error:
        raise SourceAuthorityError(
            "EG source-authority preflight failed: "
            f"{AUTHORITY_MANIFEST} is not valid JSON: {error}"
        ) from error

    _require_authority(
        isinstance(loaded, dict),
        f"{AUTHORITY_MANIFEST} must contain a JSON object",
    )
    authority: dict[str, object] = loaded
    _require_authority(
        type(authority.get("schema_version")) is int
        and authority["schema_version"] == 1,
        "schema_version must be exactly 1",
    )
    _require_authority(
        authority.get("scope") == "erdos-gyarfas-problem-64",
        "scope must be exactly 'erdos-gyarfas-problem-64'",
    )

    original = _authority_section(authority, "original")
    _require_authority(
        original.get("path") == ORIGINAL_EG_SOURCE,
        f"original.path must be exactly {ORIGINAL_EG_SOURCE!r}",
    )
    _require_authority(
        original.get("role") == "sole EG mathematical and DAG authority",
        "original.role must identify the sole EG mathematical and DAG authority",
    )
    for field in (
        "mathematical_authority",
        "dag_authority",
        "must_not_be_edited",
        "corrections_require_explicit_approval",
    ):
        _require_authority(
            original.get(field) is True,
            f"original.{field} must be true",
        )
    _require_authority(
        type(original.get("byte_size")) is int
        and original["byte_size"] == ORIGINAL_EG_BYTE_SIZE,
        f"original.byte_size must be pinned to {ORIGINAL_EG_BYTE_SIZE}",
    )
    _require_authority(
        original.get("sha256") == ORIGINAL_EG_SHA256,
        f"original.sha256 must be pinned to {ORIGINAL_EG_SHA256}",
    )

    living = _authority_section(authority, "living_proof")
    _require_authority(
        living.get("path") == LIVING_EG_SOURCE,
        f"living_proof.path must be exactly {LIVING_EG_SOURCE!r}",
    )
    _require_authority(
        living.get("role") == "non-binding editorial cross-check only",
        "living_proof.role must remain non-binding editorial evidence",
    )
    for field in ("mathematical_authority", "dag_authority"):
        _require_authority(
            living.get(field) is False,
            f"living_proof.{field} must be false",
        )

    legacy = _authority_section(authority, "legacy_lean")
    _require_authority(
        legacy.get("paths") == LEGACY_EG_PATHS,
        "legacy_lean.paths must identify only the reviewed legacy Lean roots",
    )
    _require_authority(
        legacy.get("role")
        == "kernel-checked implementation and parity evidence only",
        "legacy_lean.role must remain implementation and parity evidence only",
    )
    for field in ("mathematical_authority", "dag_authority"):
        _require_authority(
            legacy.get(field) is False,
            f"legacy_lean.{field} must be false",
        )

    anchors = _authority_section(authority, "original_node_anchor_registry")
    _require_authority(
        anchors.get("path") == ORIGINAL_NODE_ANCHOR_REGISTRY.as_posix(),
        "original_node_anchor_registry.path must name the reviewed locator",
    )
    _require_authority(
        anchors.get("generator") == ORIGINAL_NODE_ANCHOR_GENERATOR,
        "original_node_anchor_registry.generator must name the pinned extractor",
    )
    _require_authority(
        anchors.get("role")
        == "exact diagram locator generated only from the pinned original",
        "original_node_anchor_registry.role must remain locator-only",
    )
    _require_authority(
        anchors.get("scope") == "diagram_anchor_only",
        "original_node_anchor_registry.scope must be diagram_anchor_only",
    )
    for field in ("mathematical_authority", "full_quantified_contract_reviewed"):
        _require_authority(
            anchors.get(field) is False,
            f"original_node_anchor_registry.{field} must be false",
        )

    workflow = _authority_section(authority, "migration_workflow")
    _require_authority(
        workflow.get("requirements_source") == ORIGINAL_EG_SOURCE,
        "migration_workflow.requirements_source must be the original EG proof",
    )
    _require_authority(
        workflow.get("first_step") == ORIGINAL_FIRST_STEP,
        "migration_workflow.first_step must extract original requirements first",
    )
    _require_authority(
        workflow.get("second_step") == LEGACY_SECOND_STEP,
        "migration_workflow.second_step must consult legacy Lean second",
    )
    _require_authority(
        workflow.get("discrepancy_policy") == DISCREPANCY_POLICY,
        "migration_workflow.discrepancy_policy must block on discrepancies",
    )
    prohibited = workflow.get("prohibited_requirements_sources")
    _require_authority(
        isinstance(prohibited, list)
        and all(type(item) is str for item in prohibited),
        "migration_workflow.prohibited_requirements_sources must be a string list",
    )
    missing_prohibited = REQUIRED_PROHIBITED_REQUIREMENTS_SOURCES - set(prohibited)
    _require_authority(
        not missing_prohibited,
        "migration_workflow.prohibited_requirements_sources is missing "
        f"{sorted(missing_prohibited)}",
    )

    source_path = root / ORIGINAL_EG_SOURCE
    try:
        original_bytes = source_path.read_bytes()
    except OSError as error:
        raise SourceAuthorityError(
            "EG source-authority preflight failed: cannot read "
            f"{ORIGINAL_EG_SOURCE}: {error}"
        ) from error
    _require_authority(
        len(original_bytes) == ORIGINAL_EG_BYTE_SIZE,
        f"{ORIGINAL_EG_SOURCE} byte_size is {len(original_bytes)}, "
        f"expected {ORIGINAL_EG_BYTE_SIZE}",
    )
    observed_sha256 = hashlib.sha256(original_bytes).hexdigest()
    _require_authority(
        observed_sha256 == ORIGINAL_EG_SHA256,
        f"{ORIGINAL_EG_SOURCE} sha256 is {observed_sha256}, "
        f"expected {ORIGINAL_EG_SHA256}",
    )

    anchor_path = root / ORIGINAL_NODE_ANCHOR_REGISTRY
    try:
        committed_anchors = anchor_path.read_bytes()
        expected_anchors = render_registry(extract_registry(root))
    except (OSError, AnchorExtractionError) as error:
        raise SourceAuthorityError(
            "EG source-authority preflight failed: cannot verify "
            f"{ORIGINAL_NODE_ANCHOR_REGISTRY}: {error}"
        ) from error
    _require_authority(
        committed_anchors == expected_anchors,
        f"{ORIGINAL_NODE_ANCHOR_REGISTRY} does not match the pinned original",
    )

EG_FIELDS = [
    "node_id",
    "paper_ref",
    "direct_predecessors",
    "legacy_files",
    "legacy_declarations",
    "normalized_input",
    "normalized_outcomes",
    "observed_legacy_ct_ids",
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

SUPPLEMENTAL_LEGACY_FIELDS = [
    "legacy_node_id",
    "source_file",
    "observed_imports",
    "legacy_declarations",
    "normalized_input",
    "normalized_outcomes",
    "observed_ct_ids",
    "legacy_kernel",
    "notes",
]

API_FIELDS = [
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

PDE_FIELDS = [
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


@dataclass(frozen=True)
class Feature:
    feature_id: str
    owner: str
    spec_section: str
    legacy_sources: str
    new_module: str
    first_graph_consumer: str
    first_pde_consumer: str
    fixtures: str
    notes: str = ""


FEATURES = [
    Feature("core.problem", "Core", "core-3", "Core/Problem.lean", "Core/Problem.lean", "EG problem", "PDE LocalModel", "CorePrimitives"),
    Feature("core.progress", "Core", "core-3", "Core/Problem.lean", "Core/Progress.lean", "minimal graph selection", "profile descent", "CorePrimitives"),
    Feature("core.context", "Core", "core-3", "Core/Context.lean", "Core/Context.lean", "EG root", "PDE root", "CorePrimitives"),
    Feature("core.semantic-equivalence", "Core", "core-3", "Graph isomorphism modules", "Core/SemanticEquivalence.lean", "graph isomorphism", "gauge equivalence", "CorePrimitives"),
    Feature("core.proof-ledger", "Core", "core-4.1", "Core/ResidualRefinement.lean", "Core/Residual/Ledger.lean", "EG root", "PDE row chain", "ResidualLedger"),
    Feature("core.typed-query", "Core", "core-4.1", "Core/ResidualRefinement.lean", "Core/Residual/Query.lean", "EG node 2", "PDE row 2", "ResidualLedger"),
    Feature("core.decision", "Core", "core-4.1", "Core/ResidualRefinement.lean", "Core/Residual/Decision.lean", "EG node 2", "PDE sign toy", "ResidualLedger"),
    Feature("core.focus-selection-work", "Core", "core-4.1;core-9", "Core/FocusedActiveContinuation.lean", "Core/Residual/Focus.lean", "EG focused chain", "PDE focused row chain", "Focus;ProofProjection", "Every focus carries a counted selector and polynomial selection budget"),
    Feature("core.focus-refinement", "Core", "core-4.1;core-9", "", "Core/Residual/Focus.lean", "finite-tag branch refinement", "PDE rows 5 and 6", "Focus;PDERow5DirectedExhaustiveness", "Core derives counted child focuses from inherited finite tags; the raw refinement constructor remains private"),
    Feature("core.join", "Core", "core-4.1", "Core/ResidualRefinement.lean", "Core/Residual/Join.lean", "first manuscript join", "PDE merged row", "ResidualLedger"),
    Feature("core.coordinate-system", "Core", "core-5", "domain coordinate modules", "Core/Coordinate/System.lean", "graph restriction", "PDE recentering", "CoordinatesAndAssembly"),
    Feature("core.coordinate-path", "Core", "core-5", "manual domain composition", "Core/Coordinate/Path.lean", "graph composite", "PDE recenter-rescale", "CoordinatesAndAssembly"),
    Feature("core.coordinate-transport", "Core", "core-5", "manual domain transports", "Core/Coordinate/Transport.lean", "graph baseline transport", "PDE equation transport", "CoordinatesAndAssembly"),
    Feature("core.locality", "Core", "core-6", "graph/PDE restriction modules", "Core/Assembly/Locality.lean", "induced support", "nested window", "CoordinatesAndAssembly"),
    Feature("core.atom-context", "Core", "core-6", "Graph boundary replacement", "Core/Assembly/AtomContext.lean", "graph gluing", "local/tail split", "CoordinatesAndAssembly"),
    Feature("core.work-budget", "Core", "core-9", "Core/WorkBudget.lean", "Core/Budget/Work.lean", "finite graph CT", "finite PDE toy", "Budgets"),
    Feature("core.resource-budget", "Core", "core-9", "graph budget modules", "Core/Budget/Resource.lean", "graph charge", "energy/capacity", "Budgets"),
    Feature("core.resource-transcript", "Core", "pde-8", "", "Core/Budget/Transcript.lean", "graph resource fixture", "PDE row 3", "PDERows1To4"),
    Feature("core.continued-decision", "Core", "core-4.1", "Core/ResidualRefinement.lean", "Core/Residual/Decision.lean", "EG node 5", "PDE branch continuation", "Decision"),
    Feature("core.proof-projection", "Core", "core-4.1", "Core/ResidualRefinement.lean", "Core/Residual/ProofProjection.lean", "EG node 12", "PDE derived row fact", "ProofProjection", "Counted focused proposition derived from an exact predecessor query with zero additional projection work"),
    Feature("core.normal-form-class-closure", "Core", "core-10", "", "Core/NormalForm/ClassClosure.lean", "graph closed classes", "PDE quotient closure", "ClassClosureCounted", "Finite avoidance is separated from target-complete whole-quotient zero; the counted generator reports the exact scan work"),
    Feature("core.normal-form-sign-gap", "Core", "core-10", "", "Core/NormalForm/SignGap.lean", "graph budget sign", "PDE flux sign", "NormalForms"),
    Feature("core.normal-form-equality-rigidity", "Core", "core-10", "", "Core/NormalForm/EqualityRigidity.lean", "graph equality class", "PDE rigidity row", "NormalForms"),
    Feature("graph.finite-object", "Graph", "graph-4", "Graph/FiniteObject.lean", "Graph/Object.lean", "EG problem", "", "GraphBasics"),
    Feature("graph.finite-views", "Graph", "graph-4", "Graph finite modules", "Graph/Finite.lean", "EG CT schedules", "", "GraphBasics"),
    Feature("graph.isomorphism", "Graph", "graph-5", "Graph isomorphism modules", "Graph/Isomorphism.lean", "EG target", "", "GraphBasics"),
    Feature("graph.induced", "Graph", "graph-6", "Graph induced modules", "Graph/Induced.lean", "EG deletion", "", "GraphBasics"),
    Feature("graph.deletion", "Graph", "graph-6", "Graph deletion modules", "Graph/Deletion.lean", "EG CT2", "", "GraphBasics"),
    Feature("graph.cycle-target", "Graph", "graph-7", "Graph target modules", "Graph/Target.lean", "EG target", "", "GraphBasics"),
    Feature("graph.rooted-return", "Graph", "graph-7", "Graph/EdgeRootedReturn.lean", "Graph/RootedReturn.lean", "EG node 5", "", "RootedReturn"),
    Feature("graph.proper-subgraph-minimality", "Graph", "graph-6", "Graph/PackedMinimumDegreeCycle.lean", "Graph/Minimality.lean", "EG node 8", "", "GraphMinimality"),
    Feature("graph.deletion-criticality", "Graph", "graph-6", "Graph/DeletionCriticality.lean", "Graph/DeletionCriticality.lean", "EG nodes 9 and 10", "", "GraphDeletionCriticality", "Graph derives endpoint tightness and slack-vertex independence from the literal minimality residual"),
    Feature("graph.atom-response-coordinates", "Graph", "graph-7", "Graph/PackedBoundariedGluing.lean", "Graph/AtomResponse.lean", "EG node 12", "", "GraphAtomResponse", "Arbitrary local response coordinates and any certified target-complete quotient indexed by the registered atom profile"),
    Feature("graph.boundary-overlap", "Graph", "graph-6", "Graph/PackedBoundariedGluing.lean", "Graph/BoundaryOverlap.lean", "EG node 13 obligation", "", "GraphBoundaryOverlap;GraphBoundaryOverlapCounterexample", "Exact unrestricted-gluing inclusion-exclusion without assuming local profiles transfer"),
    Feature("pde.local-atlas", "PDE", "pde-4.2", "", "PDE/Atlas.lean", "", "PDE model", "PDEBasics"),
    Feature("pde.equation", "PDE", "pde-4.3", "", "PDE/Equation.lean", "", "PDE model", "PDEBasics"),
    Feature("pde.local-model", "PDE", "pde-4.1", "", "PDE/Model.lean", "", "NS2D registration", "PDEBasics"),
    Feature("pde.coordinates", "PDE", "pde-5", "", "PDE/Coordinate.lean", "", "recenter/rescale/gauge", "PDEBasics"),
    Feature("pde.local-tail", "PDE", "pde-6", "", "PDE/LocalTail.lean", "", "CZ pressure split", "PDEBasics"),
    Feature("pde.observable", "PDE", "pde-7", "", "PDE/Observable.lean", "", "PDE row 1", "PDERows1To4"),
    Feature("pde.target-interface", "PDE", "pde-7", "", "PDE/Target.lean", "", "PDE row 1", "PDERows1To4"),
    Feature("pde.fast-track-signature", "PDE", "pde-8", "", "PDE/FastTrack/Signature.lean", "", "PDE row 1", "PDERows1To4"),
    Feature("pde.generator-form", "PDE", "pde-8", "", "PDE/GeneratorForm.lean", "", "PDE row 2", "PDERows1To4", "Every form state realizes a valid registered equation state; continuum admissibility remains an explicit PDE-boundary contract"),
    Feature("pde.represented-quotient", "PDE", "pde-8", "", "PDE/Quotient.lean", "", "PDE row 4", "PDERows1To4;RepresentedNS2DQuotientDefectPacket", "Indexed by the exact inherited GeneratorForm; the defect executor reads that form through a typed predecessor query"),
    Feature("pde.defect-geometry", "PDE", "pde-8", "", "PDE/Quotient.lean", "", "PDE row 4", "PDERows1To4;RepresentedNS2DQuotientDefectPacket", "Core decides exact containment of the framework-computed defect; continuum NS2D geometry remains an explicit boundary contract"),
    Feature("pde.structural-gradient", "PDE", "pde-8", "", "PDE/StructuralGradient.lean", "", "PDE row 5", "PDEStructuralGradient;RepresentedNS2DDirectedExhaustivenessPacket", "The PDE layer registers the represented closed densely defined operator and derives closed range only through an explicit positive-gap criterion"),
    Feature("pde.directed-exhaustiveness", "PDE", "pde-8", "", "PDE/FastTrack/DirectedExhaustiveness.lean", "", "PDE row 5", "PDERow5DirectedExhaustiveness;RepresentedNS2DDirectedExhaustivenessPacket", "One focused counted CT15-to-CT16-to-ClassClosure executor; all bridge laws are predecessor-owned active queries"),
    Feature("pde.defect-routing-raw", "PDE", "pde-8", "", "PDE/FastTrack/DefectRouting.lean", "", "PDE row 6 raw execution", "PDERow6DefectRoutingRaw;RepresentedNS2DDefectRoutingPacket", "Kernel-checked source-neutral CT13-to-CT7 transcript and typed unavailable-alignment residual; no analytic or continuum row-6 claim"),
    Feature("pde.direct-resistance", "PDE", "pde-8", "", "PDE/DirectResistance.lean", "", "PDE row 6 analytic alignment", "PDERow6FiniteOrthogonalAlignment;PDERow6FinitePressureGaugeAlignment", "Generic exact-defect orthogonal projection, finite compensator, nonroutable harmonic, energy, and drift contract; no continuum theorem is inferred"),
    Feature("pde.defect-routing-alignment", "PDE", "pde-8", "", "PDE/FastTrack/DefectRoutingAlignment.lean", "", "PDE row 6 analytic semantics", "PDERow6FiniteOrthogonalAlignment;PDERow6FinitePressureGaugeAlignment", "Strict predecessor-query alignment derives semantic tags, nonroutability, routes, preserved reads, and exact work; continuum alignment remains unregistered"),
] + [
    Feature(
        f"ct.ct{number}",
        "CT",
        "DOMAIN_INDEPENDENT_CORE.md section 11",
        f"lean/StructuralExhaustion/CT{number}",
        f"CT{number}/Automation.lean",
        "first DAG consumer",
        "PDE cross-domain fixture",
        f"CT{number}",
        "Complete vertical slice required",
    )
    for number in range(1, 18)
] + [
    Feature(
        "routes.registry",
        "Routes",
        "HYPOSTRUCTURE_MIGRATION_GUIDE.md section 16.4",
        "lean/StructuralExhaustion/Routes",
        "Routes/Registry.lean",
        "first cross-CT EG edge",
        "first cross-row PDE edge",
        "RouteRegistry",
        "Routes consume and return full accumulated ledgers",
    )
] + [
    Feature(
        "routes.accumulated-executor",
        "Routes",
        "HYPOSTRUCTURE_MIGRATION_GUIDE.md section 16.4",
        "lean/StructuralExhaustion/Routes/Accumulated.lean",
        "Routes/Accumulated.lean",
        "first accumulated EG edge",
        "first accumulated PDE edge",
        "RouteRegistry",
        "One typed Core executor for registered generic accumulated profiles",
    )
] + [
    Feature(
        "route.ct1-to-ct2-local-deletion",
        "Routes",
        "HYPOSTRUCTURE_MIGRATION_GUIDE.md section 16.4",
        "lean/StructuralExhaustion/Routes/CT1ToCT2LocalDeletion.lean",
        "Routes/CT1ToCT2.lean",
        "EG local deletion",
        "PDE local replacement",
        "CT1ToCT2LocalDeletion",
        "Specialized semantic-discovery profile",
    )
] + [
    Feature(
        f"route.accumulated.ct{source}-to-ct{target}",
        "Routes",
        "HYPOSTRUCTURE_MIGRATION_GUIDE.md section 16.4",
        "lean/StructuralExhaustion/Routes/Accumulated.lean",
        "Routes/Registry.lean",
        "EG accumulated edge",
        "PDE accumulated edge",
        "AccumulatedRouteRegistry",
        "Registry data over one generic full-ledger executor",
    )
    for source, target in [
        (1, 9), (1, 10), (2, 1), (3, 1), (5, 2),
        (7, 5), (5, 10), (9, 1), (9, 5), (9, 10),
        (9, 14), (10, 5), (10, 6), (10, 9), (10, 14),
        (12, 10), (12, 15), (14, 1), (14, 12), (15, 9),
    ]
] + [
    Feature(
        feature_id,
        "Routes",
        "HYPOSTRUCTURE_MIGRATION_GUIDE.md section 16.4",
        legacy,
        module,
        graph_consumer,
        "",
        fixture,
        "Legacy application-owned transition to register generically",
    )
    for feature_id, legacy, module, graph_consumer, fixture in [
        ("route.required.ct12-to-ct6", "examples/erdos_64_eg/Erdos64EG/Shared/CT6SurplusPortActivation.lean", "Routes/CT12ToCT6.lean", "EG surplus-port activation", "CT12ToCT6"),
        ("route.required.ct6-to-ct15", "examples/erdos_64_eg/Erdos64EG/Shared/CT15BaselineSpineDemand.lean", "Routes/CT6ToCT15.lean", "EG baseline-spine demand", "CT6ToCT15"),
        ("route.required.ct15-to-ct15", "examples/erdos_64_eg/Erdos64EG/Shared/CT15SparsePairResponses.lean", "Routes/CT15ToCT15.lean", "EG rank refinement", "CT15ToCT15"),
        ("route.required.ct9-to-ct9-capacity-token", "examples/erdos_64_eg/Erdos64EG/Shared/CT9CapacityTokenLedger.lean", "Routes/CT9ToCT9.lean", "EG capacity-token refinement", "CT9ToCT9CapacityToken"),
        ("route.required.ct9-to-ct9-coupled-overload", "examples/erdos_64_eg/Erdos64EG/Shared/CT9CoupledClassOverload.lean", "Routes/CT9ToCT9.lean", "EG coupled-overload refinement", "CT9ToCT9CoupledOverload"),
    ]
] + [
    Feature(
        f"route.pde.ct{source}-to-ct{target}",
        "Routes",
        "HYPOSTRUCTURE_MIGRATION_GUIDE.md section 16.4",
        "PDEs/llm_auditable_proof_architecture_draft.tex",
        f"Routes/CT{source}ToCT{target}.lean",
        "",
        "PDE row chain",
        f"PDERouteCT{source}ToCT{target}",
        "Required by the PDE architecture; implement after both endpoints",
    )
    for source, target in [
        (15, 16), (15, 10), (13, 7), (3, 7), (17, 12),
        (12, 11), (10, 11), (11, 14), (14, 11), (3, 14),
        (14, 15), (15, 13), (11, 1), (14, 16), (16, 10),
        (7, 16), (16, 1), (3, 13), (13, 15), (15, 14),
    ]
]

PDE_ROWS = [
    ("1", "legal signature", "model|observable|target", ""),
    ("2", "generator/form", "represented generator|form", ""),
    ("3", "budget", "resource budget|B1-B4", ""),
    ("4", "quotient defect", "quotient|defect computation", ""),
    ("5", "directed exhaustiveness", "structural gradient|closed-range criterion|target-complete quotient audit", "CT15|CT16|Core ClassClosure"),
    ("6", "routing", "defect routing|harmonic split", "CT13|CT7"),
    ("7", "capacity", "capacity|target validation", "CT14|CT1"),
    ("8", "committor/operator", "exact response|projection error", "CT3|CT7"),
    ("9", "scale reaching", "bounded scales|peeling|deficit", "CT17|CT12|CT11"),
    ("10", "SCRC and boundary repair", "classifier|cost|capacity", "CT10|CT11|CT14|CT1"),
    ("11", "conservative carrier", "local aggregation|capacity", "CT5|CT14|CT11"),
    ("12", "elliptic constraint tail", "local inverse|tail|gauge|rank", "CT3|CT14|CT15|CT13"),
    ("13", "ledger propagation", "closed-ledger propagation", ""),
    ("14", "flux sign", "sign/gap normal form", "CT10|CT11|CT1"),
    ("15", "borderline equality", "saturation|whole support", "CT14|CT16|CT10"),
    ("16", "rigidity/separator", "response|equality support|closure", "CT7|CT16|CT1"),
    ("17", "stochastic lift", "pathwise/expectation lift", ""),
    ("17b", "conditional gauge", "conditional projection|fluctuation capacity", "CT15|CT14"),
    ("18", "target completeness", "final quotient audit|target closure", "CT16|CT1"),
]


# Complete immutable EG topology reconstructed from the eleven numbered proof
# diagrams and their continuation captions in `original_erdos_64_proof.tex`.
# Legacy Lean imports are implementation/parity observations and must never
# create, remove, or redirect an edge in this map.
ORIGINAL_EG_PREDECESSORS: dict[int, tuple[int, ...]] = {
    1: (),
    2: (1,),
    3: (2,),
    4: (2,),
    5: (4,),
    6: (5,),
    7: (6,),
    8: (6,),
    9: (8,),
    10: (9,),
    11: (10,),
    12: (11,),
    13: (12,),
    14: (13,),
    15: (14,),
    16: (15,),
    17: (15,),
    18: (17,),
    19: (18,),
    20: (19,),
    21: (19,),
    22: (21,),
    23: (22,),
    24: (22,),
    25: (24,),
    26: (25,),
    27: (26,),
    28: (27,),
    29: (28,),
    30: (29,),
    31: (30,),
    32: (31,),
    33: (32,),
    34: (32,),
    35: (33,),
    36: (35,),
    37: (36,),
    38: (36,),
    39: (38,),
    40: (38,),
    41: (40,),
    42: (41,),
    43: (41,),
    44: (43,),
    45: (44,),
    46: (45,),
    47: (34,),
    48: (47,),
    49: (48,),
    50: (49,),
    51: (50,),
    52: (51,),
    53: (50,),
    54: (52, 53),
    55: (53,),
    56: (55,),
    57: (56,),
    58: (57,),
    59: (58,),
    60: (59,),
    61: (59,),
    62: (61,),
    63: (62,),
    64: (62,),
    65: (64, 66),
    66: (108,),
    67: (65,),
    68: (67,),
    69: (68,),
    70: (68, 69),
    71: (70,),
    72: (71,),
    73: (72,),
    74: (72,),
    75: (71, 73),
    76: (74, 75),
    77: (76,),
    78: (68,),
    79: (78,),
    80: (79,),
    81: (80,),
    82: (81,),
    83: (81,),
    84: (80, 83),
    85: (82, 84),
    86: (63,),
    87: (86,),
    88: (87,),
    89: (88, 102),
    90: (89,),
    91: (90,),
    92: (91,),
    93: (89,),
    94: (93,),
    95: (93,),
    96: (95,),
    97: (95,),
    98: (97,),
    99: (97,),
    100: (99,),
    101: (94, 99),
    102: (101,),
    103: (101,),
    104: (103,),
    105: (103,),
    106: (105,),
    107: (105,),
    108: (107,),
    109: (107,),
    110: (77, 109),
    111: (110,),
    112: (111,),
    113: (112,),
    114: (113,),
    115: (114,),
    116: (115,),
    117: (115,),
    118: (117,),
    119: (117,),
    120: (119,),
    121: (120,),
    122: (121,),
    123: (118,),
    124: (123,),
    125: (20,),
    126: (125,),
    127: (126,),
    128: (127,),
    129: (128,),
    130: (129,),
    131: (130,),
    132: (130,),
    133: (132,),
    134: (132,),
    135: (134,),
    136: (135,),
    137: (131, 136),
    138: (137,),
    139: (137,),
    140: (139,),
    141: (139,),
    142: (141,),
    143: (141,),
    144: (140, 142, 143),
    145: (24,),
    146: (145,),
    147: (146,),
    148: (146,),
    149: (148,),
    150: (148,),
    151: (150,),
    152: (151,),
    153: (152,),
    154: (153,),
    155: (154,),
    156: (154,),
    157: (154,),
}

ORIGINAL_EG_NODE_IDS = range(1, 158)
SUPPLEMENTAL_LEGACY_NODE_IDS = range(158, 165)


def validate_original_eg_topology() -> None:
    expected = set(ORIGINAL_EG_NODE_IDS)
    if set(ORIGINAL_EG_PREDECESSORS) != expected:
        missing = sorted(expected - set(ORIGINAL_EG_PREDECESSORS))
        extra = sorted(set(ORIGINAL_EG_PREDECESSORS) - expected)
        raise ValueError(
            f"incomplete original EG topology: missing={missing}, extra={extra}"
        )
    for node, predecessors in ORIGINAL_EG_PREDECESSORS.items():
        if tuple(sorted(set(predecessors))) != predecessors:
            raise ValueError(f"non-canonical predecessor list for EG node {node}")
        if any(predecessor not in expected for predecessor in predecessors):
            raise ValueError(f"out-of-range predecessor for EG node {node}")


def read_existing(path: Path, key: str) -> dict[str, dict[str, str]]:
    if not path.is_file():
        return {}
    with path.open(newline="", encoding="utf-8") as stream:
        return {row[key]: row for row in csv.DictReader(stream)}


def write_rows(path: Path, fields: list[str], rows: list[dict[str, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def olean_status(source: Path, olean: Path) -> str:
    if not olean.is_file():
        return "missing"
    if olean.stat().st_mtime_ns < source.stat().st_mtime_ns:
        return "stale"
    return "fresh"


def module_source(root: Path, module: str) -> Path:
    """Resolve either a package-relative source path or a Lean module name."""
    if module.endswith(".lean"):
        relative = Path(module)
    else:
        name = module.removeprefix("Hypostructure.")
        relative = Path(*name.split(".")).with_suffix(".lean")
    return root / "hypostructure/Hypostructure" / relative


def module_status(root: Path, module: str) -> str:
    source = module_source(root, module)
    if not source.is_file():
        return "planned"
    relative = source.relative_to(root / "hypostructure/Hypostructure")
    olean = (
        root
        / "hypostructure/.lake/build/lib/lean/Hypostructure"
        / relative.with_suffix(".olean")
    )
    return "kernel_checked" if olean_status(source, olean) == "fresh" else "implemented"


def feature_status(root: Path, feature: Feature) -> str:
    return module_status(root, feature.new_module)


EG_STATUSES = (
    "inventoried",
    "scaffolded",
    "typechecked",
    "parity_checked",
    "migrated_open",
    "migrated_closed",
    "published",
    "cutover",
)


def observed_eg_status(new_source: Path, new_olean: Path) -> str:
    """Return the strongest EG state justified by local build evidence alone."""
    if not new_source.is_file():
        return "inventoried"
    if olean_status(new_source, new_olean) != "fresh":
        return "scaffolded"
    return "typechecked"


def refreshed_eg_status(
    previous: str, new_source: Path, new_olean: Path
) -> str:
    """Preserve reviewed migration states only while their kernel basis is fresh."""
    observed = observed_eg_status(new_source, new_olean)
    if observed != "typechecked":
        return observed
    if previous in EG_STATUSES[3:]:
        return previous
    return observed


def update_api(root: Path, output: Path) -> None:
    previous = read_existing(output, "feature_id")
    rows: list[dict[str, str]] = []
    generated_ids: set[str] = set()
    for feature in FEATURES:
        generated_ids.add(feature.feature_id)
        default = {
            **feature.__dict__,
            "status": feature_status(root, feature),
        }
        old = previous.get(feature.feature_id, {})
        # Preserve reviewed human fields while refreshing source-derived status.
        rows.append({
            **default,
            **old,
            "new_module": default["new_module"],
            "status": feature_status(root, feature),
        })
    # The static matrix contains reviewed features beyond the source-derived
    # bootstrap set.  Retain them verbatim and refresh only their build status.
    for feature_id, old in previous.items():
        if feature_id in generated_ids:
            continue
        module = old.get("new_module", "")
        status = module_status(root, module) if module else old.get("status", "")
        rows.append({**old, "status": status})
    write_rows(output, API_FIELDS, rows)


def update_eg(root: Path, output: Path) -> None:
    validate_original_eg_topology()
    previous = read_existing(output, "node_id")
    legacy_root = root / "examples/erdos_64_eg/Erdos64EG"
    rows: list[dict[str, str]] = []
    for number in ORIGINAL_EG_NODE_IDS:
        source = legacy_root / f"Node{number}.lean"
        text = source.read_text(encoding="utf-8") if source.is_file() else ""
        predecessors = ORIGINAL_EG_PREDECESSORS[number]
        cts = sorted({int(value) for value in CT_IMPORT.findall(text)})
        legacy_olean = (
            root
            / "examples/erdos_64_eg/.lake/build/lib/lean/Erdos64EG"
            / f"Node{number}.olean"
        )
        new_source = (
            root
            / "examples/hypostructure_erdos_64_eg/HypostructureErdos64EG"
            / f"Node{number}.lean"
        )
        new_olean = (
            root
            / "examples/hypostructure_erdos_64_eg/.lake/build/lib/lean/"
            / "HypostructureErdos64EG"
            / f"Node{number}.olean"
        )
        default = {field: "" for field in EG_FIELDS}
        observed_status = observed_eg_status(new_source, new_olean)
        default.update(
            {
                "node_id": str(number),
                "paper_ref": f"original_erdos_64_proof.tex node {number}",
                "direct_predecessors": "|".join(map(str, predecessors)),
                "legacy_files": (
                    str(source.relative_to(root)) if source.is_file() else ""
                ),
                "observed_legacy_ct_ids": "|".join(
                    f"CT{ct}" for ct in cts
                ),
                "new_file": str(new_source.relative_to(root)),
                "parity_module": (
                    "examples/hypostructure_parity/HypostructureParity/"
                    f"Node{number}.lean"
                ),
                "legacy_kernel": (
                    olean_status(source, legacy_olean)
                    if source.is_file()
                    else "missing"
                ),
                "new_kernel": (
                    olean_status(new_source, new_olean)
                    if new_source.is_file()
                    else "missing"
                ),
                "parity_status": "missing",
                "math_status": "unknown",
                "work_status": "unknown",
                "status": observed_status,
                "blocker": "not migrated",
            }
        )
        old = previous.get(str(number), {})
        refreshed = {**default, **old}
        refreshed["legacy_kernel"] = default["legacy_kernel"]
        refreshed["new_kernel"] = default["new_kernel"]
        refreshed["direct_predecessors"] = default["direct_predecessors"]
        refreshed["legacy_files"] = default["legacy_files"]
        refreshed["paper_ref"] = default["paper_ref"]
        refreshed["observed_legacy_ct_ids"] = default[
            "observed_legacy_ct_ids"
        ]
        refreshed["status"] = refreshed_eg_status(
            old.get("status", ""), new_source, new_olean
        )
        rows.append(refreshed)
    write_rows(output, EG_FIELDS, rows)


def update_supplemental_legacy(
    root: Path, output: Path, paper_matrix: Path
) -> None:
    """Record source-only legacy nodes without admitting them to the paper DAG."""
    previous = read_existing(output, "legacy_node_id")
    former_paper_rows = read_existing(paper_matrix, "node_id")
    legacy_root = root / "examples/erdos_64_eg/Erdos64EG"
    rows: list[dict[str, str]] = []

    for number in SUPPLEMENTAL_LEGACY_NODE_IDS:
        source = legacy_root / f"Node{number}.lean"
        text = source.read_text(encoding="utf-8") if source.is_file() else ""
        observed_imports = sorted(
            {int(value) for value in LEGACY_NODE_IMPORT.findall(text)}
        )
        observed_cts = sorted({int(value) for value in CT_IMPORT.findall(text)})
        legacy_olean = (
            root
            / "examples/erdos_64_eg/.lake/build/lib/lean/Erdos64EG"
            / f"Node{number}.olean"
        )
        former = former_paper_rows.get(str(number), {})
        old = previous.get(str(number), {})
        reviewed_ct_ids = (
            old.get("observed_ct_ids", "")
            or former.get("observed_legacy_ct_ids", "")
            or "|".join(f"CT{ct}" for ct in observed_cts)
        )
        default = {
            "legacy_node_id": str(number),
            "source_file": (
                str(source.relative_to(root)) if source.is_file() else ""
            ),
            "observed_imports": "|".join(map(str, observed_imports)),
            "legacy_declarations": former.get("legacy_declarations", ""),
            "normalized_input": former.get("normalized_input", ""),
            "normalized_outcomes": former.get("normalized_outcomes", ""),
            "observed_ct_ids": reviewed_ct_ids,
            "legacy_kernel": (
                olean_status(source, legacy_olean)
                if source.is_file()
                else "missing"
            ),
            "notes": (
                "Source-only legacy implementation/parity evidence; excluded "
                "from the original EG DAG, frontier, and completeness checks"
            ),
        }
        refreshed = {**default, **old}
        for field in (
            "source_file",
            "observed_imports",
            "legacy_kernel",
        ):
            refreshed[field] = default[field]
        rows.append(refreshed)

    write_rows(output, SUPPLEMENTAL_LEGACY_FIELDS, rows)


def pde_module_paths(root: Path, module: str) -> tuple[Path, Path] | None:
    if module.startswith("Hypostructure."):
        package = root / "hypostructure"
    elif module.startswith("HypostructurePDEExamples."):
        package = root / "examples/hypostructure_pde"
    else:
        return None

    relative = Path(*module.split(".")).with_suffix(".lean")
    source = package / relative
    olean = package / ".lake/build/lib/lean" / relative.with_suffix(".olean")
    return source, olean


def pde_module_is_fresh(root: Path, module: str) -> bool:
    paths = pde_module_paths(root, module)
    if paths is None:
        return False
    source, olean = paths
    return source.is_file() and olean_status(source, olean) == "fresh"


def observed_pde_statuses(root: Path, fixture_spec: str) -> tuple[str, str]:
    modules = tuple(
        item.strip() for item in fixture_spec.split(";") if item.strip()
    )
    if not modules or any(
        pde_module_paths(root, module) is None for module in modules
    ):
        return "not_checked", "not_checked"

    framework_modules = tuple(
        module for module in modules if module.startswith("Hypostructure.")
    )
    example_modules = tuple(
        module
        for module in modules
        if module.startswith("HypostructurePDEExamples.")
    )
    framework_fresh = bool(framework_modules) and all(
        pde_module_is_fresh(root, module) for module in framework_modules
    )
    kernel_status = "kernel_checked" if framework_fresh else "not_checked"
    integration_fresh = (
        framework_fresh
        and bool(example_modules)
        and all(pde_module_is_fresh(root, module) for module in example_modules)
    )
    integration_status = (
        "fixture_checked" if integration_fresh else "not_checked"
    )
    return kernel_status, integration_status


def update_pde(root: Path, output: Path) -> None:
    previous = read_existing(output, "row_id")
    rows: list[dict[str, str]] = []
    for row_id, title, capabilities, chain in PDE_ROWS:
        default = {field: "" for field in PDE_FIELDS}
        default.update(
            {
                "row_id": row_id,
                "notebook_source": f"PDEs/10_continuous_extension.ipynb#{title}",
                "required_capabilities": capabilities,
                "ct_chain": chain,
                "kernel_status": "not_checked",
                "integration_status": "not_checked",
            }
        )
        refreshed = {**default, **previous.get(row_id, {})}
        kernel_status, integration_status = observed_pde_statuses(
            root, refreshed["axiom_free_fixture"]
        )
        refreshed["kernel_status"] = kernel_status
        refreshed["integration_status"] = integration_status
        rows.append(refreshed)
    write_rows(output, PDE_FIELDS, rows)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument(
        "--only",
        choices=("all", "eg"),
        default="all",
        help="refresh every ledger or only the EG topology/evidence ledgers",
    )
    args = parser.parse_args()
    root = args.root.resolve()
    validate_eg_source_authority(root)
    output = root / "migration/hypostructure"
    if args.only == "all":
        update_api(root, output / "api-feature-matrix.csv")
    paper_matrix = output / "eg-node-matrix.csv"
    update_supplemental_legacy(
        root, output / "supplemental-legacy-evidence.csv", paper_matrix
    )
    update_eg(root, paper_matrix)
    if args.only == "all":
        update_pde(root, output / "pde-row-matrix.csv")
    print(f"Updated Hypostructure migration records under {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
