"""Public API response models for the framework explorer."""

from __future__ import annotations

from typing import Any, Literal

from pydantic import BaseModel, ConfigDict


class ApiModel(BaseModel):
    model_config = ConfigDict(extra="forbid")


class VerificationView(ApiModel):
    state: Literal["verified", "stale", "failed"]
    reportedStatus: str
    catalogHash: str
    verificationCatalogHash: str
    message: str
    toolchain: dict[str, Any]
    aggregate: dict[str, str]


class CatalogView(ApiModel):
    schemaVersion: str
    catalogHash: str
    sourceOfTruth: dict[str, Any]


class ExampleCatalogView(ApiModel):
    schemaVersion: str
    catalogHash: str
    sourceOfTruth: dict[str, Any]


class ExampleVerificationView(ApiModel):
    state: Literal["verified", "stale", "failed"]
    reportedStatus: str
    exampleCatalogHash: str
    verificationExampleCatalogHash: str
    message: str


class FrameworkTotals(ApiModel):
    tactics: int
    nodes: int
    transitions: int
    terminals: int
    residualKinds: int
    routes: int
    manualObligations: int


class TacticSummary(ApiModel):
    tacticId: str
    title: str
    apiVersion: str
    namespace: str
    nodeCount: int
    transitionCount: int
    terminalCount: int
    residualCount: int
    manualObligationCount: int


class HealthResponse(ApiModel):
    status: Literal["ok"]
    artifactType: Literal["frameworkExplorerHealth"]
    catalog: CatalogView
    verification: VerificationView
    tacticCount: int
    exampleCount: int


class FrameworkResponse(ApiModel):
    artifactType: Literal["frameworkExplorer"]
    catalog: CatalogView
    verification: VerificationView
    totals: FrameworkTotals
    tactics: list[TacticSummary]
    routes: list[dict[str, Any]]


class TacticResponse(ApiModel):
    artifactType: Literal["frameworkExplorerTactic"]
    catalogHash: str
    verification: VerificationView
    tactic: dict[str, Any]
    graph: dict[str, Any]
    inboundRoutes: list[dict[str, Any]]
    outboundRoutes: list[dict[str, Any]]


class ExampleWorkflowSummary(ApiModel):
    workflowId: str
    title: str
    purpose: str
    completion: str


class ExampleSummary(ApiModel):
    exampleId: str
    title: str
    summary: str
    proofStatus: Literal["complete", "partial"]
    tacticIds: list[str]
    workflowCount: int
    workflows: list[ExampleWorkflowSummary]


class ExamplesResponse(ApiModel):
    artifactType: Literal["frameworkExplorerExamples"]
    catalog: ExampleCatalogView
    verification: ExampleVerificationView
    examples: list[ExampleSummary]


class ExampleSourceOfTruth(ApiModel):
    kind: Literal["compiledLeanEnvironment"]
    rootModule: str
    descriptor: str


class ExampleStageRecord(ApiModel):
    stageId: str
    title: str
    summary: str
    kind: Literal["problem", "tactic", "adapter", "certificate", "theorem", "fixture"]
    tacticId: str | None = None
    primaryDeclarationId: str
    evidenceDeclarationIds: list[str]


class ExampleLinkRecord(ApiModel):
    linkId: str
    sourceStageId: str
    targetStageId: str
    kind: Literal[
        "registeredRoute",
        "frameworkComposition",
        "proofData",
        "validation",
        "scheduleAudit",
        "sharedProblem",
    ]
    label: str
    summary: str
    routeId: str | None = None
    evidenceDeclarationIds: list[str]


class ExampleWorkflowRecord(ApiModel):
    workflowId: str
    title: str
    summary: str
    purpose: str
    completion: Literal["complete", "partial"]
    stages: list[ExampleStageRecord]
    links: list[ExampleLinkRecord]


class ExampleInterfaceBindingRecord(ApiModel):
    bindingId: str
    workflowId: str
    stageId: str
    tacticId: str
    role: str
    summary: str
    problemDeclarationId: str
    frameworkDeclarationId: str


class ExampleManuscriptReferenceRecord(ApiModel):
    label: str
    title: str
    nodeIds: list[int]


class ExampleDeclarationGroupRecord(ApiModel):
    groupId: str
    title: str
    role: Literal[
        "mathematicalDefinition",
        "semanticTheorem",
        "encodingBridge",
        "tacticExecution",
        "executionAudit",
        "soundnessTotality",
        "workBound",
        "compositionProvenance",
        "frameworkInterface",
        "externalTheorem",
        "fixture",
    ]
    explanation: str
    declarationIds: list[str]


class ExampleProofStepRecord(ApiModel):
    stepId: str
    stageId: str | None = None
    title: str
    plainExplanation: str
    formalStatement: str
    status: Literal["implemented", "next", "notStarted"]
    correspondence: Literal[
        "exact", "equivalentEncoding", "specialization", "composite", "support", "partial"
    ]
    manuscriptRefs: list[ExampleManuscriptReferenceRecord]
    declarationGroups: list[ExampleDeclarationGroupRecord]
    scopeNotes: str
    workBound: str


class ExampleManuscriptCoverageRecord(ApiModel):
    implementedSteps: int
    totalSteps: int
    explainedDeclarations: int
    displayedDeclarations: int


class ExampleManuscriptRecord(ApiModel):
    title: str
    path: str
    proofSteps: list[ExampleProofStepRecord]
    coverage: ExampleManuscriptCoverageRecord


class ExampleDeclarationRecord(ApiModel):
    declarationId: str
    name: str
    kind: str
    type: str
    sourceId: str
    startLine: int
    startColumn: int
    endLine: int
    endColumn: int
    selectionStartLine: int
    selectionStartColumn: int
    selectionEndLine: int
    selectionEndColumn: int


class ExampleSourceRecord(ApiModel):
    sourceId: str
    moduleName: str
    path: str
    sha256: str
    content: str


class ExampleDetail(ApiModel):
    artifactType: Literal["structuralExhaustionExample"]
    schemaVersion: Literal["1.1.0"]
    sourceOfTruth: ExampleSourceOfTruth
    exampleId: str
    title: str
    summary: str
    proofStatus: Literal["complete", "partial"]
    tacticIds: list[str]
    workflows: list[ExampleWorkflowRecord]
    interfaceBindings: list[ExampleInterfaceBindingRecord]
    manuscript: ExampleManuscriptRecord | None
    declarations: list[ExampleDeclarationRecord]
    sources: list[ExampleSourceRecord]


class ExampleResponse(ApiModel):
    artifactType: Literal["frameworkExplorerExample"]
    catalogHash: str
    frameworkCatalogHash: str
    verification: ExampleVerificationView
    example: ExampleDetail
    tactics: list[TacticSummary]
