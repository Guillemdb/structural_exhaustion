"""Public API response models for the framework explorer."""

from __future__ import annotations

from typing import Any, Literal

from pydantic import BaseModel, ConfigDict


class ApiModel(BaseModel):
    model_config = ConfigDict(extra="forbid")


class ArtifactWarningView(ApiModel):
    code: Literal["staleHash"]
    message: str


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
    implementedTransitions: int
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


class ImplementedTransitionRecord(ApiModel):
    transitionId: str
    sourceTacticId: str
    targetTacticId: str
    relationshipKind: Literal[
        "registeredRoute",
        "frameworkComposition",
        "proofData",
        "validation",
        "scheduleAudit",
        "sharedProblem",
    ]
    automationClass: Literal[
        "registeredRoute", "frameworkExecutor", "frameworkAudit"
    ]
    frameworkAutomated: Literal[True]
    automationDeclarationIds: list[str]
    label: str
    summary: str
    exampleId: str
    exampleTitle: str
    workflowId: str
    workflowTitle: str
    workflowCompletion: Literal["complete", "partial"]
    linkId: str
    sourceStageId: str
    sourceStageTitle: str
    sourceDeclarationId: str
    targetStageId: str
    targetStageTitle: str
    targetDeclarationId: str
    routeId: str | None = None
    evidenceDeclarationIds: list[str]


class HealthResponse(ApiModel):
    status: Literal["ok"]
    artifactType: Literal["frameworkExplorerHealth"]
    artifactWarnings: list[ArtifactWarningView]
    catalog: CatalogView
    verification: VerificationView
    tacticCount: int
    exampleCount: int


class FrameworkResponse(ApiModel):
    artifactType: Literal["frameworkExplorer"]
    artifactWarnings: list[ArtifactWarningView]
    catalog: CatalogView
    verification: VerificationView
    exampleCatalog: ExampleCatalogView
    exampleVerification: ExampleVerificationView
    totals: FrameworkTotals
    tactics: list[TacticSummary]
    routes: list[dict[str, Any]]
    implementedTransitions: list[ImplementedTransitionRecord]


class TacticResponse(ApiModel):
    artifactType: Literal["frameworkExplorerTactic"]
    artifactWarnings: list[ArtifactWarningView]
    catalogHash: str
    verification: VerificationView
    tactic: dict[str, Any]
    graph: dict[str, Any]
    inboundRoutes: list[dict[str, Any]]
    outboundRoutes: list[dict[str, Any]]


class InternalReference(ApiModel):
    ref: str
    provision: str


class InternalStep(ApiModel):
    stepId: str
    role: Literal[
        "authorObject",
        "inferredInstance",
        "predecessorState",
        "operation",
        "theorem",
        "output",
    ]
    reference: InternalReference
    plainExplanation: str
    mathematicalDefinition: str | None
    label: str
    declarationId: str | None


class InternalEdge(ApiModel):
    edgeId: str
    sourceStepId: str
    targetStepId: str
    relation: Literal["consumes", "then", "produces", "certifies"]


class InternalFlow(ApiModel):
    nodeId: str
    steps: list[InternalStep]
    edges: list[InternalEdge]


class NodeInternalRecord(ApiModel):
    nodeId: str
    internalFlow: InternalFlow


class SourcePosition(ApiModel):
    line: int
    column: int


class SourceRange(ApiModel):
    start: SourcePosition
    end: SourcePosition


class InternalDeclaration(ApiModel):
    declarationId: str
    name: str
    kind: Literal[
        "axiom",
        "definition",
        "theorem",
        "opaque",
        "quotient",
        "inductive",
        "constructor",
        "recursor",
    ]
    type: str
    docString: str | None
    module: str | None
    sourceFile: str | None
    range: SourceRange | None
    selectionRange: SourceRange | None
    bodyAvailable: bool
    typeDependencies: list[str]
    bodyDependencies: list[str]
    projectLocal: bool
    sourceId: str | None


class InternalSource(ApiModel):
    sourceId: str
    moduleName: str | None
    path: str
    sha256: str
    content: str


class TacticInternals(ApiModel):
    artifactType: Literal["structuralExhaustionNodeInternals"]
    schemaVersion: Literal["1.0.0"]
    tacticId: str
    apiVersion: str
    nodes: list[NodeInternalRecord]
    declarations: list[InternalDeclaration]
    sources: list[InternalSource]


class TacticInternalsResponse(ApiModel):
    artifactType: Literal["frameworkExplorerTacticInternals"]
    artifactWarnings: list[ArtifactWarningView]
    catalogHash: str
    verification: VerificationView
    internals: TacticInternals


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
    artifactWarnings: list[ArtifactWarningView]
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
    automationDeclarationIds: list[str]
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


class ExampleManuscriptInlineRecord(ApiModel):
    kind: Literal[
        "text",
        "code",
        "space",
        "softBreak",
        "lineBreak",
        "math",
        "emphasis",
        "strong",
        "underline",
        "strikeout",
        "smallCaps",
        "upright",
        "reference",
        "citation",
    ]
    text: str | None = None
    display: bool | None = None
    tex: str | None = None
    children: list["ExampleManuscriptInlineRecord"] | None = None
    labels: list[str] | None = None
    referenceKind: str | None = None
    prefix: str | None = None
    keys: list[str] | None = None


class ExampleManuscriptBlockRecord(ApiModel):
    kind: Literal[
        "paragraph",
        "heading",
        "environment",
        "orderedList",
        "bulletList",
        "blockQuote",
        "codeBlock",
        "figure",
    ]
    inlines: list[ExampleManuscriptInlineRecord] | None = None
    level: int | None = None
    label: str | None = None
    environment: str | None = None
    title: list[ExampleManuscriptInlineRecord] | None = None
    blocks: list["ExampleManuscriptBlockRecord"] | None = None
    start: int | None = None
    items: list[list["ExampleManuscriptBlockRecord"]] | None = None
    text: str | None = None
    svg: str | None = None
    svgSha256: str | None = None
    caption: list["ExampleManuscriptBlockRecord"] | None = None


class ExampleManuscriptFragmentRecord(ApiModel):
    label: str
    environment: str
    sourceLine: int
    includesProof: bool
    contentSha256: str
    blocks: list[ExampleManuscriptBlockRecord]


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
    verifiedMathematicalObjects: int
    totalMathematicalObjects: int
    verifiedDiagramNodes: int
    totalDiagramNodes: int
    verifiedWorkflowSteps: int


class ExampleManuscriptRecord(ApiModel):
    title: str
    path: str
    sha256: str
    fragments: list[ExampleManuscriptFragmentRecord]
    formalizedNodeIds: list[int]
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
    schemaVersion: Literal["1.4.0"]
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
    artifactWarnings: list[ArtifactWarningView]
    catalogHash: str
    frameworkCatalogHash: str
    verification: ExampleVerificationView
    example: ExampleDetail
    tactics: list[TacticSummary]
