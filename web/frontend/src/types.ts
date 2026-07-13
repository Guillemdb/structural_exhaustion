export type VerificationState = "verified" | "stale" | "failed";

export interface VerificationDisplay {
  state: VerificationState;
  message: string;
}

export interface VerificationView {
  state: VerificationState;
  reportedStatus: string;
  catalogHash: string;
  verificationCatalogHash: string;
  message: string;
  toolchain: Record<string, unknown>;
  aggregate: Record<string, string>;
}

export interface CatalogView {
  schemaVersion: string;
  catalogHash: string;
  sourceOfTruth: Record<string, unknown>;
}

export interface FrameworkTotals {
  tactics: number;
  nodes: number;
  transitions: number;
  terminals: number;
  residualKinds: number;
  routes: number;
  manualObligations: number;
}

export interface TacticSummary {
  tacticId: string;
  title: string;
  apiVersion: string;
  namespace: string;
  nodeCount: number;
  transitionCount: number;
  terminalCount: number;
  residualCount: number;
  manualObligationCount: number;
}

export interface ProvisionedRef {
  ref: string;
  provision: string;
}

export interface CapabilityRequirement extends ProvisionedRef {
  conceptId: string;
}

export interface CapabilityConcept {
  conceptId: string;
  requirementRef: string;
  formalDeclaration: {
    name: string;
    kind: string;
    type: string;
  };
  presentation: {
    label: string;
    mathematicalDefinition: string;
    plainExplanation: string;
  };
}

export interface FormalEdge {
  edgeId: string;
  constructor: string;
  constructorType: string;
  sourceNode: string;
  targetNode: string;
}

export interface AutomationContract {
  executionClass: string;
  authorInputs: ProvisionedRef[];
  inferredInputs: ProvisionedRef[];
  predecessorInputs: ProvisionedRef[];
  derivedInputs: ProvisionedRef[];
  frameworkTheorems: ProvisionedRef[];
  transitiveDependencies: ProvisionedRef[];
  generatedOutputs: ProvisionedRef[];
  manualObligations: string[];
}

export interface NodeRecord {
  ordinal: number;
  nodeId: string;
  semanticId: string;
  nodeKind: string;
  constructor: string;
  sourceFile: string;
  presentation: {
    label: string;
    summary: string;
  };
  formalContract: {
    predecessorIndexed: boolean;
    incomingEdges: FormalEdge[];
    outgoingEdges: FormalEdge[];
  };
  automation: AutomationContract;
}

export interface TransitionRecord extends FormalEdge {
  ordinal: number;
  provision: string;
}

export interface TerminalRecord {
  ordinal: number;
  case: string;
  nodeId: string;
  constructor: string;
}

export interface ResidualField {
  fieldName: string;
  leanType: string;
  provision: string;
}

export interface ResidualKind {
  residualKindId: string;
  leanType: string;
  inheritedContext: string;
  semanticFields: ResidualField[];
}

export interface CapabilityRecord {
  tacticId: string;
  capabilityId: string;
  requiredDefinitions: CapabilityRequirement[];
  requiredInstances: ProvisionedRef[];
  derivedOperations: ProvisionedRef[];
}

export interface TacticRecord {
  tacticId: string;
  title: string;
  apiVersion: string;
  namespace: string;
  capability: CapabilityRecord;
  capabilityProfiles: CapabilityRecord[];
  capabilityConcepts: CapabilityConcept[];
  nodes: NodeRecord[];
  transitions: TransitionRecord[];
  terminals: TerminalRecord[];
  residualKinds: ResidualKind[];
  apiDeclarations: Array<{
    name: string;
    kind: string;
    type: string;
  }>;
  loopDecrease: unknown;
}

export interface RouteRecord {
  routeId: string;
  sourceTacticId: string;
  sourceResidualKind: string;
  targetTacticId: string;
  selectionClass: string;
  discovery: string;
  triggerConstructor: string;
  soundnessTheorem: string;
  contextPreservationTheorem: string;
  provenanceTheorem: string;
  authoringBoundary: {
    semanticDiscovery: {
      kind: string;
      adapterType: string | null;
    };
    problemSpecificInputs: string[];
    frameworkOwnedResponsibilities: string[];
  };
}

export interface FrameworkResponse {
  artifactType: "frameworkExplorer";
  catalog: CatalogView;
  verification: VerificationView;
  totals: FrameworkTotals;
  tactics: TacticSummary[];
  routes: RouteRecord[];
}

export interface GraphElementData {
  id: string;
  label?: string;
  kind?: string;
  source?: string;
  target?: string;
  [key: string]: unknown;
}

export interface GraphElement {
  data: GraphElementData;
}

export interface TacticResponse {
  artifactType: "frameworkExplorerTactic";
  catalogHash: string;
  verification: VerificationView;
  tactic: TacticRecord;
  graph: {
    tacticId: string;
    elements: GraphElement[];
  };
  inboundRoutes: RouteRecord[];
  outboundRoutes: RouteRecord[];
}

export interface SelectedGraphElement {
  id: string;
  group: "node" | "edge";
  data: GraphElementData;
}

export type ExampleProofStatus = "complete" | "partial";

export type ExampleStageKind =
  | "problem"
  | "tactic"
  | "adapter"
  | "certificate"
  | "theorem"
  | "fixture";

export type ExampleLinkKind =
  | "registeredRoute"
  | "frameworkComposition"
  | "proofData"
  | "validation"
  | "scheduleAudit"
  | "sharedProblem";

export interface ExampleWorkflowSummary {
  workflowId: string;
  title: string;
  purpose: string;
  completion: ExampleProofStatus;
}

export interface ExampleSummary {
  exampleId: string;
  title: string;
  summary: string;
  proofStatus: ExampleProofStatus;
  tacticIds: string[];
  workflowCount: number;
  workflows: ExampleWorkflowSummary[];
}

export interface ExampleVerificationView extends VerificationDisplay {
  reportedStatus: string;
  exampleCatalogHash: string;
  verificationExampleCatalogHash: string;
}

export interface ExamplesResponse {
  artifactType: "frameworkExplorerExamples";
  catalog: CatalogView;
  verification: ExampleVerificationView;
  examples: ExampleSummary[];
}

export interface ExampleStage {
  stageId: string;
  title: string;
  kind: ExampleStageKind;
  summary: string;
  tacticId?: string | null;
  primaryDeclarationId: string;
  evidenceDeclarationIds: string[];
}

export interface ExampleLink {
  linkId: string;
  sourceStageId: string;
  targetStageId: string;
  kind: ExampleLinkKind;
  label: string;
  summary: string;
  routeId?: string | null;
  evidenceDeclarationIds: string[];
}

export interface ExampleWorkflow extends ExampleWorkflowSummary {
  summary: string;
  purpose: string;
  stages: ExampleStage[];
  links: ExampleLink[];
}

export interface ExampleInterfaceBinding {
  bindingId: string;
  workflowId: string;
  stageId: string;
  tacticId: string;
  role: string;
  summary: string;
  problemDeclarationId: string;
  frameworkDeclarationId: string;
}

export type ExampleCorrespondenceKind =
  | "exact"
  | "equivalentEncoding"
  | "specialization"
  | "composite"
  | "support"
  | "partial";

export type ExampleImplementationStatus = "implemented" | "next" | "notStarted";

export type ExampleDeclarationRole =
  | "mathematicalDefinition"
  | "semanticTheorem"
  | "encodingBridge"
  | "tacticExecution"
  | "executionAudit"
  | "soundnessTotality"
  | "workBound"
  | "compositionProvenance"
  | "frameworkInterface"
  | "externalTheorem"
  | "fixture";

export interface ExampleManuscriptReference {
  label: string;
  title: string;
  nodeIds: number[];
}

export interface ExampleDeclarationGroup {
  groupId: string;
  title: string;
  role: ExampleDeclarationRole;
  explanation: string;
  declarationIds: string[];
}

export interface ExampleProofStep {
  stepId: string;
  stageId?: string;
  title: string;
  plainExplanation: string;
  formalStatement: string;
  status: ExampleImplementationStatus;
  correspondence: ExampleCorrespondenceKind;
  manuscriptRefs: ExampleManuscriptReference[];
  declarationGroups: ExampleDeclarationGroup[];
  scopeNotes: string;
  workBound: string;
}

export interface ExampleManuscript {
  title: string;
  path: string;
  proofSteps: ExampleProofStep[];
  coverage: {
    implementedSteps: number;
    totalSteps: number;
    explainedDeclarations: number;
    displayedDeclarations: number;
  };
}

export interface ExampleDeclaration {
  declarationId: string;
  name: string;
  kind: string;
  type: string;
  sourceId: string;
  startLine: number;
  startColumn: number;
  endLine: number;
  endColumn: number;
  selectionStartLine: number;
  selectionStartColumn: number;
  selectionEndLine: number;
  selectionEndColumn: number;
}

export interface ExampleSource {
  sourceId: string;
  moduleName: string;
  path: string;
  sha256: string;
  content: string;
}

export interface ExampleDetail {
  artifactType: "structuralExhaustionExample";
  schemaVersion: "1.1.0";
  sourceOfTruth: {
    kind: "compiledLeanEnvironment";
    rootModule: string;
    descriptor: string;
  };
  exampleId: string;
  title: string;
  summary: string;
  proofStatus: ExampleProofStatus;
  tacticIds: string[];
  workflows: ExampleWorkflow[];
  interfaceBindings: ExampleInterfaceBinding[];
  manuscript: ExampleManuscript | null;
  declarations: ExampleDeclaration[];
  sources: ExampleSource[];
}

export interface ExampleResponse {
  artifactType: "frameworkExplorerExample";
  catalogHash: string;
  frameworkCatalogHash: string;
  verification: ExampleVerificationView;
  example: ExampleDetail;
  tactics: TacticSummary[];
}
