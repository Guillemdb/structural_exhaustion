import type {
  ExampleDetail,
  ExampleInterfaceBinding,
  ExampleManuscriptReference,
  ExampleProofStep,
  ExampleResponse,
} from "./types";

/**
 * Evidence ownership is derived from the declaration namespace, not from the
 * prose attached to a proof step.  In particular, declarations below an
 * `External` namespace remain visible as a separate trust boundary even when
 * the declaration is re-exported by a framework module.
 */
export type ErdosDeclarationOwnership = "author" | "framework" | "external";

export interface ErdosDeclarationEvidence {
  authorOwnedDeclarationIds: readonly string[];
  frameworkOwnedDeclarationIds: readonly string[];
  externalDeclarationIds: readonly string[];
}

export interface ErdosWorkBoundEvidence {
  stepId: string;
  description: string;
}

export interface ErdosFrameworkLeverageCounts {
  authorOwnedDeclarations: number;
  frameworkOwnedDeclarations: number;
  externalDeclarations: number;
  ctCapabilities: number;
  registeredTransitions: number;
  automationDeclarations: number;
  interfaceBindings: number;
  proofSteps: number;
  workBounds: number;
  workflows: number;
  stages: number;
  links: number;
  linksWithAutomation: number;
}

/**
 * Raw, auditable reuse evidence.  These values deliberately do not estimate
 * elapsed time or a hypothetical manual implementation.
 */
export interface ErdosFrameworkLeverageSummary extends ErdosDeclarationEvidence {
  counts: ErdosFrameworkLeverageCounts;
  ctIds: readonly string[];
  transitionProfileIds: readonly string[];
  automationDeclarationIds: readonly string[];
  interfaceBindingIds: readonly string[];
  proofStepIds: readonly string[];
  workBounds: readonly ErdosWorkBoundEvidence[];
}

export interface ErdosNodeCausalEvidence extends ErdosDeclarationEvidence {
  nodeId: number;
  paperReferences: readonly ExampleManuscriptReference[];
  proofSteps: readonly ExampleProofStep[];
  proofStepIds: readonly string[];
  stageIds: readonly string[];
  incomingLinkIds: readonly string[];
  ctIds: readonly string[];
  transitionProfileIds: readonly string[];
  automationDeclarationIds: readonly string[];
  bindings: readonly ExampleInterfaceBinding[];
  workBounds: readonly ErdosWorkBoundEvidence[];
}

export interface ErdosProofHistorySnapshot {
  snapshotVersion: "1.0.0";
  exampleId: string;
  recordedAt: string | null;
  catalogHash: string | null;
  frameworkCatalogHash: string | null;
  manuscriptSha256: string | null;
  sourceDescriptor: string;
  proofStatus: ExampleDetail["proofStatus"];
  greenNodeIds: readonly number[];
  yellowNodeIds: readonly number[];
  nextNodeIds: readonly number[];
  provedObligations: number;
  remainingObligations: number;
  coverage: {
    implementedSteps: number;
    totalSteps: number;
    verifiedDiagramNodes: number;
    totalDiagramNodes: number;
    verifiedWorkflowSteps: number;
  };
  leverage: ErdosFrameworkLeverageCounts;
}

export interface ErdosGuidedTourStop {
  nodeIds: readonly number[];
  title: string;
  paperQuestion: string;
  frameworkContribution: string;
  evidenceFocus: string;
}

export interface ErdosGuidedTour {
  tourId: string;
  title: string;
  summary: string;
  nodeIds: readonly number[];
  stops: readonly ErdosGuidedTourStop[];
}

export const ERDOS_FRAMEWORK_GUIDED_TOURS: readonly ErdosGuidedTour[] = [
  {
    tourId: "induced-path-to-label-algebra",
    title: "From an induced path to an exact label algebra",
    summary:
      "Follow three reusable finite procedures from the induced-P13 dichotomy through a maximum packing to the exact attachment-label table.",
    nodeIds: [15, 16, 17, 18],
    stops: [
      {
        nodeIds: [15, 16],
        title: "Force an induced P13",
        paperQuestion: "Why must a minimal target-avoiding graph contain the required induced path?",
        frameworkContribution:
          "CT1 packages the hit/avoiding split, its execution audit, and a proof-carrying induced-path realization while keeping the external HSS theorem explicit.",
        evidenceFocus:
          "Compare the application bridge with the CT1 and graph-owned declarations, then inspect the isolated external declaration.",
      },
      {
        nodeIds: [17],
        title: "Select a maximum disjoint packing",
        paperQuestion: "How is the induced path turned into a remainder with an exact cardinality identity?",
        frameworkContribution:
          "The registered CT1-to-CT12 transition profile supplies the typed handoff, and CT12 records the selected packing and remainder without materializing the universe of packings.",
        evidenceFocus:
          "Inspect the registered transition profile, CT12 binding, exact predecessor, and declared iteration bound.",
      },
      {
        nodeIds: [18],
        title: "Classify every legal attachment label",
        paperQuestion: "Which of the 8192 path-position codes are legal, and what relations do they induce?",
        frameworkContribution:
          "CT10 performs the exhaustive finite classification and exposes the trace, semantics, totality, and explicit primitive-check ledger.",
        evidenceFocus:
          "Inspect the problem-specific legality predicate beside the reusable exhaustive classifier and its exact work bound.",
      },
    ],
  },
  {
    tourId: "curvature-rank-without-global-enumeration",
    title: "Curvature rank without global enumeration",
    summary:
      "See how CT15 turns one finite response profile into an attained target rank, an exhaustive decision, and proof-carrying residuals without enumerating powersets or context families.",
    nodeIds: [31, 32, 33, 34],
    stops: [
      {
        nodeIds: [31],
        title: "Define an attained target rank",
        paperQuestion: "What is the largest raw-wedge family surviving every functional admissible quotient?",
        frameworkContribution:
          "CT15 supplies the survival predicate, target-rank maximum, upper bound, and an attained maximal family over the graph-specific wedge response profile.",
        evidenceFocus:
          "Separate the authored wedge coordinates and response semantics from the reusable CT15 rank machinery.",
      },
      {
        nodeIds: [32],
        title: "Make the rank split exhaustive",
        paperQuestion: "Is there strict rank loss, or does the rank equal the complete wedge count?",
        frameworkContribution:
          "CT15 derives the exact two-edge decision from the previous bound with no additional executable scan.",
        evidenceFocus:
          "Inspect the incoming automation declaration and the two proof-carrying branch constructors.",
      },
      {
        nodeIds: [33],
        title: "Extract a finite dependence circuit",
        paperQuestion: "What concrete witness does the strict-rank-loss edge carry into Branch D?",
        frameworkContribution:
          "CT15 proof-selects a quotient and two distinct coordinates with the same response, packaging them as a singleton-basis pair circuit.",
        evidenceFocus:
          "Inspect the exact predecessor, retained quotient, pair circuit, and zero-search work statement.",
      },
      {
        nodeIds: [34],
        title: "Retain the exact full-rank residual",
        paperQuestion: "What survives on the no-rank-loss edge?",
        frameworkContribution:
          "CT15 reuses its attained-maximum theorem to retain a surviving family of the complete declared size, stronger than the paper's asymptotic residual.",
        evidenceFocus:
          "Inspect the equality branch, attained family, and absence of any new finite scan.",
      },
    ],
  },
] as const;

type ErdosExampleData = ExampleResponse | ExampleDetail;

function detailOf(data: ErdosExampleData): ExampleDetail {
  return "example" in data ? data.example : data;
}

function responseOf(data: ErdosExampleData): ExampleResponse | null {
  return "example" in data ? data : null;
}

function sortedUnique(values: Iterable<string>): string[] {
  return [...new Set([...values].filter((value) => value.length > 0))].sort((left, right) =>
    left.localeCompare(right, undefined, { numeric: true }));
}

function sortedUniqueNumbers(values: Iterable<number>): number[] {
  return [...new Set(values)].sort((left, right) => left - right);
}

function uniqueBy<T>(values: Iterable<T>, keyOf: (value: T) => string): T[] {
  const result: T[] = [];
  const seen = new Set<string>();
  for (const value of values) {
    const key = keyOf(value);
    if (seen.has(key)) continue;
    seen.add(key);
    result.push(value);
  }
  return result;
}

export function classifyErdosDeclarationOwnership(
  declarationId: string,
): ErdosDeclarationOwnership {
  const namespaceSegments = declarationId.split(".");
  if (namespaceSegments.includes("External")) return "external";
  if (declarationId === "Erdos64EG" || declarationId.startsWith("Erdos64EG.")) {
    return "author";
  }
  if (
    declarationId === "StructuralExhaustion"
    || declarationId.startsWith("StructuralExhaustion.")
  ) {
    return "framework";
  }
  return "external";
}

function partitionDeclarations(declarationIds: Iterable<string>): ErdosDeclarationEvidence {
  const buckets: Record<ErdosDeclarationOwnership, string[]> = {
    author: [],
    framework: [],
    external: [],
  };
  for (const declarationId of sortedUnique(declarationIds)) {
    buckets[classifyErdosDeclarationOwnership(declarationId)].push(declarationId);
  }
  return {
    authorOwnedDeclarationIds: buckets.author,
    frameworkOwnedDeclarationIds: buckets.framework,
    externalDeclarationIds: buckets.external,
  };
}

function ctIdsFrom(values: Iterable<string>): string[] {
  const result: string[] = [];
  for (const value of values) {
    for (const match of value.matchAll(/(?:^|\b)(CT\d+)(?=\b|\.)/g)) {
      result.push(match[1]);
    }
  }
  return sortedUnique(result);
}

function workBoundsFor(proofSteps: readonly ExampleProofStep[]): ErdosWorkBoundEvidence[] {
  return uniqueBy(
    proofSteps
      .filter((step) => step.workBound.trim().length > 0)
      .map((step) => ({ stepId: step.stepId, description: step.workBound.trim() })),
    ({ stepId }) => stepId,
  );
}

export function deriveErdosFrameworkLeverage(
  data: ErdosExampleData,
): ErdosFrameworkLeverageSummary {
  const detail = detailOf(data);
  const manuscript = detail.manuscript;
  const stages = detail.workflows.flatMap((workflow) => workflow.stages);
  const links = detail.workflows.flatMap((workflow) => workflow.links);
  const proofSteps = manuscript?.proofSteps ?? [];
  const ownership = partitionDeclarations(
    detail.declarations.map((declaration) => declaration.declarationId),
  );
  const transitionProfileIds = sortedUnique(
    links.flatMap((link) =>
      link.transitionProfileId ? [link.transitionProfileId] : []),
  );
  const automationDeclarationIds = sortedUnique(
    links.flatMap((link) => link.automationDeclarationIds),
  );
  const explicitCtIds = [
    ...detail.tacticIds,
    ...stages.flatMap((stage) => stage.tacticId ? [stage.tacticId] : []),
    ...detail.interfaceBindings.map((binding) => binding.tacticId),
  ];
  const ctIds = ctIdsFrom([
    ...explicitCtIds,
    ...transitionProfileIds,
    ...ownership.frameworkOwnedDeclarationIds,
  ]);
  const workBounds = workBoundsFor(proofSteps);
  const counts: ErdosFrameworkLeverageCounts = {
    authorOwnedDeclarations: ownership.authorOwnedDeclarationIds.length,
    frameworkOwnedDeclarations: ownership.frameworkOwnedDeclarationIds.length,
    externalDeclarations: ownership.externalDeclarationIds.length,
    ctCapabilities: ctIds.length,
    registeredTransitions: transitionProfileIds.length,
    automationDeclarations: automationDeclarationIds.length,
    interfaceBindings: new Set(detail.interfaceBindings.map((binding) => binding.bindingId)).size,
    proofSteps: new Set(proofSteps.map((step) => step.stepId)).size,
    workBounds: workBounds.length,
    workflows: new Set(detail.workflows.map((workflow) => workflow.workflowId)).size,
    stages: new Set(stages.map((stage) => stage.stageId)).size,
    links: new Set(links.map((link) => link.linkId)).size,
    linksWithAutomation: new Set(
      links
        .filter((link) => link.automationDeclarationIds.length > 0)
        .map((link) => link.linkId),
    ).size,
  };

  return {
    ...ownership,
    counts,
    ctIds,
    transitionProfileIds,
    automationDeclarationIds,
    interfaceBindingIds: sortedUnique(
      detail.interfaceBindings.map((binding) => binding.bindingId),
    ),
    proofStepIds: sortedUnique(proofSteps.map((step) => step.stepId)),
    workBounds,
  };
}

export function deriveErdosNodeCausalEvidence(
  data: ErdosExampleData,
  nodeId: number,
): ErdosNodeCausalEvidence {
  const detail = detailOf(data);
  const proofSteps = uniqueBy(
    (detail.manuscript?.proofSteps ?? []).filter((step) =>
      step.manuscriptRefs.some((reference) => reference.nodeIds.includes(nodeId))),
    (step) => step.stepId,
  );
  const stageIds = sortedUnique(
    proofSteps.flatMap((step) => step.stageId ? [step.stageId] : []),
  );
  const relevantStageIds = new Set(stageIds);
  const stages = detail.workflows.flatMap((workflow) => workflow.stages)
    .filter((stage) => relevantStageIds.has(stage.stageId));
  const incomingLinks = detail.workflows.flatMap((workflow) => workflow.links)
    .filter((link) => relevantStageIds.has(link.targetStageId));
  const bindings = uniqueBy(
    detail.interfaceBindings.filter((binding) => relevantStageIds.has(binding.stageId)),
    (binding) => binding.bindingId,
  );
  const paperReferences = uniqueBy(
    proofSteps.flatMap((step) => step.manuscriptRefs)
      .map((reference) => ({ ...reference, nodeIds: [...reference.nodeIds] })),
    (reference) => `${reference.label}:${reference.nodeIds.join(",")}`,
  );
  const automationDeclarationIds = sortedUnique(
    incomingLinks.flatMap((link) => link.automationDeclarationIds),
  );
  const transitionProfileIds = sortedUnique(
    incomingLinks.flatMap((link) =>
      link.transitionProfileId ? [link.transitionProfileId] : []),
  );
  const declarationIds = sortedUnique([
    ...proofSteps.flatMap((step) =>
      step.declarationGroups.flatMap((group) => group.declarationIds)),
    ...stages.flatMap((stage) => [
      stage.primaryDeclarationId,
      ...stage.evidenceDeclarationIds,
    ]),
    ...incomingLinks.flatMap((link) => [
      ...link.automationDeclarationIds,
      ...link.evidenceDeclarationIds,
    ]),
    ...bindings.flatMap((binding) => [
      binding.problemDeclarationId,
      binding.frameworkDeclarationId,
    ]),
  ]);
  const explicitCtIds = [
    ...stages.flatMap((stage) => stage.tacticId ? [stage.tacticId] : []),
    ...bindings.map((binding) => binding.tacticId),
  ];

  return {
    nodeId,
    ...partitionDeclarations(declarationIds),
    paperReferences,
    proofSteps,
    proofStepIds: sortedUnique(proofSteps.map((step) => step.stepId)),
    stageIds,
    incomingLinkIds: sortedUnique(incomingLinks.map((link) => link.linkId)),
    ctIds: ctIdsFrom([...explicitCtIds, ...transitionProfileIds, ...declarationIds]),
    transitionProfileIds,
    automationDeclarationIds,
    bindings,
    workBounds: workBoundsFor(proofSteps),
  };
}

export function deriveAllErdosNodeCausalEvidence(
  data: ErdosExampleData,
): readonly ErdosNodeCausalEvidence[] {
  const detail = detailOf(data);
  const nodeIds = sortedUniqueNumbers(
    (detail.manuscript?.proofSteps ?? []).flatMap((step) =>
      step.manuscriptRefs.flatMap((reference) => reference.nodeIds)),
  );
  return nodeIds.map((nodeId) => deriveErdosNodeCausalEvidence(data, nodeId));
}

export function createErdosProofHistorySnapshot(
  data: ErdosExampleData,
  recordedAt: string | null = null,
): ErdosProofHistorySnapshot {
  const detail = detailOf(data);
  const response = responseOf(data);
  const manuscript = detail.manuscript;
  const greenNodeIds = sortedUniqueNumbers(manuscript?.formalizedNodeIds ?? []);
  const greenNodes = new Set(greenNodeIds);
  const implementedEvidenceNodeIds = sortedUniqueNumbers(
    (manuscript?.proofSteps ?? [])
      .filter((step) => step.status === "implemented")
      .flatMap((step) => step.manuscriptRefs.flatMap((reference) => reference.nodeIds)),
  );
  const nextNodeIds = sortedUniqueNumbers(
    (manuscript?.proofSteps ?? [])
      .filter((step) => step.status === "next")
      .flatMap((step) => step.manuscriptRefs.flatMap((reference) => reference.nodeIds)),
  );
  const obligations = manuscript?.nodeObligations ?? [];
  const leverage = deriveErdosFrameworkLeverage(data);

  return {
    snapshotVersion: "1.0.0",
    exampleId: detail.exampleId,
    recordedAt,
    catalogHash: response?.catalogHash ?? null,
    frameworkCatalogHash: response?.frameworkCatalogHash ?? null,
    manuscriptSha256: manuscript?.sha256 ?? null,
    sourceDescriptor: detail.sourceOfTruth.descriptor,
    proofStatus: detail.proofStatus,
    greenNodeIds,
    yellowNodeIds: implementedEvidenceNodeIds.filter((nodeId) => !greenNodes.has(nodeId)),
    nextNodeIds,
    provedObligations: obligations.filter((obligation) => obligation.status === "proved").length,
    remainingObligations: obligations.filter((obligation) => obligation.status !== "proved").length,
    coverage: {
      implementedSteps: manuscript?.coverage.implementedSteps ?? 0,
      totalSteps: manuscript?.coverage.totalSteps ?? 0,
      verifiedDiagramNodes: manuscript?.coverage.verifiedDiagramNodes ?? 0,
      totalDiagramNodes: manuscript?.coverage.totalDiagramNodes ?? 0,
      verifiedWorkflowSteps: manuscript?.coverage.verifiedWorkflowSteps ?? 0,
    },
    leverage: leverage.counts,
  };
}
