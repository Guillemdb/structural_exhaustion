import type {
  FrameworkResponse,
  GraphElement,
  ExampleWorkflow,
  TransitionProfileRecord,
  TacticSummary,
  TacticResponse,
  TacticInternalsResponse,
} from "./types";

export function transitionProfileLabel(profile: TransitionProfileRecord): string {
  return profile.sourceResidualKind.replace(`${profile.sourceTacticId}.residual.`, "");
}

export function frameworkGraphElements(framework: FrameworkResponse): GraphElement[] {
  const nodes = framework.tactics.map((tactic) => ({
    data: {
      id: tactic.tacticId,
      label: tactic.tacticId,
      title: tactic.title,
      kind: "tactic",
      nodeCount: tactic.nodeCount,
      terminalCount: tactic.terminalCount,
    },
  }));
  const edges = framework.transitionProfiles.map((profile) => ({
    data: {
      id: profile.profileId,
      source: profile.sourceTacticId,
      target: profile.targetTacticId,
      label: transitionProfileLabel(profile),
      kind: "transitionProfile",
    },
  }));
  const implementedEdges = (framework.implementedTransitions ?? []).map((transition) => ({
    data: {
      id: transition.transitionId,
      source: transition.sourceTacticId,
      target: transition.targetTacticId,
      label: transition.label,
      kind: "implementedTransition",
      relationshipKind: transition.relationshipKind,
      automationClass: transition.automationClass,
      frameworkAutomated: transition.frameworkAutomated,
      exampleId: transition.exampleId,
      workflowId: transition.workflowId,
      linkId: transition.linkId,
    },
  }));
  return [...nodes, ...edges, ...implementedEdges];
}

interface MachineGraphOptions {
  includeOutboundTransitionProfiles?: boolean;
  targetTactics?: TacticSummary[];
}

function normalizedTransitionProfileSuffix(value: string): string {
  return value.toLowerCase().replace(/[^a-z0-9]/g, "");
}

function transitionProfileSourceNode(
  response: TacticResponse,
  profile: TransitionProfileRecord,
): string | undefined {
  const residualSuffix = profile.sourceResidualKind.split(".residual.").at(-1);
  if (!residualSuffix) return undefined;

  const normalizedSuffix = normalizedTransitionProfileSuffix(residualSuffix);
  return response.tactic.nodes.find(
    (node) =>
      node.nodeKind === "residual" &&
      normalizedTransitionProfileSuffix(node.nodeId).endsWith(normalizedSuffix),
  )?.nodeId;
}

function outboundTransitionProfileLabel(profile: TransitionProfileRecord): string {
  const base = transitionProfileLabel(profile);
  const profileTarget = `->${profile.targetTacticId}`;
  const variant = profile.profileId.split(profileTarget)[1]?.replace(/^\./, "");
  return variant ? `${base} · ${variant}` : base;
}

export function machineGraphElements(
  response: TacticResponse,
  options: MachineGraphOptions = {},
): GraphElement[] {
  const machineElements = response.graph.elements.filter(
    (element) => element.data.kind !== "transitionProfile",
  );
  if (
    !options.includeOutboundTransitionProfiles
    || response.outboundTransitionProfiles.length === 0
  ) {
    return machineElements;
  }

  const tacticTitles = new Map(
    (options.targetTactics ?? []).map((tactic) => [tactic.tacticId, tactic.title]),
  );
  const targetNodes = new Map<string, GraphElement>();
  const transitionEdges: GraphElement[] = [];

  for (const profile of response.outboundTransitionProfiles) {
    const source = transitionProfileSourceNode(response, profile);
    if (!source) continue;

    const target = `transition-target:${profile.targetTacticId}`;
    if (!targetNodes.has(target)) {
      const title = tacticTitles.get(profile.targetTacticId);
      targetNodes.set(target, {
        data: {
          id: target,
          label: title ? `${profile.targetTacticId}\n${title}` : profile.targetTacticId,
          kind: "transitionTargetTactic",
          tacticId: profile.targetTacticId,
        },
      });
    }
    transitionEdges.push({
      data: {
        id: profile.profileId,
        source,
        target,
        label: outboundTransitionProfileLabel(profile),
        kind: "transitionProfile",
        transitionProfileId: profile.profileId,
      },
    });
  }

  return [...machineElements, ...targetNodes.values(), ...transitionEdges];
}

function internalStepId(nodeId: string, stepId: string): string {
  return `internal:step:${nodeId}:${stepId}`;
}

export function internalDeclarationId(nodeId: string, name: string): string {
  return `internal:declaration:${nodeId}:${name}`;
}

function declarationLabel(name: string, kind?: string): string {
  const tail = name.split(".").at(-1) ?? name;
  return kind ? `${tail}\n${kind}` : `${tail}\nexternal`;
}

export function expandedMachineGraphElements(
  response: TacticResponse,
  internalsResponse: TacticInternalsResponse,
  expandedNodeId: string,
  expandedDeclarations: ReadonlySet<string> = new Set(),
): GraphElement[] {
  const overview = machineGraphElements(response);
  const internalNode = internalsResponse.internals.nodes.find(
    (candidate) => candidate.nodeId === expandedNodeId,
  );
  if (!internalNode) return overview;

  const declarations = new Map(
    internalsResponse.internals.declarations.map((declaration) => [
      declaration.declarationId,
      declaration,
    ]),
  );
  const elements = overview.map((element) =>
    element.data.id === expandedNodeId
      ? { data: { ...element.data, expanded: true } }
      : element,
  );
  const stepDeclarationIds = new Set(
    internalNode.internalFlow.steps.flatMap((step) =>
      step.declarationId ? [step.declarationId] : [],
    ),
  );

  for (const step of internalNode.internalFlow.steps) {
    elements.push({
      data: {
        id: internalStepId(expandedNodeId, step.stepId),
        parent: expandedNodeId,
        label: step.label,
        kind: "internalStep",
        internalKind: "step",
        nodeId: expandedNodeId,
        stepId: step.stepId,
        role: step.role,
        declarationId: step.declarationId ?? undefined,
      },
    });
  }
  for (const edge of internalNode.internalFlow.edges) {
    elements.push({
      data: {
        id: `internal:edge:${expandedNodeId}:${edge.edgeId}`,
        source: internalStepId(expandedNodeId, edge.sourceStepId),
        target: internalStepId(expandedNodeId, edge.targetStepId),
        label: edge.relation,
        kind: "internalFlow",
        internalKind: "flowEdge",
        relation: edge.relation,
      },
    });
  }

  const addedDeclarations = new Set<string>();
  const addDependencyNode = (name: string) => {
    if (addedDeclarations.has(name) || stepDeclarationIds.has(name)) return;
    const declaration = declarations.get(name);
    elements.push({
      data: {
        id: internalDeclarationId(expandedNodeId, name),
        parent: expandedNodeId,
        label: declarationLabel(name, declaration?.kind),
        kind: declaration?.projectLocal === false || !declaration
          ? "externalDeclaration"
          : "leanDeclaration",
        internalKind: "declaration",
        declarationId: name,
        projectLocal: declaration?.projectLocal ?? false,
      },
    });
    addedDeclarations.add(name);
  };

  const roots = new Map<string, string>();
  for (const step of internalNode.internalFlow.steps) {
    if (step.declarationId) {
      roots.set(step.declarationId, internalStepId(expandedNodeId, step.stepId));
    }
  }
  const pending = [...roots.keys()].filter((name) => expandedDeclarations.has(name));
  const processed = new Set<string>();
  while (pending.length) {
    const name = pending.shift()!;
    if (processed.has(name)) continue;
    const declaration = declarations.get(name);
    const source = roots.get(name) ?? internalDeclarationId(expandedNodeId, name);
    if (
      !declaration
      || !declaration.projectLocal
      || (!roots.has(name) && !addedDeclarations.has(name))
    ) continue;
    processed.add(name);
    const dependencies = [
      ...declaration.typeDependencies.map((dependency) => ({
        dependency,
        kind: "typeDependency",
      })),
      ...declaration.bodyDependencies.map((dependency) => ({
        dependency,
        kind: "bodyDependency",
      })),
    ];
    for (const { dependency, kind } of dependencies) {
      if (dependency === name) continue;
      addDependencyNode(dependency);
      const target = stepDeclarationIds.has(dependency)
        ? roots.get(dependency)
        : internalDeclarationId(expandedNodeId, dependency);
      if (!target) continue;
      elements.push({
        data: {
          id: `internal:dependency:${expandedNodeId}:${kind}:${name}:${dependency}`,
          source,
          target,
          label: kind === "typeDependency" ? "in type" : "in body",
          kind,
          internalKind: "dependencyEdge",
        },
      });
      if (
        expandedDeclarations.has(dependency)
        && declarations.get(dependency)?.projectLocal
      ) {
        pending.push(dependency);
      }
    }
  }
  return elements;
}

export function exampleGraphElements(workflow: ExampleWorkflow): GraphElement[] {
  const nodes = workflow.stages.map((stage) => ({
    data: {
      id: stage.stageId,
      label: stage.tacticId ? `${stage.tacticId}\n${stage.title}` : stage.title,
      kind: stage.kind,
      tacticId: stage.tacticId ?? undefined,
    },
  }));
  const edges = workflow.links.map((link) => ({
    data: {
      id: link.linkId,
      source: link.sourceStageId,
      target: link.targetStageId,
      label: link.label,
      kind: link.kind,
      transitionProfileId: link.transitionProfileId ?? undefined,
    },
  }));
  return [...nodes, ...edges];
}
