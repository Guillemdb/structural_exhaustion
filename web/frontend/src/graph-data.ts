import type {
  FrameworkResponse,
  GraphElement,
  ExampleWorkflow,
  RouteRecord,
  TacticSummary,
  TacticResponse,
} from "./types";

export function routeLabel(route: RouteRecord): string {
  return route.sourceResidualKind.replace(`${route.sourceTacticId}.residual.`, "");
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
  const edges = framework.routes.map((route) => ({
    data: {
      id: route.routeId,
      source: route.sourceTacticId,
      target: route.targetTacticId,
      label: routeLabel(route),
      kind: "route",
    },
  }));
  return [...nodes, ...edges];
}

interface MachineGraphOptions {
  includeOutboundRoutes?: boolean;
  targetTactics?: TacticSummary[];
}

function normalizedRouteSuffix(value: string): string {
  return value.toLowerCase().replace(/[^a-z0-9]/g, "");
}

function routeSourceNode(response: TacticResponse, route: RouteRecord): string | undefined {
  const residualSuffix = route.sourceResidualKind.split(".residual.").at(-1);
  if (!residualSuffix) return undefined;

  const normalizedSuffix = normalizedRouteSuffix(residualSuffix);
  return response.tactic.nodes.find(
    (node) =>
      node.nodeKind === "residual" &&
      normalizedRouteSuffix(node.nodeId).endsWith(normalizedSuffix),
  )?.nodeId;
}

function outboundRouteLabel(route: RouteRecord): string {
  const base = routeLabel(route);
  const routeTarget = `->${route.targetTacticId}`;
  const variant = route.routeId.split(routeTarget)[1]?.replace(/^\./, "");
  return variant ? `${base} · ${variant}` : base;
}

export function machineGraphElements(
  response: TacticResponse,
  options: MachineGraphOptions = {},
): GraphElement[] {
  const machineElements = response.graph.elements.filter(
    (element) => element.data.kind !== "generatedRoute",
  );
  if (!options.includeOutboundRoutes || response.outboundRoutes.length === 0) {
    return machineElements;
  }

  const tacticTitles = new Map(
    (options.targetTactics ?? []).map((tactic) => [tactic.tacticId, tactic.title]),
  );
  const targetNodes = new Map<string, GraphElement>();
  const routeEdges: GraphElement[] = [];

  for (const route of response.outboundRoutes) {
    const source = routeSourceNode(response, route);
    if (!source) continue;

    const target = `route-target:${route.targetTacticId}`;
    if (!targetNodes.has(target)) {
      const title = tacticTitles.get(route.targetTacticId);
      targetNodes.set(target, {
        data: {
          id: target,
          label: title ? `${route.targetTacticId}\n${title}` : route.targetTacticId,
          kind: "routedTactic",
          tacticId: route.targetTacticId,
        },
      });
    }
    routeEdges.push({
      data: {
        id: route.routeId,
        source,
        target,
        label: outboundRouteLabel(route),
        kind: "route",
        routeId: route.routeId,
      },
    });
  }

  return [...machineElements, ...targetNodes.values(), ...routeEdges];
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
      routeId: link.routeId ?? undefined,
    },
  }));
  return [...nodes, ...edges];
}
