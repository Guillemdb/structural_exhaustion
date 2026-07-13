import type {
  FrameworkResponse,
  GraphElement,
  ExampleWorkflow,
  RouteRecord,
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

export function machineGraphElements(response: TacticResponse): GraphElement[] {
  return response.graph.elements.filter(
    (element) => element.data.kind !== "generatedRoute",
  );
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
