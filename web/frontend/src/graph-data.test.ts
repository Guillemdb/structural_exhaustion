import { describe, expect, it } from "vitest";

import {
  exampleGraphElements,
  expandedMachineGraphElements,
  frameworkGraphElements,
  machineGraphElements,
} from "./graph-data";
import type {
  ExampleWorkflow,
  FrameworkResponse,
  TacticInternalsResponse,
  TacticResponse,
} from "./types";

describe("graph projections", () => {
  it("builds the framework graph from generated tactic and route records", () => {
    const framework = {
      tactics: [
        { tacticId: "CT6", title: "Activity", nodeCount: 4, terminalCount: 2 },
        { tacticId: "CT9", title: "Overload", nodeCount: 5, terminalCount: 2 },
        { tacticId: "CT10", title: "Classification", nodeCount: 8, terminalCount: 3 },
      ],
      routes: [
        {
          routeId: "CT6.residual.activeLedger->CT9",
          sourceTacticId: "CT6",
          sourceResidualKind: "CT6.residual.activeLedger",
          targetTacticId: "CT9",
        },
      ],
      implementedTransitions: [
        {
          transitionId: "implemented:erdos-64:proof-slice:labels-surplus",
          sourceTacticId: "CT10",
          targetTacticId: "CT6",
          relationshipKind: "frameworkComposition",
          automationClass: "frameworkExecutor",
          frameworkAutomated: true,
          automationDeclarationIds: [
            "StructuralExhaustion.Graph.SurplusPortActivity.run",
          ],
          label: "same selected graph",
          exampleId: "erdos-64",
          workflowId: "proof-slice",
          linkId: "proof-slice.labels-surplus-ct6",
        },
      ],
    } as FrameworkResponse;

    expect(frameworkGraphElements(framework).map((element) => element.data)).toEqual([
      expect.objectContaining({ id: "CT6", kind: "tactic" }),
      expect.objectContaining({ id: "CT9", kind: "tactic" }),
      expect.objectContaining({ id: "CT10", kind: "tactic" }),
      expect.objectContaining({
        id: "CT6.residual.activeLedger->CT9",
        source: "CT6",
        target: "CT9",
        label: "activeLedger",
        kind: "route",
      }),
      expect.objectContaining({
        id: "implemented:erdos-64:proof-slice:labels-surplus",
        source: "CT10",
        target: "CT6",
        label: "same selected graph",
        kind: "implementedTransition",
        relationshipKind: "frameworkComposition",
        automationClass: "frameworkExecutor",
        frameworkAutomated: true,
        exampleId: "erdos-64",
      }),
    ]);
  });

  it("removes route callout pseudo-nodes from an individual machine graph", () => {
    const response = {
      graph: {
        tacticId: "CT6",
        elements: [
          { data: { id: "CT6.entry", kind: "entry" } },
          { data: { id: "route", kind: "generatedRoute" } },
          { data: { id: "edge", source: "CT6.entry", target: "CT6.end" } },
        ],
      },
    } as TacticResponse;

    expect(machineGraphElements(response).map((element) => element.data.id)).toEqual([
      "CT6.entry",
      "edge",
    ]);
  });

  it("optionally connects residual terminals to deduplicated destination CT nodes", () => {
    const response = {
      tactic: {
        nodes: [
          { nodeId: "CT1.entry", nodeKind: "entry" },
          { nodeId: "CT1.terminal.avoiding", nodeKind: "residual" },
        ],
      },
      graph: {
        tacticId: "CT1",
        elements: [
          { data: { id: "CT1.entry", kind: "entry" } },
          { data: { id: "CT1.terminal.avoiding", kind: "residual" } },
        ],
      },
      outboundRoutes: [
        {
          routeId: "CT1.residual.avoiding->CT2",
          sourceTacticId: "CT1",
          sourceResidualKind: "CT1.residual.avoiding",
          targetTacticId: "CT2",
        },
        {
          routeId: "CT1.residual.avoiding->CT2.localDeletion",
          sourceTacticId: "CT1",
          sourceResidualKind: "CT1.residual.avoiding",
          targetTacticId: "CT2",
        },
      ],
    } as TacticResponse;

    const elements = machineGraphElements(response, {
      includeOutboundRoutes: true,
      targetTactics: [
        {
          tacticId: "CT2",
          title: "Minimal deletion",
          apiVersion: "1.0.0",
          namespace: "StructuralExhaustion.CT2",
          nodeCount: 6,
          transitionCount: 5,
          terminalCount: 4,
          residualCount: 2,
          manualObligationCount: 0,
        },
      ],
    }).map((element) => element.data);

    expect(elements).toEqual([
      { id: "CT1.entry", kind: "entry" },
      { id: "CT1.terminal.avoiding", kind: "residual" },
      {
        id: "route-target:CT2",
        label: "CT2\nMinimal deletion",
        kind: "routedTactic",
        tacticId: "CT2",
      },
      {
        id: "CT1.residual.avoiding->CT2",
        source: "CT1.terminal.avoiding",
        target: "route-target:CT2",
        label: "avoiding",
        kind: "route",
        routeId: "CT1.residual.avoiding->CT2",
      },
      {
        id: "CT1.residual.avoiding->CT2.localDeletion",
        source: "CT1.terminal.avoiding",
        target: "route-target:CT2",
        label: "avoiding · localDeletion",
        kind: "route",
        routeId: "CT1.residual.avoiding->CT2.localDeletion",
      },
    ]);
  });

  it("expands exactly one CT node into curated steps and on-demand Lean dependencies", () => {
    const response = {
      graph: {
        tacticId: "CT1",
        elements: [
          { data: { id: "CT1.entry", label: "CT1.entry", kind: "entry" } },
          { data: { id: "CT1.next", label: "CT1.next", kind: "computation" } },
          {
            data: {
              id: "high-edge",
              label: "begin",
              kind: "ctTransition",
              ordinal: 1,
              source: "CT1.entry",
              target: "CT1.next",
              constructor: "StructuralExhaustion.CT1.Graph.Edge.begin",
              constructorType: "Graph.Edge .entry .next",
              provision: "generated_audit",
            },
          },
        ],
      },
      outboundRoutes: [],
    } as unknown as TacticResponse;
    const declaration = (name: string, dependencies: string[] = []) => ({
      declarationId: name,
      name,
      kind: "definition",
      type: "Type",
      docString: null,
      module: "StructuralExhaustion.CT1.Test",
      sourceFile: "StructuralExhaustion/CT1/Test.lean",
      range: null,
      selectionRange: null,
      bodyAvailable: true,
      typeDependencies: dependencies,
      bodyDependencies: [],
      projectLocal: true,
      sourceId: "StructuralExhaustion/CT1/Test.lean",
    });
    const internals = {
      internals: {
        nodes: [{
          nodeId: "CT1.entry",
          internalFlow: {
            nodeId: "CT1.entry",
            steps: [
              {
                stepId: "input.1",
                role: "authorObject",
                reference: { ref: "StructuralExhaustion.CT1.A", provision: "user_definition" },
                plainExplanation: "Input A.",
                mathematicalDefinition: "A",
                label: "A",
                declarationId: "StructuralExhaustion.CT1.A",
              },
              {
                stepId: "output.1",
                role: "output",
                reference: { ref: "StructuralExhaustion.CT1.Output", provision: "derived_by_computation" },
                plainExplanation: "Output.",
                mathematicalDefinition: null,
                label: "Output",
                declarationId: "StructuralExhaustion.CT1.Output",
              },
            ],
            edges: [{
              edgeId: "inside",
              sourceStepId: "input.1",
              targetStepId: "output.1",
              relation: "produces",
            }],
          },
        }],
        declarations: [
          declaration("StructuralExhaustion.CT1.A", [
            "StructuralExhaustion.Core.B",
            "Nat",
          ]),
          declaration("StructuralExhaustion.Core.B", ["StructuralExhaustion.Core.C"]),
          declaration("StructuralExhaustion.Core.C"),
          declaration("StructuralExhaustion.CT1.Output"),
        ],
        sources: [],
      },
    } as unknown as TacticInternalsResponse;

    const firstLevel = expandedMachineGraphElements(
      response,
      internals,
      "CT1.entry",
      new Set(["StructuralExhaustion.CT1.A"]),
    ).map((element) => element.data);
    expect(firstLevel.find((element) => element.id === "CT1.entry")).toMatchObject({
      expanded: true,
    });
    expect(firstLevel.find((element) => element.id === "high-edge")).toMatchObject({
      label: "begin",
      kind: "ctTransition",
      source: "CT1.entry",
      target: "CT1.next",
    });
    expect(firstLevel.filter((element) => element.internalKind === "step")).toHaveLength(2);
    expect(firstLevel.filter((element) => element.internalKind === "step")).toEqual(
      expect.arrayContaining([expect.objectContaining({ parent: "CT1.entry", role: "authorObject" })]),
    );
    expect(firstLevel.some((element) => element.declarationId === "StructuralExhaustion.Core.B")).toBe(true);
    expect(firstLevel.some((element) => element.declarationId === "Nat")).toBe(true);
    expect(firstLevel.some((element) => element.declarationId === "StructuralExhaustion.Core.C")).toBe(false);

    const secondLevel = expandedMachineGraphElements(
      response,
      internals,
      "CT1.entry",
      new Set(["StructuralExhaustion.CT1.A", "StructuralExhaustion.Core.B"]),
    );
    expect(secondLevel.some(
      (element) => element.data.declarationId === "StructuralExhaustion.Core.C",
    )).toBe(true);
    expect(secondLevel.find((element) => element.data.id === "high-edge")?.data).toMatchObject({
      label: "begin",
      kind: "ctTransition",
    });
  });

  it("projects example stages and typed relationships without inventing composition", () => {
    const workflow = {
      workflowId: "main",
      title: "Main route",
      summary: "A generated workflow.",
      purpose: "Show the proof path.",
      completion: "complete",
      stages: [
        {
          stageId: "ct6",
          title: "Activity search",
          summary: "Run CT6.",
          kind: "tactic",
          tacticId: "CT6",
          primaryDeclarationId: "ct6.run",
          evidenceDeclarationIds: [],
        },
        {
          stageId: "ct9",
          title: "Overload",
          summary: "Run CT9.",
          kind: "tactic",
          tacticId: "CT9",
          primaryDeclarationId: "ct9.run",
          evidenceDeclarationIds: [],
        },
      ],
      links: [
        {
          linkId: "ct6-to-ct9",
          sourceStageId: "ct6",
          targetStageId: "ct9",
          kind: "registeredRoute",
          label: "active ledger",
          summary: "The registered residual route.",
          routeId: "CT6.residual.activeLedger->CT9",
          automationDeclarationIds: [
            "StructuralExhaustion.Routes.CT6ToCT9.routeContract",
          ],
          evidenceDeclarationIds: [],
        },
      ],
    } satisfies ExampleWorkflow;

    expect(exampleGraphElements(workflow).map((element) => element.data)).toEqual([
      expect.objectContaining({ id: "ct6", label: "CT6\nActivity search", kind: "tactic" }),
      expect.objectContaining({ id: "ct9", label: "CT9\nOverload", kind: "tactic" }),
      expect.objectContaining({
        id: "ct6-to-ct9",
        source: "ct6",
        target: "ct9",
        kind: "registeredRoute",
        routeId: "CT6.residual.activeLedger->CT9",
      }),
    ]);
  });
});
