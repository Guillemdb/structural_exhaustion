import { describe, expect, it } from "vitest";

import {
  exampleGraphElements,
  frameworkGraphElements,
  machineGraphElements,
} from "./graph-data";
import type { ExampleWorkflow, FrameworkResponse, TacticResponse } from "./types";

describe("graph projections", () => {
  it("builds the framework graph from generated tactic and route records", () => {
    const framework = {
      tactics: [
        { tacticId: "CT6", title: "Activity", nodeCount: 4, terminalCount: 2 },
        { tacticId: "CT9", title: "Overload", nodeCount: 5, terminalCount: 2 },
      ],
      routes: [
        {
          routeId: "CT6.residual.activeLedger->CT9",
          sourceTacticId: "CT6",
          sourceResidualKind: "CT6.residual.activeLedger",
          targetTacticId: "CT9",
        },
      ],
    } as FrameworkResponse;

    expect(frameworkGraphElements(framework).map((element) => element.data)).toEqual([
      expect.objectContaining({ id: "CT6", kind: "tactic" }),
      expect.objectContaining({ id: "CT9", kind: "tactic" }),
      expect.objectContaining({
        id: "CT6.residual.activeLedger->CT9",
        source: "CT6",
        target: "CT9",
        label: "activeLedger",
        kind: "route",
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
