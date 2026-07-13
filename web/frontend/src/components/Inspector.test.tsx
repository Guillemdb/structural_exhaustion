import { fireEvent, render, screen } from "@testing-library/react";
import { MemoryRouter } from "react-router-dom";
import { describe, expect, it } from "vitest";

import type { NodeRecord, TacticRecord } from "../types";
import { Inspector } from "./Inspector";

const node: NodeRecord = {
  ordinal: 2,
  nodeId: "CT6.search.firstFailure",
  semanticId: "CT6.search.firstFailure",
  nodeKind: "computation",
  constructor: "StructuralExhaustion.CT6.Graph.NodeId.firstFailureSearch",
  sourceFile: "StructuralExhaustion/CT6/Graph.lean",
  presentation: {
    label: "CT6.search.firstFailure",
    summary: "Compiled computation node with an explicit automation contract.",
  },
  formalContract: {
    predecessorIndexed: true,
    incomingEdges: [],
    outgoingEdges: [],
  },
  automation: {
    executionClass: "finiteSearch",
    authorInputs: [
      { ref: "Capability.failureOrder", provision: "user_finite_enumeration" },
    ],
    inferredInputs: [],
    predecessorInputs: [],
    derivedInputs: [],
    frameworkTheorems: [],
    transitiveDependencies: [],
    generatedOutputs: [
      { ref: "CT6.ActiveLedgerResidual", provision: "derived_by_generic_theorem" },
    ],
    manualObligations: [],
  },
};

const tactic = {
  tacticId: "CT6",
  title: "Ordered activity failure",
  apiVersion: "CT6-v5",
  namespace: "StructuralExhaustion.CT6",
  capability: {
    tacticId: "CT6",
    capabilityId: "StructuralExhaustion.CT6.reference",
    requiredDefinitions: [],
    requiredInstances: [],
    derivedOperations: [],
  },
  capabilityProfiles: [],
  nodes: [node],
  transitions: [],
  terminals: [],
  residualKinds: [],
  apiDeclarations: [],
  loopDecrease: null,
} satisfies TacticRecord;

describe("Inspector", () => {
  it("shows generated node metadata and contract categories", () => {
    render(
      <MemoryRouter>
        <Inspector
          tactic={tactic}
          node={node}
          inboundRoutes={[]}
          outboundRoutes={[]}
        />
      </MemoryRouter>,
    );

    expect(screen.getByRole("heading", { name: "CT6.search.firstFailure" })).toBeVisible();
    expect(screen.getByText("finiteSearch")).toBeVisible();
    expect(screen.getByText("CT6.ActiveLedgerResidual")).toBeVisible();

    fireEvent.click(screen.getByRole("tab", { name: "contract" }));
    expect(screen.getByText("Capability.failureOrder")).toBeVisible();
    expect(screen.getByText("user finite enumeration")).toBeVisible();
  });
});
