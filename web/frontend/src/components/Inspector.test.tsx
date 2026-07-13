import { fireEvent, render, screen, within } from "@testing-library/react";
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
    requiredDefinitions: [
      {
        conceptId: "CT6.capability.activeSite",
        ref: "StructuralExhaustion.CT6.Capability.ActiveSite",
        provision: "user_definition",
      },
    ],
    requiredInstances: [],
    derivedOperations: [],
  },
  capabilityProfiles: [
    {
      tacticId: "CT6",
      capabilityId: "StructuralExhaustion.CT6.profile.specialized",
      requiredDefinitions: [
        {
          conceptId: "CT6.capability.activeSite",
          ref: "StructuralExhaustion.CT6.Capability.ActiveSite",
          provision: "user_definition",
        },
        {
          conceptId: "CT6.profile.siteRank",
          ref: "StructuralExhaustion.CT6.Profile.siteRank",
          provision: "user_operator",
        },
      ],
      requiredInstances: [],
      derivedOperations: [],
    },
  ],
  capabilityConcepts: [
    {
      conceptId: "CT6.capability.activeSite",
      requirementRef: "StructuralExhaustion.CT6.Capability.ActiveSite",
      formalDeclaration: {
        name: "StructuralExhaustion.CT6.Capability.ActiveSite",
        kind: "definition",
        type: "(G : P.Ambient) → Type uSite",
      },
      presentation: {
        label: "Active site",
        mathematicalDefinition: "\\mathcal{A}(G) = \\{a : a \\text{ is active in } G\\}",
        plainExplanation: "The local sites that CT6 examines in the ambient object.",
      },
    },
    {
      conceptId: "CT6.profile.siteRank",
      requirementRef: "StructuralExhaustion.CT6.Profile.siteRank",
      formalDeclaration: {
        name: "StructuralExhaustion.CT6.Profile.siteRank",
        kind: "definition",
        type: "ActiveSite G → Nat",
      },
      presentation: {
        label: "Site rank",
        mathematicalDefinition: "r : \\mathcal{A}(G) \\to \\mathbb{N}",
        plainExplanation: "Assigns an ordering rank to each active site.",
      },
    },
  ],
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

  it("expands a capability definition with mathematical and formal metadata", () => {
    const { container } = render(
      <MemoryRouter>
        <Inspector
          tactic={tactic}
          inboundRoutes={[]}
          outboundRoutes={[]}
        />
      </MemoryRouter>,
    );

    const activeSite = within(container).getAllByText("Active site")[0];
    expect(activeSite).toBeVisible();
    fireEvent.click(activeSite);

    expect(screen.getByText("The local sites that CT6 examines in the ambient object.")).toBeVisible();
    expect(screen.getByText("(G : P.Ambient) → Type uSite")).toBeVisible();
    const activeDefinition = container.querySelector<HTMLElement>(
      "#capability-concept-CT6-capability-activeSite",
    );
    expect(activeDefinition).not.toBeNull();
    expect(within(activeDefinition!).getAllByText("user definition")).toHaveLength(2);
    expect(screen.getByLabelText("Mathematical definition of Active site")).toBeVisible();
    expect(container.querySelector(".math-formula .katex")).not.toBeNull();
    expect(container.querySelector(".math-formula math")).not.toBeNull();
  });

  it("lists profile requirements without repeating base concept details", () => {
    const { container } = render(
      <MemoryRouter>
        <Inspector
          tactic={tactic}
          inboundRoutes={[]}
          outboundRoutes={[]}
        />
      </MemoryRouter>,
    );

    fireEvent.click(within(container).getByText("StructuralExhaustion.CT6.profile.specialized"));

    expect(within(container).getByText("Shared with base capability")).toHaveAttribute(
      "href",
      "#capability-concept-CT6-capability-activeSite",
    );
    expect(within(container).getByText("Site rank")).toBeVisible();
    expect(within(container).getAllByLabelText("Mathematical definition of Active site")).toHaveLength(1);
  });
});
