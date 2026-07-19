import { fireEvent, render, screen } from "@testing-library/react";
import { MemoryRouter, useLocation } from "react-router-dom";
import { beforeEach, describe, expect, it, vi } from "vitest";

import { fetchDocumentation, fetchFramework } from "../api";
import type {
  DocumentationResponse,
  FrameworkResponse,
  GraphElement,
  SelectedGraphElement,
} from "../types";
import { FrameworkPage } from "./FrameworkPage";

vi.mock("../api", () => ({ fetchFramework: vi.fn(), fetchDocumentation: vi.fn() }));
vi.mock("../components/AppHeader", () => ({ AppHeader: () => null }));
vi.mock("../components/GraphCanvas", () => ({
  GraphCanvas: ({
    elements,
    onSelect,
  }: {
    elements: GraphElement[];
    onSelect?: (selection: SelectedGraphElement | null) => void;
  }) => (
    <div aria-label="Mock framework graph">
      {elements.map((element) => (
        <button
          key={element.data.id}
          type="button"
          onClick={() => onSelect?.({
            id: element.data.id,
            group: element.data.source ? "edge" : "node",
            data: element.data,
          })}
        >
          graph:{element.data.id}
        </button>
      ))}
    </div>
  ),
}));

const transitionId =
  "implemented:even-cycle:main:main.ct10-ct6";

const framework = {
  catalog: {
    schemaVersion: "9.0.0",
    catalogHash: "catalog-hash",
    sourceOfTruth: { kind: "compiledLeanEnvironment" },
  },
  exampleVerification: { state: "verified" },
  totals: {
    tactics: 2,
    nodes: 16,
    transitions: 10,
    terminals: 6,
    residualKinds: 4,
    transitionFamilies: 0,
    transitionProfiles: 0,
    implementedTransitions: 1,
    manualObligations: 0,
  },
  tactics: [
    {
      tacticId: "CT10",
      title: "Finite refinement classification",
      nodeCount: 8,
      terminalCount: 3,
      residualCount: 2,
    },
    {
      tacticId: "CT6",
      title: "Ordered activity failure",
      nodeCount: 4,
      terminalCount: 2,
      residualCount: 2,
    },
  ],
  transitionFamilies: [],
  transitionProfiles: [],
  implementedTransitions: [
    {
      transitionId,
      sourceTacticId: "CT10",
      targetTacticId: "CT6",
      relationshipKind: "frameworkComposition",
      automationClass: "frameworkExecutor",
      frameworkAutomated: true,
      automationDeclarationIds: [
        "StructuralExhaustion.Graph.SurplusPortActivity.run",
      ],
      label: "same selected graph",
      summary: "The exact CT10 predecessor is retained for the CT6 surplus run.",
      exampleId: "even-cycle",
      exampleTitle: "Even cycle",
      workflowId: "main",
      workflowTitle: "Even-cycle workflow",
      workflowCompletion: "complete",
      linkId: "proof-slice.labels-surplus-ct6",
      sourceStageId: "proof-slice.p13-labels",
      sourceStageTitle: "CT10 label algebra",
      sourceDeclarationId: "Erdos64EG.Internal.verifiedP13LabelAlgebraPrefix",
      targetStageId: "proof-slice.surplus-ct6",
      targetStageTitle: "CT6 sparse surplus",
      targetDeclarationId: "Erdos64EG.Internal.verifiedSparseSurplusPrefix",
      transitionProfileId: null,
      evidenceDeclarationIds: [
        "Erdos64EG.Internal.verifiedSparseSurplusPrefix",
      ],
    },
  ],
} as unknown as FrameworkResponse;

const documentation = {
  tacticGuides: [
    { tacticId: "CT10", role: "Classification", useWhen: "Classify finite refinements.", leanEntry: "Run CT10." },
    { tacticId: "CT6", role: "Ordered failure", useWhen: "Inspect a first failure.", leanEntry: "Run CT6." },
  ],
} as unknown as DocumentationResponse;

function LocationProbe() {
  return <output aria-label="Current location">{useLocation().pathname}</output>;
}

describe("FrameworkPage implemented transitions", () => {
  beforeEach(() => {
    vi.clearAllMocks();
    vi.mocked(fetchFramework).mockResolvedValue(framework);
    vi.mocked(fetchDocumentation).mockResolvedValue(documentation);
  });

  it("renders and inspects a non-Erdős CT composition", async () => {
    render(
      <MemoryRouter initialEntries={["/"]}>
        <FrameworkPage />
        <LocationProbe />
      </MemoryRouter>,
    );

    const edge = await screen.findByRole("button", {
      name: `graph:${transitionId}`,
    });
    expect(screen.getByText("1", { selector: ".stat-strip strong" })).toBeVisible();

    fireEvent.click(edge);
    expect(screen.getByText("CT10 → CT6", { selector: "strong" })).toBeVisible();
    expect(screen.getByText("same selected graph")).toBeVisible();
    expect(screen.getByText("Framework automated")).toBeVisible();
    expect(screen.getByText(
      "StructuralExhaustion.Graph.SurplusPortActivity.run",
    )).toBeVisible();
    expect(screen.getByText(/Even cycle/)).toBeVisible();
    expect(screen.getByText(
      "Erdos64EG.Internal.verifiedP13LabelAlgebraPrefix",
      { selector: ".implemented-transition-map code" },
    )).toBeVisible();
    expect(screen.getByText(
      "Erdos64EG.Internal.verifiedSparseSurplusPrefix",
      { selector: ".implemented-transition-map code" },
    )).toBeVisible();

    fireEvent.click(screen.getByRole("button", { name: "Inspect proof workflow" }));
    expect(screen.getByRole("status", { name: "Current location" })).toHaveTextContent(
      "/examples/even-cycle",
    );
  });
});
