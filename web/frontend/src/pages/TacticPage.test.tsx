import { fireEvent, render, screen, waitFor } from "@testing-library/react";
import { MemoryRouter, Route, Routes, useLocation } from "react-router-dom";
import { beforeEach, describe, expect, it, vi } from "vitest";

import { fetchFramework, fetchTactic, fetchTacticInternals } from "../api";
import type {
  FrameworkResponse,
  GraphElement,
  SelectedGraphElement,
  TacticResponse,
} from "../types";
import { TacticPage } from "./TacticPage";

vi.mock("../api", () => ({
  fetchFramework: vi.fn(),
  fetchTactic: vi.fn(),
  fetchTacticInternals: vi.fn(),
}));
vi.mock("../components/AppHeader", () => ({ AppHeader: () => null }));
vi.mock("../components/Inspector", () => ({ Inspector: () => null }));
vi.mock("../components/TransitionProfileList", () => ({
  TransitionProfileList: () => null,
}));
vi.mock("../components/GraphCanvas", () => ({
  GraphCanvas: ({
    elements,
    onSelect,
  }: {
    elements: GraphElement[];
    onSelect?: (selection: SelectedGraphElement | null) => void;
  }) => (
    <div aria-label="Mock CT graph">
      {elements.map((element) => (
        <button
          type="button"
          key={element.data.id}
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

const transitionProfile = {
  profileId: "CT1.residual.avoiding->CT2",
  familyId: "CT1->CT2",
  sourceTacticId: "CT1",
  sourceResidualKind: "CT1.residual.avoiding",
  targetTacticId: "CT2",
};

const tacticResponse = {
  artifactWarnings: [],
  catalogHash: "catalog-hash",
  tactic: {
    tacticId: "CT1",
    title: "Finite target realization",
    nodes: [
      { nodeId: "CT1.entry", nodeKind: "entry" },
      { nodeId: "CT1.terminal.avoiding", nodeKind: "residual" },
    ],
    transitions: [],
    terminals: [],
  },
  graph: {
    tacticId: "CT1",
    elements: [
      { data: { id: "CT1.entry", kind: "entry" } },
      { data: { id: "CT1.terminal.avoiding", kind: "residual" } },
    ],
  },
  inboundTransitionProfiles: [],
  outboundTransitionProfiles: [transitionProfile],
} as unknown as TacticResponse;

const internalsResponse = {
  artifactWarnings: [],
  catalogHash: "catalog-hash",
  internals: {
    nodes: [{
      nodeId: "CT1.entry",
      internalFlow: {
        nodeId: "CT1.entry",
        steps: [{
          stepId: "author.1",
          role: "authorObject",
          reference: { ref: "StructuralExhaustion.CT1.Input", provision: "user_definition" },
          plainExplanation: "The input object.",
          mathematicalDefinition: "I",
          label: "Input",
          declarationId: "StructuralExhaustion.CT1.Input",
        }],
        edges: [],
      },
    }],
    declarations: [],
    sources: [],
  },
};

const frameworkResponse = {
  artifactWarnings: [],
  tactics: [
    {
      tacticId: "CT1",
      title: "Finite target realization",
      nodeCount: 2,
    },
    {
      tacticId: "CT2",
      title: "Minimal deletion or replacement",
      nodeCount: 6,
    },
  ],
} as unknown as FrameworkResponse;

function LocationProbe() {
  return <output aria-label="Current location">{useLocation().pathname}</output>;
}

describe("TacticPage transition-profile overlay", () => {
  beforeEach(() => {
    vi.clearAllMocks();
    vi.mocked(fetchTactic).mockResolvedValue(tacticResponse);
    vi.mocked(fetchFramework).mockResolvedValue(frameworkResponse);
    vi.mocked(fetchTacticInternals).mockResolvedValue(internalsResponse as never);
  });

  it("toggles outbound transition profiles and opens a destination CT node", async () => {
    render(
      <MemoryRouter initialEntries={["/ct/CT1"]}>
        <Routes>
          <Route path="/ct/:tacticId" element={<TacticPage />} />
        </Routes>
        <LocationProbe />
      </MemoryRouter>,
    );

    const toggle = await screen.findByRole("checkbox", {
      name: "Show transition profiles to other CTs",
    });
    expect(toggle).not.toBeChecked();
    expect(screen.queryByRole("button", {
      name: "graph:transition-target:CT2",
    })).toBeNull();

    fireEvent.click(toggle);
    expect(toggle).toBeChecked();
    expect(screen.getByRole("button", { name: "graph:CT1.residual.avoiding->CT2" })).toBeVisible();

    fireEvent.click(screen.getByRole("button", {
      name: "graph:transition-target:CT2",
    }));
    expect(screen.getByRole("status", { name: "Current location" })).toHaveTextContent("/ct/CT2");
  });

  it("loads low-level data only after selection and restores the overview", async () => {
    render(
      <MemoryRouter initialEntries={["/ct/CT1"]}>
        <Routes>
          <Route path="/ct/:tacticId" element={<TacticPage />} />
        </Routes>
      </MemoryRouter>,
    );

    const transitionToggle = await screen.findByRole("checkbox", {
      name: "Show transition profiles to other CTs",
    });
    fireEvent.click(transitionToggle);
    await waitFor(() => expect(transitionToggle).toBeChecked());
    expect(fetchTacticInternals).not.toHaveBeenCalled();

    fireEvent.click(screen.getByRole("button", { name: "graph:CT1.entry" }));
    fireEvent.click(screen.getByRole("button", { name: "Expand selected node" }));

    expect(await screen.findByRole("button", {
      name: "graph:internal:step:CT1.entry:author.1",
    })).toBeVisible();
    expect(fetchTacticInternals).toHaveBeenCalledTimes(1);
    expect(transitionToggle).not.toBeChecked();
    expect(transitionToggle).toBeDisabled();

    fireEvent.click(screen.getByRole("button", { name: "Return to overview" }));
    await waitFor(() => expect(transitionToggle).toBeChecked());
    expect(screen.queryByRole("button", {
      name: "graph:internal:step:CT1.entry:author.1",
    })).toBeNull();
  });
});
