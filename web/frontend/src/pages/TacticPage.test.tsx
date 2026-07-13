import { fireEvent, render, screen } from "@testing-library/react";
import { MemoryRouter, Route, Routes, useLocation } from "react-router-dom";
import { beforeEach, describe, expect, it, vi } from "vitest";

import { fetchFramework, fetchTactic } from "../api";
import type {
  FrameworkResponse,
  GraphElement,
  SelectedGraphElement,
  TacticResponse,
} from "../types";
import { TacticPage } from "./TacticPage";

vi.mock("../api", () => ({ fetchFramework: vi.fn(), fetchTactic: vi.fn() }));
vi.mock("../components/AppHeader", () => ({ AppHeader: () => null }));
vi.mock("../components/Inspector", () => ({ Inspector: () => null }));
vi.mock("../components/RouteList", () => ({ RouteList: () => null }));
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

const route = {
  routeId: "CT1.residual.avoiding->CT2",
  sourceTacticId: "CT1",
  sourceResidualKind: "CT1.residual.avoiding",
  targetTacticId: "CT2",
};

const tacticResponse = {
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
  inboundRoutes: [],
  outboundRoutes: [route],
} as unknown as TacticResponse;

const frameworkResponse = {
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

describe("TacticPage route overlay", () => {
  beforeEach(() => {
    vi.clearAllMocks();
    vi.mocked(fetchTactic).mockResolvedValue(tacticResponse);
    vi.mocked(fetchFramework).mockResolvedValue(frameworkResponse);
  });

  it("toggles outbound routes and opens a destination CT node", async () => {
    render(
      <MemoryRouter initialEntries={["/ct/CT1"]}>
        <Routes>
          <Route path="/ct/:tacticId" element={<TacticPage />} />
        </Routes>
        <LocationProbe />
      </MemoryRouter>,
    );

    const toggle = await screen.findByRole("checkbox", { name: "Show routes to other CTs" });
    expect(toggle).not.toBeChecked();
    expect(screen.queryByRole("button", { name: "graph:route-target:CT2" })).toBeNull();

    fireEvent.click(toggle);
    expect(toggle).toBeChecked();
    expect(screen.getByRole("button", { name: "graph:CT1.residual.avoiding->CT2" })).toBeVisible();

    fireEvent.click(screen.getByRole("button", { name: "graph:route-target:CT2" }));
    expect(screen.getByRole("status", { name: "Current location" })).toHaveTextContent("/ct/CT2");
  });
});
