import { fireEvent, render, screen } from "@testing-library/react";
import { describe, expect, it, vi } from "vitest";

import type { ExampleManuscript } from "../types";
import { ErdosProofFlowDiagram } from "./ErdosProofFlowDiagram";

vi.mock("./GraphCanvas", () => ({
  GraphCanvas: ({
    onSelect,
  }: {
    onSelect?: (selection: {
      id: string;
      group: "edge";
      data: { source: string; target: string };
    }) => void;
  }) => (
    <div data-testid="implemented-flowchart">
      <button
        type="button"
        onClick={() => onSelect?.({
          id: "proof-edge:1:1",
          group: "edge",
          data: { source: "proof-node:1", target: "proof-node:2" },
        })}
      >
        Select test edge
      </button>
    </div>
  ),
}));

const manuscript: ExampleManuscript = {
  title: "Erdős–Gyárfás",
  path: "original_erdos_64_proof.tex",
  sha256: "a".repeat(64),
  fragments: [],
  formalizedNodeIds: [],
  nodeObligations: [],
  coverage: {
    implementedSteps: 0,
    totalSteps: 0,
    explainedDeclarations: 0,
    displayedDeclarations: 0,
    verifiedMathematicalObjects: 0,
    totalMathematicalObjects: 0,
    verifiedDiagramNodes: 0,
    totalDiagramNodes: 157,
    verifiedWorkflowSteps: 0,
  },
  proofSteps: [],
};

describe("ErdosProofFlowDiagram views", () => {
  it("switches between implemented, paper, and side-by-side comparison views", () => {
    render(
      <ErdosProofFlowDiagram
        manuscript={manuscript}
        activeNodeId={null}
        onNodeSelect={vi.fn()}
      />,
    );

    expect(screen.getByTestId("implemented-flowchart")).toBeVisible();
    fireEvent.click(screen.getByRole("button", { name: "Original paper" }));

    const paperDiagram = screen.getByRole("img", {
      name: "Original reference-paper proof-dependency diagram, Part I",
    });
    expect(paperDiagram).toHaveAttribute("src", "/assets/erdos-original/part-1.svg");

    fireEvent.click(screen.getByRole("button", { name: /Part X 0\/20 formalized/ }));
    expect(screen.getByRole("img", {
      name: "Original reference-paper proof-dependency diagram, Part X",
    })).toHaveAttribute("src", "/assets/erdos-original/part-10.svg");

    fireEvent.click(screen.getByRole("button", { name: "Implemented flowchart" }));
    expect(screen.getByTestId("implemented-flowchart")).toBeVisible();

    fireEvent.click(screen.getByRole("button", { name: "Compare side by side" }));
    expect(screen.getByTestId("implemented-flowchart")).toBeVisible();
    expect(screen.getByRole("img", {
      name: "Original reference-paper proof-dependency diagram, Part X",
    })).toBeVisible();
    expect(screen.getByRole("complementary", { name: "Selected paper node" }))
      .toHaveTextContent("Select a numbered node");
  });

  it("identifies the selected original-paper node in compare view", () => {
    render(
      <ErdosProofFlowDiagram
        manuscript={manuscript}
        activeNodeId={1}
        onNodeSelect={vi.fn()}
        defaultView="compare"
      />,
    );

    expect(screen.getByRole("complementary", { name: "Selected paper node" }))
      .toHaveTextContent("[1] finite simple graph G");
    expect(screen.getByRole("img", {
      name: "Original reference-paper proof-dependency diagram, Part I",
    })).toBeVisible();
  });

  it("reports proof-edge endpoint node numbers without treating the edge as a node", () => {
    const onNodeSelect = vi.fn();
    const onEdgeSelect = vi.fn();
    render(
      <ErdosProofFlowDiagram
        manuscript={manuscript}
        activeNodeId={null}
        onNodeSelect={onNodeSelect}
        onEdgeSelect={onEdgeSelect}
      />,
    );

    fireEvent.click(screen.getByRole("button", { name: "Select test edge" }));

    expect(onEdgeSelect).toHaveBeenCalledWith(1, 2);
    expect(onNodeSelect).not.toHaveBeenCalled();
  });

  it("can suppress the legacy node detail panel for an external inspector", () => {
    render(
      <ErdosProofFlowDiagram
        manuscript={manuscript}
        activeNodeId={1}
        onNodeSelect={vi.fn()}
        showSelectionDetails={false}
      />,
    );

    expect(screen.queryByLabelText("Original-paper obligation ledger")).not.toBeInTheDocument();
  });
});
