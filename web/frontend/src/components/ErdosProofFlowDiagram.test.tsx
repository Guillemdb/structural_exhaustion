import { fireEvent, render, screen } from "@testing-library/react";
import { describe, expect, it, vi } from "vitest";

import type { ExampleManuscript } from "../types";
import { ErdosProofFlowDiagram } from "./ErdosProofFlowDiagram";

vi.mock("./GraphCanvas", () => ({
  GraphCanvas: () => <div data-testid="implemented-flowchart" />,
}));

const manuscript: ExampleManuscript = {
  title: "Erdős–Gyárfás",
  path: "original_erdos_64_proof.tex",
  sha256: "a".repeat(64),
  fragments: [],
  formalizedNodeIds: [],
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
  it("switches between the implemented flowchart and the exact paper rendering", () => {
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
  });
});
