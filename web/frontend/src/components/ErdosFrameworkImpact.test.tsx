import { fireEvent, render, screen, within } from "@testing-library/react";
import { describe, expect, it, vi } from "vitest";

import type { ExampleResponse, ExampleStage, ExampleWorkflow } from "../types";
import { ErdosFrameworkImpact, type ErdosImpactTour } from "./ErdosFrameworkImpact";

const authorStage: ExampleStage = {
  stageId: "slice.author",
  title: "Define the graph coordinates",
  kind: "problem",
  summary: "Problem-specific finite data.",
  primaryDeclarationId: "Problem.input",
  evidenceDeclarationIds: [],
};

const frameworkStage: ExampleStage = {
  stageId: "slice.ct15",
  title: "Run target-relative rank",
  kind: "tactic",
  summary: "Execute CT15.",
  tacticId: "CT15",
  primaryDeclarationId: "Problem.run",
  evidenceDeclarationIds: [],
};

const workflow: ExampleWorkflow = {
  workflowId: "slice",
  title: "Rank split",
  purpose: "Split at a first rank drop.",
  summary: "A synthetic verified slice.",
  completion: "partial",
  stages: [authorStage, frameworkStage],
  links: [{
    linkId: "slice.transition",
    sourceStageId: authorStage.stageId,
    targetStageId: frameworkStage.stageId,
    kind: "registeredTransition",
    label: "Typed transition",
    summary: "Move the residual into CT15.",
    transitionProfileId: "CT14ToCT15",
    automationDeclarationIds: ["Framework.execute", "Framework.sound"],
    evidenceDeclarationIds: [],
  }],
};

const response = {
  example: {
    workflows: [workflow],
    interfaceBindings: [{
      bindingId: "slice.binding",
      workflowId: workflow.workflowId,
      stageId: frameworkStage.stageId,
      tacticId: "CT15",
      role: "Rank coordinates",
      summary: "Supply the concrete coordinates to the reusable profile.",
      problemDeclarationId: "Problem.input",
      frameworkDeclarationId: "Framework.profile",
    }],
  },
} as ExampleResponse;

const tours: ErdosImpactTour[] = [{
  tourId: "rank-tour",
  title: "From coordinates to an exhaustive rank split",
  summary: "See the boundary between proof-specific semantics and reusable search.",
  stageIds: [authorStage.stageId, frameworkStage.stageId],
  authorSupplied: "The finite coordinates and target response.",
  frameworkSupplied: "The rank scan, residual split, and soundness theorem.",
  verifiedOutcome: "Either a first rank drop or a full-rank ledger.",
  tacticIds: ["CT15"],
}];

describe("ErdosFrameworkImpact", () => {
  it("shows auditable reuse metrics without presenting them as time saved", () => {
    render(<ErdosFrameworkImpact response={response} tours={tours} selectedNodeId={31} />);

    expect(screen.getByText(/evidence of reuse, not a percentage of the proof automated/i)).toBeVisible();
    expect(screen.getByText("Paper node [31] selected")).toBeVisible();

    const transitions = screen.getByText("Framework-backed transitions").parentElement;
    const registeredProfiles = screen.getByText("Registered transition profiles").parentElement;
    const declarations = screen.getByText("Framework declarations reused").parentElement;
    expect(within(registeredProfiles!).getByText("1")).toBeVisible();
    expect(within(transitions!).getByText("1")).toBeVisible();
    expect(within(declarations!).getByText("3")).toBeVisible();
  });

  it("exposes guided tours and their exact stages to the workspace", () => {
    const onTourSelect = vi.fn();
    const onStageSelect = vi.fn();
    render(
      <ErdosFrameworkImpact
        response={response}
        tours={tours}
        activeTourId="rank-tour"
        onTourSelect={onTourSelect}
        onStageSelect={onStageSelect}
      />,
    );

    fireEvent.click(screen.getByRole("button", { name: "Explore this slice" }));
    expect(onTourSelect).toHaveBeenCalledWith("rank-tour");

    fireEvent.click(screen.getByRole("button", { name: /Run target-relative rank/ }));
    expect(onStageSelect).toHaveBeenCalledWith(frameworkStage, workflow);
    expect(screen.getByText("The rank scan, residual split, and soundness theorem.")).toBeVisible();
  });
});
