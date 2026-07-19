import { fireEvent, render, screen } from "@testing-library/react";
import { describe, expect, it, vi } from "vitest";

import type {
  ExampleDeclaration,
  ExampleInterfaceBinding,
  ExampleManuscript,
  ExampleNodeObligation,
  ExampleProofStep,
  ExampleStage,
} from "../types";
import { ErdosNodeStory } from "./ErdosNodeStory";

const manuscript: ExampleManuscript = {
  title: "Erdős–Gyárfás Problem 64",
  path: "proofs/erdos_64_eg/erdos_64_proof.tex",
  sha256: "a".repeat(64),
  fragments: [],
  formalizedNodeIds: [31],
  nodeObligations: [],
  proofSteps: [],
  coverage: {
    implementedSteps: 2,
    totalSteps: 2,
    explainedDeclarations: 3,
    displayedDeclarations: 3,
    verifiedMathematicalObjects: 1,
    totalMathematicalObjects: 1,
    verifiedDiagramNodes: 1,
    totalDiagramNodes: 157,
    verifiedWorkflowSteps: 2,
  },
};

const proofSteps: ExampleProofStep[] = [
  {
    stepId: "node31.coordinates",
    stageId: "node31.ct15",
    title: "Define target-relative coordinates",
    plainExplanation: "The application fixes the finite coordinates seen by the target.",
    formalStatement: "r_T(x) = k",
    status: "implemented",
    correspondence: "exact",
    manuscriptRefs: [{ label: "lem:rank", title: "Rank dichotomy", nodeIds: [31] }],
    declarationGroups: [{
      groupId: "node31.input",
      title: "Graph-specific coordinate family",
      role: "mathematicalDefinition",
      explanation: "Defines the coordinates used by this graph argument.",
      declarationIds: ["Problem.coordinates"],
    }],
    scopeNotes: "Exact for the selected paper node.",
    workBound: "The coordinate family is finite.",
  },
  {
    stepId: "node31.split",
    stageId: "node31.ct15",
    title: "Execute the rank dichotomy",
    plainExplanation: "CT15 returns the first drop or a full-rank ledger.",
    formalStatement: "drop \u2228 full",
    status: "implemented",
    correspondence: "composite",
    manuscriptRefs: [{ label: "lem:rank", title: "Rank dichotomy", nodeIds: [31] }],
    declarationGroups: [{
      groupId: "node31.execution",
      title: "Reusable exhaustive execution",
      role: "tacticExecution",
      explanation: "Runs the shared CT15 executor.",
      declarationIds: ["Problem.runCT15"],
    }],
    scopeNotes: "The residual alternatives are explicit.",
    workBound: "At most one scan of the finite coordinates.",
  },
];

const stage: ExampleStage = {
  stageId: "node31.ct15",
  title: "Node 31 CT15 execution",
  kind: "tactic",
  summary: "Instantiates the target-relative rank profile.",
  tacticId: "CT15",
  primaryDeclarationId: "Problem.runCT15",
  evidenceDeclarationIds: [],
};

const bindings: ExampleInterfaceBinding[] = [{
  bindingId: "node31.rank-profile",
  workflowId: "node31",
  stageId: stage.stageId,
  tacticId: "CT15",
  role: "Target-relative coordinates",
  summary: "Connects the graph coordinates to the reusable CT15 profile.",
  problemDeclarationId: "Problem.coordinates",
  frameworkDeclarationId: "Framework.CT15.profile",
}];

const declarations: ExampleDeclaration[] = [
  {
    declarationId: "Problem.coordinates",
    name: "Erdos64EG.rankCoordinates",
    kind: "definition",
    type: "Coordinates",
    sourceId: "source.problem",
    startLine: 10,
    startColumn: 1,
    endLine: 12,
    endColumn: 1,
    selectionStartLine: 10,
    selectionStartColumn: 1,
    selectionEndLine: 10,
    selectionEndColumn: 20,
  },
  {
    declarationId: "Problem.runCT15",
    name: "Erdos64EG.runRankSplit",
    kind: "theorem",
    type: "drop \u2228 full",
    sourceId: "source.problem",
    startLine: 20,
    startColumn: 1,
    endLine: 24,
    endColumn: 1,
    selectionStartLine: 20,
    selectionStartColumn: 1,
    selectionEndLine: 20,
    selectionEndColumn: 20,
  },
];

const obligations: ExampleNodeObligation[] = [
  {
    nodeId: 31,
    obligationId: "node31.input",
    title: "Construct the rank input",
    statement: "The target-relative coordinate input exists.",
    status: "proved",
    evidenceStepIds: ["node31.coordinates"],
  },
  {
    nodeId: 31,
    obligationId: "node31.consumer",
    title: "Consume both residuals",
    statement: "Each outgoing residual reaches its exact successor.",
    status: "partial",
    evidenceStepIds: ["node31.split"],
  },
];

describe("ErdosNodeStory", () => {
  it("renders every proof step for one node and preserves caller-owned status semantics", () => {
    render(
      <ErdosNodeStory
        nodeId={31}
        status="partial"
        isFrontier
        manuscript={manuscript}
        proofSteps={proofSteps}
        obligations={obligations}
        stages={[stage]}
        bindings={bindings}
        declarations={declarations}
      />,
    );

    expect(screen.getByText("Partially formalized")).toBeVisible();
    expect(screen.getByText("Current frontier")).toBeVisible();
    expect(screen.getByText("Define target-relative coordinates")).toBeVisible();
    expect(screen.getByText("Execute the rank dichotomy")).toBeVisible();
    expect(screen.getAllByText("lem:rank")).toHaveLength(1);
    expect(screen.getByText("Construct the rank input")).toBeVisible();
    expect(screen.getByText("Consume both residuals")).toBeVisible();
  });

  it("connects author inputs to framework interfaces and exposes navigation callbacks", () => {
    const onDeclarationSelect = vi.fn();
    const onStageSelect = vi.fn();
    render(
      <ErdosNodeStory
        nodeId={31}
        status="verified"
        manuscript={manuscript}
        proofSteps={proofSteps}
        obligations={obligations}
        stages={[stage]}
        bindings={bindings}
        declarations={declarations}
        onDeclarationSelect={onDeclarationSelect}
        onStageSelect={onStageSelect}
      />,
    );

    expect(screen.getByRole("heading", { name: "Author supplied" })).toBeVisible();
    expect(screen.getByRole("heading", { name: "Framework supplied" })).toBeVisible();
    expect(screen.getByText("Framework.CT15.profile")).toBeVisible();

    fireEvent.click(screen.getByRole("button", { name: /Node 31 CT15 execution/ }));
    expect(onStageSelect).toHaveBeenCalledWith(stage);
    fireEvent.click(screen.getByRole("button", { name: "Erdos64EG.rankCoordinates" }));
    expect(onDeclarationSelect).toHaveBeenCalledWith("Problem.coordinates");
  });

  it("shows an explicit prompt when no paper node is selected", () => {
    render(
      <ErdosNodeStory
        nodeId={null}
        status="paper"
        manuscript={manuscript}
        proofSteps={[]}
        obligations={[]}
        stages={[]}
        bindings={[]}
        declarations={[]}
      />,
    );
    expect(screen.getByRole("heading", { name: "Select a proof node" })).toBeVisible();
  });
});
