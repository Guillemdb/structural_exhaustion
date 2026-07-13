import { fireEvent, render, screen, waitFor, within } from "@testing-library/react";
import { MemoryRouter, Route, Routes } from "react-router-dom";
import { describe, expect, it, vi } from "vitest";

import { fetchExample } from "../api";
import type { ExampleResponse, GraphElement, SelectedGraphElement } from "../types";
import { ExamplePage } from "./ExamplePage";

vi.mock("../api", () => ({ fetchExample: vi.fn() }));
vi.mock("../components/GraphCanvas", () => ({
  GraphCanvas: ({
    elements,
    onSelect,
  }: {
    elements: GraphElement[];
    onSelect?: (selection: SelectedGraphElement) => void;
  }) => (
    <div aria-label="Mock composition graph">
      {elements.map((element) => {
        const isEdge = Boolean(element.data.source);
        return (
          <button
            type="button"
            key={element.data.id}
            onClick={() => onSelect?.({
              id: element.data.id,
              group: isEdge ? "edge" : "node",
              data: element.data,
            })}
          >
            graph:{element.data.id}
          </button>
        );
      })}
    </div>
  ),
}));

const source = [
  "namespace Example",
  "def problem := 1",
  "",
  "def ct6Run := problem",
  "theorem ct6Trace : True := by trivial",
  "",
  "def auditProblem := 2",
  "def ct2Run := auditProblem",
  "theorem auditTrace : True := by trivial",
  "end Example",
].join("\n");

function declaration(
  declarationId: string,
  name: string,
  startLine: number,
  endLine = startLine,
) {
  return {
    declarationId,
    name,
    kind: name.includes("Trace") ? "theorem" : "definition",
    type: "Nat",
    sourceId: "example-source",
    startLine,
    startColumn: 1,
    endLine,
    endColumn: 20,
    selectionStartLine: startLine,
    selectionStartColumn: 5,
    selectionEndLine: startLine,
    selectionEndColumn: 12,
  };
}

const response: ExampleResponse = {
  artifactType: "frameworkExplorerExample",
  catalogHash: "example-catalog",
  frameworkCatalogHash: "framework-catalog",
  verification: {
    state: "verified",
    reportedStatus: "passed",
    exampleCatalogHash: "example-catalog",
    verificationExampleCatalogHash: "example-catalog",
    message: "Fresh.",
  },
  tactics: [],
  example: {
    artifactType: "structuralExhaustionExample",
    schemaVersion: "1.1.0",
    sourceOfTruth: {
      kind: "compiledLeanEnvironment",
      rootModule: "Examples.EvenCycle",
      descriptor: "Examples.EvenCycle.descriptor",
    },
    exampleId: "even-cycle",
    title: "Even cycle",
    summary: "A complete example with an auxiliary audit.",
    proofStatus: "complete",
    tacticIds: ["CT6", "CT9", "CT2"],
    workflows: [
      {
        workflowId: "main",
        title: "Main proof",
        summary: "The primary proof route.",
        purpose: "Construct and validate a cycle.",
        completion: "complete",
        stages: [
          {
            stageId: "ct6-stage",
            title: "Activity search",
            summary: "Runs the CT6 machine.",
            kind: "tactic",
            tacticId: "CT6",
            primaryDeclarationId: "ct6-run",
            evidenceDeclarationIds: ["ct6-trace"],
          },
          {
            stageId: "ct9-stage",
            title: "Overload",
            summary: "Consumes the active ledger.",
            kind: "tactic",
            tacticId: "CT9",
            primaryDeclarationId: "ct6-trace",
            evidenceDeclarationIds: [],
          },
        ],
        links: [
          {
            linkId: "registered-link",
            sourceStageId: "ct6-stage",
            targetStageId: "ct9-stage",
            kind: "registeredRoute",
            label: "Active-ledger route",
            summary: "The generated registered route.",
            routeId: "CT6.residual.activeLedger->CT9",
            evidenceDeclarationIds: ["ct6-trace"],
          },
        ],
      },
      {
        workflowId: "audit",
        title: "Audit track",
        summary: "An independent audit.",
        purpose: "Audit deletion criticality independently.",
        completion: "complete",
        stages: [
          {
            stageId: "ct2-stage",
            title: "Deletion audit",
            summary: "Runs CT2 without claiming a pipeline edge.",
            kind: "tactic",
            tacticId: "CT2",
            primaryDeclarationId: "ct2-run",
            evidenceDeclarationIds: ["audit-trace"],
          },
        ],
        links: [],
      },
    ],
    interfaceBindings: [
      {
        bindingId: "ct6-binding",
        workflowId: "main",
        stageId: "ct6-stage",
        tacticId: "CT6",
        role: "Execution input",
        summary: "Connects the example input to CT6.",
        problemDeclarationId: "problem",
        frameworkDeclarationId: "ct6-run",
      },
    ],
    manuscript: {
      title: "Synthetic proof",
      path: "proofs/synthetic.tex",
      coverage: {
        implementedSteps: 3,
        totalSteps: 3,
        explainedDeclarations: 5,
        displayedDeclarations: 5,
      },
      proofSteps: [
        {
          stepId: "proof.activity",
          stageId: "ct6-stage",
          title: "Activity theorem",
          plainExplanation: "The activity search constructs the exact active ledger.",
          formalStatement: "A = A",
          status: "implemented",
          correspondence: "exact",
          manuscriptRefs: [{ label: "lem:activity", title: "Activity", nodeIds: [1] }],
          declarationGroups: [
            {
              groupId: "activity-declarations",
              title: "Activity declarations",
              role: "tacticExecution",
              explanation: "These declarations run CT6 and prove its trace.",
              declarationIds: ["problem", "ct6-run", "ct6-trace"],
            },
          ],
          scopeNotes: "This exactly covers the synthetic activity lemma.",
          workBound: "One finite scan.",
        },
        {
          stepId: "proof.overload",
          stageId: "ct9-stage",
          title: "Overload theorem",
          plainExplanation: "The overload stage consumes the active ledger.",
          formalStatement: "B = B",
          status: "implemented",
          correspondence: "composite",
          manuscriptRefs: [{ label: "lem:overload", title: "Overload", nodeIds: [2] }],
          declarationGroups: [
            {
              groupId: "overload-declarations",
              title: "Overload declarations",
              role: "semanticTheorem",
              explanation: "The CT6 trace is the displayed evidence for this fixture stage.",
              declarationIds: ["ct6-trace"],
            },
          ],
          scopeNotes: "Synthetic composite correspondence.",
          workBound: "No additional scan.",
        },
        {
          stepId: "proof.audit",
          stageId: "ct2-stage",
          title: "Deletion theorem",
          plainExplanation: "The audit verifies deletion criticality.",
          formalStatement: "C = C",
          status: "implemented",
          correspondence: "support",
          manuscriptRefs: [],
          declarationGroups: [
            {
              groupId: "audit-declarations",
              title: "Audit declarations",
              role: "executionAudit",
              explanation: "These declarations run and audit the independent CT2 execution.",
              declarationIds: ["ct2-run", "audit-trace"],
            },
          ],
          scopeNotes: "Implementation support only.",
          workBound: "One audit.",
        },
      ],
    },
    declarations: [
      declaration("problem", "Example.problem", 2),
      declaration("ct6-run", "Example.ct6Run", 4),
      declaration("ct6-trace", "Example.ct6Trace", 5),
      declaration("ct2-run", "Example.ct2Run", 8),
      declaration("audit-trace", "Example.auditTrace", 9),
    ],
    sources: [
      {
        sourceId: "example-source",
        moduleName: "Examples.EvenCycle.Concrete",
        path: "EvenCycle/Concrete.lean",
        sha256: "a".repeat(64),
        content: source,
      },
    ],
  },
};

describe("ExamplePage", () => {
  it("switches workflows, connects stages to source, explains edges, and links to CT machines", async () => {
    vi.mocked(fetchExample).mockResolvedValue(response);
    render(
      <MemoryRouter initialEntries={["/examples/even-cycle"]}>
        <Routes><Route path="/examples/:exampleId" element={<ExamplePage />} /></Routes>
      </MemoryRouter>,
    );

    expect(await screen.findByRole("heading", { name: "Activity search" })).toBeVisible();
    expect(screen.getByText("The activity search constructs the exact active ledger.")).toBeVisible();
    expect(screen.getByText("Tactic execution")).toBeVisible();
    expect(screen.getByText("5/5 displayed declarations explained")).toBeVisible();
    expect(screen.getByRole("link", { name: /Open CT6 machine/ })).toHaveAttribute("href", "/ct/CT6");
    expect(screen.getAllByText("Example.ct6Run").length).toBeGreaterThan(0);
    expect(document.querySelector('[data-line="4"]')).toHaveClass("source-line--highlighted");

    fireEvent.click(screen.getByRole("button", { name: "graph:ct9-stage" }));
    expect(screen.getByRole("heading", { name: "Overload" })).toBeVisible();
    expect(screen.getByRole("link", { name: /Open CT9 machine/ })).toHaveAttribute("href", "/ct/CT9");
    expect(document.querySelector('[data-line="5"]')).toHaveClass("source-line--highlighted");

    fireEvent.click(screen.getByRole("button", { name: "graph:registered-link" }));
    expect(screen.getByRole("heading", { name: "Active-ledger route" })).toBeVisible();
    expect(screen.getByText(/route registered and checked/)).toBeVisible();
    expect(screen.getByText("CT6.residual.activeLedger->CT9")).toBeVisible();

    fireEvent.click(screen.getByRole("button", { name: /Deletion theorem/ }));
    expect(await screen.findByRole("heading", { name: "Deletion audit" })).toBeVisible();
    expect(screen.getByText("The audit verifies deletion criticality.")).toBeVisible();
    await waitFor(() => {
      expect(document.querySelector('[data-line="8"]')).toHaveClass("source-line--highlighted");
    });

    fireEvent.click(screen.getByRole("button", { name: /Main proof/ }));
    expect(await screen.findByRole("heading", { name: "Activity search" })).toBeVisible();

    fireEvent.click(screen.getByRole("button", { name: /Audit track/ }));
    expect(await screen.findByRole("heading", { name: "Deletion audit" })).toBeVisible();
    expect(screen.getByRole("link", { name: /Open CT2 machine/ })).toHaveAttribute("href", "/ct/CT2");
    await waitFor(() => {
      expect(document.querySelector('[data-line="8"]')).toHaveClass("source-line--highlighted");
    });

    const sourceViewer = screen.getByRole("region", { name: "Examples.EvenCycle.Concrete source" });
    expect(within(sourceViewer).getByText("def ct2Run := auditProblem")).toBeVisible();

    fireEvent.click(screen.getByRole("button", { name: "Full file" }));
    expect(within(sourceViewer).getByText("end Example")).toBeVisible();
  });
});
