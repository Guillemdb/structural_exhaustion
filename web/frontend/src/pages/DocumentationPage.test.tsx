import { fireEvent, render, screen } from "@testing-library/react";
import { MemoryRouter } from "react-router-dom";
import { beforeEach, describe, expect, it, vi } from "vitest";

import { fetchDocumentation } from "../api";
import { AudienceProvider } from "../audience";
import type { DocumentationResponse } from "../types";
import { CoreDocumentationPage, GraphDocumentationPage } from "./DocumentationPage";

vi.mock("../api", () => ({ fetchDocumentation: vi.fn() }));

const response = {
  artifactWarnings: [],
  schemaVersion: "1.0.0",
  catalogHash: "1234567890abcdef",
  sourceOfTruth: { kind: "compiledLeanEnvironment" },
  verification: { state: "verified", message: "Fresh" },
  capabilities: [
    {
      capabilityId: "core.problem-context",
      layer: "core",
      category: "Model the branch",
      title: "Problems and branch contexts",
      depth: "walkthrough",
      mathematician: {
        summary: "Mathematical branch summary.",
        inputs: "An object and baseline.",
        result: "A stable branch context.",
      },
      leanUser: {
        summary: "Lean branch summary.",
        inputs: "Define Core.Problem.",
        result: "Indexed CT contexts.",
      },
      declarations: ["StructuralExhaustion.Core.Problem"],
      relatedTacticIds: ["CT1"],
      relatedCapabilityIds: [],
      examples: [],
    },
    {
      capabilityId: "graph.greedy-coloring",
      layer: "graph",
      category: "Packing and construction",
      title: "Verified greedy coloring",
      depth: "walkthrough",
      mathematician: {
        summary: "Color vertices in reverse order.",
        inputs: "A finite graph.",
        result: "A proper coloring.",
      },
      leanUser: {
        summary: "Compose CT12, CT4, and CT1.",
        inputs: "A Graph.FiniteObject.",
        result: "A Mathlib Colorable proof.",
      },
      declarations: ["StructuralExhaustion.Graph.GreedyColoring.colorOrder"],
      relatedTacticIds: ["CT12", "CT4", "CT1"],
      relatedCapabilityIds: ["core.problem-context"],
      examples: [
        {
          exampleId: "greedy-coloring",
          workflowId: "coloring",
          title: "Deterministic greedy coloring",
          exampleTitle: "Greedy coloring",
          workflow: {
            workflowId: "coloring",
            title: "Deterministic greedy coloring",
            summary: "A verified coloring workflow.",
            purpose: "Prove coloring.",
            completion: "complete",
            links: [],
            stages: [
              {
                stageId: "coloring.ct12",
                title: "CT12 vertex-peeling audit",
                summary: "Audit the declared order.",
                kind: "tactic",
                tacticId: "CT12",
                primaryDeclarationId: "StructuralExhaustion.Graph.GreedyColoring.peelingRun",
                evidenceDeclarationIds: [],
              },
            ],
          },
        },
      ],
    },
  ],
  tacticGuides: [],
} as unknown as DocumentationResponse;

describe("audience-aware framework documentation", () => {
  beforeEach(() => {
    window.localStorage.clear();
    vi.mocked(fetchDocumentation).mockResolvedValue(response);
  });

  it("switches the Core page from mathematical content to Lean API content", async () => {
    render(<MemoryRouter><AudienceProvider><CoreDocumentationPage /></AudienceProvider></MemoryRouter>);

    expect((await screen.findAllByText("Mathematical branch summary."))[0]).toBeVisible();
    fireEvent.click(screen.getByRole("button", { name: "Lean user" }));
    expect(screen.getAllByText("Lean branch summary.")[0]).toBeVisible();
    expect(screen.getByText("StructuralExhaustion.Core.Problem")).toBeVisible();
    expect(window.localStorage.getItem("structural-exhaustion.documentation-audience")).toBe("leanUser");
  });

  it("embeds a non-Erdős Graph workflow", async () => {
    render(<MemoryRouter><AudienceProvider><GraphDocumentationPage /></AudienceProvider></MemoryRouter>);
    expect(await screen.findByRole("heading", { name: "Verified greedy coloring" })).toBeVisible();
    expect(screen.getByText("CT12 vertex-peeling audit")).toBeVisible();
    expect(screen.getByRole("link", { name: /Open full workflow/ })).toHaveAttribute(
      "href",
      "/examples/greedy-coloring",
    );
    expect(screen.getByRole("link", { name: "Problems and branch contexts" })).toHaveAttribute(
      "href",
      "/framework/core#core.problem-context",
    );
  });
});
