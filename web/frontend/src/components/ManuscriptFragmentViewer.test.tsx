import { fireEvent, render, screen, within } from "@testing-library/react";
import { describe, expect, it } from "vitest";

import type { ExampleManuscript, ExampleProofStep } from "../types";
import { ManuscriptFragmentViewer } from "./ManuscriptFragmentViewer";

const svg = '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 10 10"><path d="M0 0L10 10"/></svg>';

const manuscript: ExampleManuscript = {
  title: "Synthetic paper",
  path: "proofs/synthetic.tex",
  sha256: "a".repeat(64),
  formalizedNodeIds: [],
  proofSteps: [],
  fragments: [
    {
      label: "lem:first",
      environment: "lemma",
      sourceLine: 10,
      includesProof: true,
      contentSha256: "b".repeat(64),
      blocks: [{
        kind: "environment",
        environment: "lemma",
        label: "lem:first",
        title: [{ kind: "text", text: "First exact lemma" }],
        blocks: [{
          kind: "paragraph",
          inlines: [
            { kind: "text", text: "For " },
            { kind: "math", display: false, tex: "x=1" },
            { kind: "text", text: ", use " },
            {
              kind: "reference",
              labels: ["def:second"],
              referenceKind: "definition",
              prefix: "Definition",
              text: "2",
            },
            { kind: "text", text: "." },
          ],
        }],
      }],
    },
    {
      label: "def:second",
      environment: "definition",
      sourceLine: 22,
      includesProof: false,
      contentSha256: "c".repeat(64),
      blocks: [{
        kind: "figure",
        label: "fig:second",
        svg,
        svgSha256: "d".repeat(64),
        caption: [{
          kind: "paragraph",
          inlines: [{ kind: "text", text: "The exact finite configuration." }],
        }],
      }],
    },
  ],
  coverage: {
    implementedSteps: 1,
    totalSteps: 1,
    explainedDeclarations: 1,
    displayedDeclarations: 1,
    verifiedMathematicalObjects: 2,
    totalMathematicalObjects: 2,
    verifiedDiagramNodes: 2,
    totalDiagramNodes: 2,
    verifiedWorkflowSteps: 1,
  },
};

const proofStep: ExampleProofStep = {
  stepId: "proof.synthetic",
  title: "Synthetic step",
  plainExplanation: "Synthetic.",
  formalStatement: "x=x",
  status: "implemented",
  correspondence: "exact",
  manuscriptRefs: [
    { label: "lem:first", title: "First lemma", nodeIds: [1] },
    { label: "def:second", title: "Second definition", nodeIds: [2] },
  ],
  declarationGroups: [],
  scopeNotes: "Synthetic.",
  workBound: "Constant.",
};

describe("ManuscriptFragmentViewer", () => {
  it("renders mathematical prose, references, tabs, and checked SVG figures", () => {
    render(<ManuscriptFragmentViewer manuscript={manuscript} proofStep={proofStep} />);

    const fragment = screen.getByRole("region", { name: "Rendered manuscript fragment" });
    expect(within(fragment).getByLabelText("Inline manuscript equation")).toBeVisible();
    expect(within(fragment).getByText("First exact lemma")).toBeVisible();
    expect(within(fragment).getByText("Definition 2")).toHaveAttribute("data-labels", "def:second");

    fireEvent.click(screen.getByRole("button", { name: /Second definition.*def:second/ }));
    const image = within(fragment).getByRole("img", { name: "fig:second manuscript diagram" });
    expect(image).toHaveAttribute("src", expect.stringContaining("data:image/svg+xml"));
    expect(within(fragment).getByText("The exact finite configuration.")).toBeVisible();
  });
});
