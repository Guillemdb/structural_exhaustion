import { fireEvent, render, screen } from "@testing-library/react";
import { describe, expect, it, vi } from "vitest";

import type { SelectedGraphElement, TacticInternalsResponse } from "../types";
import { NodeInternalsInspector } from "./NodeInternalsInspector";

describe("NodeInternalsInspector", () => {
  it("shows plain language, formal math, exact Lean, source, and dependencies", () => {
    const declarationId = "StructuralExhaustion.CT1.Capability.Target";
    const response = {
      internals: {
        nodes: [{
          nodeId: "CT1.entry",
          internalFlow: {
            nodeId: "CT1.entry",
            steps: [{
              stepId: "author.1",
              role: "authorObject",
              reference: { ref: declarationId, provision: "user_definition" },
              plainExplanation: "This predicate says that the desired target occurs.",
              mathematicalDefinition: "T(G) \\iff G \\text{ contains the target}",
              label: "Target predicate",
              declarationId,
            }],
            edges: [],
          },
        }],
        declarations: [{
          declarationId,
          name: declarationId,
          kind: "definition",
          type: "{P : Core.Problem} → Capability P → P.Ambient → Prop",
          docString: "The target predicate.",
          module: "StructuralExhaustion.CT1.Capability",
          sourceFile: "StructuralExhaustion/CT1/Capability.lean",
          range: {
            start: { line: 1, column: 0 },
            end: { line: 1, column: 28 },
          },
          selectionRange: null,
          bodyAvailable: true,
          typeDependencies: ["StructuralExhaustion.Core.Problem"],
          bodyDependencies: ["StructuralExhaustion.CT1.Spec"],
          projectLocal: true,
          sourceId: "StructuralExhaustion/CT1/Capability.lean",
        }],
        sources: [{
          sourceId: "StructuralExhaustion/CT1/Capability.lean",
          moduleName: "StructuralExhaustion.CT1.Capability",
          path: "lean/StructuralExhaustion/CT1/Capability.lean",
          sha256: "a".repeat(64),
          content: "namespace StructuralExhaustion.CT1\ndef Target := fun G => True\nend StructuralExhaustion.CT1\n",
        }],
      },
    } as unknown as TacticInternalsResponse;
    const selected = {
      id: "internal:step:CT1.entry:author.1",
      group: "node",
      data: {
        id: "internal:step:CT1.entry:author.1",
        internalKind: "step",
        stepId: "author.1",
        declarationId,
      },
    } satisfies SelectedGraphElement;
    const onExpand = vi.fn();

    render(
      <NodeInternalsInspector
        nodeId="CT1.entry"
        selected={selected}
        response={response}
        expandedDeclarations={new Set()}
        onExpandDeclaration={onExpand}
      />,
    );

    expect(screen.getByText("This predicate says that the desired target occurs.")).toBeVisible();
    expect(screen.getByLabelText("Formal mathematical meaning of Target predicate")).toBeVisible();
    expect(screen.getByText(response.internals.declarations[0].type)).toBeVisible();
    expect(screen.getByText("StructuralExhaustion.Core.Problem")).toBeVisible();
    expect(screen.getByLabelText(`Lean source for ${declarationId}`)).toHaveTextContent(
      "def Target := fun G => True",
    );
    fireEvent.click(screen.getByRole("button", { name: "Show 2 direct dependencies" }));
    expect(onExpand).toHaveBeenCalledWith(declarationId);
  });
});
