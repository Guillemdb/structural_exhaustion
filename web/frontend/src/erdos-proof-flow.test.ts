import { readFileSync } from "node:fs";
import { resolve } from "node:path";

import { describe, expect, it } from "vitest";

import {
  ERDOS_PROOF_FLOW_NODES,
  ERDOS_PROOF_FLOW_PARTS,
  erdosProofFlowElements,
  proofFlowNodeElementId,
  proofFlowNodeNumber,
  proofFlowNodeStatuses,
} from "./erdos-proof-flow";
import type { ExampleDetail, ExampleManuscript } from "./types";

function manuscriptWithStatuses(): ExampleManuscript {
  return {
    title: "Synthetic proof",
    path: "proofs/synthetic.tex",
    sha256: "a".repeat(64),
    fragments: [],
    coverage: {
      implementedSteps: 1,
      totalSteps: 3,
      explainedDeclarations: 0,
      displayedDeclarations: 0,
      verifiedMathematicalObjects: 0,
      totalMathematicalObjects: 1,
      verifiedDiagramNodes: 2,
      totalDiagramNodes: 157,
      verifiedWorkflowSteps: 1,
    },
    proofSteps: [
      {
        stepId: "paper",
        title: "Paper only",
        plainExplanation: "Paper only.",
        formalStatement: "Paper only.",
        status: "notStarted",
        correspondence: "partial",
        manuscriptRefs: [{ label: "paper", title: "Paper", nodeIds: [2, 19] }],
        declarationGroups: [],
        scopeNotes: "None.",
        workBound: "None.",
      },
      {
        stepId: "next",
        title: "Next",
        plainExplanation: "Next.",
        formalStatement: "Next.",
        status: "next",
        correspondence: "partial",
        manuscriptRefs: [{ label: "next", title: "Next", nodeIds: [19] }],
        declarationGroups: [],
        scopeNotes: "None.",
        workBound: "None.",
      },
      {
        stepId: "implemented",
        stageId: "stage",
        title: "Implemented",
        plainExplanation: "Implemented.",
        formalStatement: "Implemented.",
        status: "implemented",
        correspondence: "exact",
        manuscriptRefs: [{ label: "implemented", title: "Implemented", nodeIds: [1, 2] }],
        declarationGroups: [],
        scopeNotes: "None.",
        workBound: "Finite.",
      },
    ],
  };
}

describe("Erdős Chapter 1 proof flow", () => {
  it("contains all eleven paper diagrams and every numbered node exactly once", () => {
    expect(ERDOS_PROOF_FLOW_PARTS).toHaveLength(11);
    expect(ERDOS_PROOF_FLOW_NODES).toHaveLength(157);
    expect(ERDOS_PROOF_FLOW_NODES.map((node) => node.nodeId)).toEqual(
      Array.from({ length: 157 }, (_, index) => index + 1),
    );

    const allNodeIds = new Set(ERDOS_PROOF_FLOW_NODES.map((node) => node.nodeId));
    for (const part of ERDOS_PROOF_FLOW_PARTS) {
      const localNodeIds = new Set(part.nodes.map((node) => node.nodeId));
      for (const edge of part.edges) {
        expect(localNodeIds.has(edge.source)).toBe(true);
        expect(localNodeIds.has(edge.target)).toBe(true);
      }
      for (const continuation of part.continuations) {
        expect(localNodeIds.has(continuation.source)).toBe(true);
        expect(allNodeIds.has(continuation.target)).toBe(true);
      }
    }
  });

  it("derives green and frontier states from manuscript-indexed proof steps", () => {
    const manuscript = manuscriptWithStatuses();
    const statuses = proofFlowNodeStatuses(manuscript);
    expect(statuses.get(1)).toBe("implemented");
    expect(statuses.get(2)).toBe("implemented");
    expect(statuses.get(19)).toBe("next");

    const elements = erdosProofFlowElements(ERDOS_PROOF_FLOW_PARTS[0], manuscript);
    expect(elements.find((element) => element.data.id === "proof-node:1")?.data).toMatchObject({
      proofNodeId: 1,
      verified: true,
      status: "implemented",
    });
    expect(elements.find((element) => element.data.id === "proof-node:19")?.data).toMatchObject({
      verified: false,
      status: "next",
    });
  });

  it("round-trips proof node element IDs", () => {
    expect(proofFlowNodeElementId(157)).toBe("proof-node:157");
    expect(proofFlowNodeNumber("proof-node:157")).toBe(157);
    expect(proofFlowNodeNumber("proof-edge:1:1")).toBeNull();
  });

  it("matches the generated manuscript totals and current verified-node count", () => {
    const detail = JSON.parse(readFileSync(
      resolve(process.cwd(), "../../generated/examples/erdos-64.json"),
      "utf8",
    )) as ExampleDetail;
    expect(detail.manuscript).not.toBeNull();
    if (!detail.manuscript) return;

    const statuses = proofFlowNodeStatuses(detail.manuscript);
    const verified = ERDOS_PROOF_FLOW_NODES.filter(
      (node) => statuses.get(node.nodeId) === "implemented",
    );
    expect(ERDOS_PROOF_FLOW_NODES).toHaveLength(
      detail.manuscript.coverage.totalDiagramNodes,
    );
    expect(verified).toHaveLength(
      detail.manuscript.coverage.verifiedDiagramNodes,
    );
  });
});
