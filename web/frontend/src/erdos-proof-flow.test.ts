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
    formalizedNodeIds: [1],
    coverage: {
      implementedSteps: 1,
      totalSteps: 3,
      explainedDeclarations: 0,
      displayedDeclarations: 0,
      verifiedMathematicalObjects: 0,
      totalMathematicalObjects: 1,
      verifiedDiagramNodes: 1,
      totalDiagramNodes: 175,
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
  it("contains all eleven paper diagrams and every active node exactly once", () => {
    expect(ERDOS_PROOF_FLOW_PARTS).toHaveLength(11);
    expect(ERDOS_PROOF_FLOW_NODES).toHaveLength(194);
    expect(ERDOS_PROOF_FLOW_NODES.map((node) => node.nodeId).sort((a, b) => a - b)).toEqual(
      Array.from({ length: 195 }, (_, index) => index + 1).filter((nodeId) => nodeId !== 172),
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

  it("separates complete, partial, frontier, and paper-only node states", () => {
    const manuscript = manuscriptWithStatuses();
    const statuses = proofFlowNodeStatuses(manuscript);
    expect(statuses.get(1)).toBe("implemented");
    expect(statuses.get(2)).toBe("partial");
    expect(statuses.get(19)).toBe("next");

    const elements = erdosProofFlowElements(ERDOS_PROOF_FLOW_PARTS[0], manuscript);
    expect(elements.find((element) => element.data.id === "proof-node:1")?.data).toMatchObject({
      proofNodeId: 1,
      verified: true,
      status: "implemented",
      closure: "open",
    });
    expect(elements.find((element) => element.data.id === "proof-node:19")?.data).toMatchObject({
      verified: false,
      status: "next",
    });
    expect(elements.find((element) => element.data.id === "proof-node:2")?.data).toMatchObject({
      verified: false,
      status: "partial",
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
    expect(statuses.get(3)).toBe("implemented");
    expect(statuses.get(19)).toBe("implemented");
    expect(statuses.get(131)).toBe("implemented");
    expect(statuses.get(132)).toBe("implemented");
    expect(detail.manuscript.coverage.verifiedDiagramNodes).toBe(116);
    expect(statuses.get(158)).toBe("implemented");
    expect(statuses.get(159)).toBe("implemented");
    expect(statuses.get(155)).toBe("implemented");
    expect(statuses.get(161)).toBe("implemented");
    expect(statuses.get(162)).toBe("implemented");
    expect(statuses.get(163)).toBe("implemented");
    expect(statuses.get(160) ?? "notStarted").toBe("notStarted");
    expect(statuses.get(164)).toBe("implemented");
    expect(statuses.get(165)).toBe("implemented");
    expect(statuses.get(166)).toBe("implemented");
    expect(statuses.get(167)).toBe("implemented");
    expect(statuses.get(168)).toBe("implemented");
    expect(statuses.get(169)).toBe("implemented");
    expect(statuses.get(170)).toBe("implemented");
    expect(statuses.get(171)).toBe("implemented");
    expect(statuses.get(173)).toBe("implemented");
    expect(statuses.get(174)).toBe("implemented");
    expect(statuses.get(175)).toBe("implemented");
    expect(statuses.get(177)).toBe("implemented");
    expect(statuses.get(178)).toBe("implemented");
    expect(statuses.get(179)).toBe("implemented");
    expect(statuses.get(180)).toBe("implemented");
    expect(statuses.get(181)).toBe("implemented");
    expect(statuses.get(182)).toBe("implemented");
    expect(statuses.get(183)).toBe("implemented");
    expect(statuses.get(184)).toBe("implemented");
    expect(statuses.get(185)).toBe("implemented");
    expect(statuses.get(186)).toBe("implemented");
    expect(statuses.get(187)).toBe("implemented");
    expect(statuses.get(188)).toBe("implemented");
    expect(statuses.get(189)).toBe("implemented");
    expect(statuses.get(190)).toBe("implemented");
    expect(statuses.get(191)).toBe("implemented");
    expect(statuses.get(192)).toBe("implemented");
    expect(statuses.get(193)).toBe("implemented");
    expect(statuses.get(194)).toBe("implemented");
    expect(statuses.get(195)).toBe("implemented");
    for (const nodeId of [133, 134, 135, 136, 137, 138, 139, 141]) {
      expect(statuses.get(nodeId)).toBe("implemented");
    }
    for (const nodeId of [19, 20, 28, 75, 80, 81, 82, 83, 125, 140, 142, 143]) {
      expect(statuses.get(nodeId)).toBe("implemented");
    }
    for (const nodeId of [84, 144]) {
      expect(statuses.get(nodeId)).toBe("implemented");
    }
    for (const nodeId of [176]) {
      expect(statuses.get(nodeId)).toBe("next");
    }

    const partOneElements = erdosProofFlowElements(ERDOS_PROOF_FLOW_PARTS[0], detail.manuscript);
    expect(partOneElements.find((element) => element.data.id === "proof-node:3")?.data)
      .toMatchObject({ status: "implemented", closure: "closed" });

    const partTen = ERDOS_PROOF_FLOW_PARTS.find((part) => part.part === 10);
    expect(partTen).toBeDefined();
    if (!partTen) return;
    expect(erdosProofFlowElements(partTen, detail.manuscript)
      .find((element) => element.data.id === "proof-node:138")?.data)
      .toMatchObject({ status: "implemented", closure: "open" });
    expect(erdosProofFlowElements(partTen, detail.manuscript)
      .find((element) => element.data.id === "proof-node:193")?.data)
      .toMatchObject({ status: "implemented", closure: "open" });
    const partEleven = ERDOS_PROOF_FLOW_PARTS.find((part) => part.part === 11);
    expect(partEleven).toBeDefined();
    if (!partEleven) return;
    for (const nodeId of [194, 195]) {
      expect(erdosProofFlowElements(partEleven, detail.manuscript)
        .find((element) => element.data.id === `proof-node:${nodeId}`)?.data)
        .toMatchObject({ status: "implemented", closure: "open" });
    }
  });

  it("keeps every exported proof-slice stage reachable from node 1", () => {
    const detail = JSON.parse(readFileSync(
      resolve(process.cwd(), "../../generated/examples/erdos-64.json"),
      "utf8",
    )) as ExampleDetail;
    const workflow = detail.workflows.find(({ workflowId }) => workflowId === "proof-slice");
    expect(workflow).toBeDefined();
    if (!workflow) return;

    const successors = new Map<string, string[]>();
    for (const link of workflow.links) {
      const targets = successors.get(link.sourceStageId) ?? [];
      targets.push(link.targetStageId);
      successors.set(link.sourceStageId, targets);
    }
    const reachable = new Set<string>(["proof-slice.official"]);
    const queue = ["proof-slice.official"];
    for (let index = 0; index < queue.length; index += 1) {
      for (const target of successors.get(queue[index]) ?? []) {
        if (reachable.has(target)) continue;
        reachable.add(target);
        queue.push(target);
      }
    }

    expect(workflow.stages.filter(({ stageId }) => !reachable.has(stageId))).toEqual([]);
  });

  it("reports exactly the current partially formalized nodes", () => {
    const detail = JSON.parse(readFileSync(
      resolve(process.cwd(), "../../generated/examples/erdos-64.json"),
      "utf8",
    )) as ExampleDetail;
    expect(detail.manuscript).not.toBeNull();
    if (!detail.manuscript) return;

    const statuses = proofFlowNodeStatuses(detail.manuscript);
    const partialNodeIds = [...statuses.entries()]
      .filter(([, status]) => status === "partial")
      .map(([nodeId]) => nodeId)
      .sort((left, right) => left - right);
    expect(partialNodeIds).toEqual([]);
    expect(statuses.get(3)).toBe("implemented");
    expect(statuses.get(22) ?? "notStarted").toBe("notStarted");
    expect(statuses.get(64) ?? "notStarted").toBe("notStarted");
    expect(statuses.get(65) ?? "notStarted").toBe("notStarted");
    expect(statuses.get(66) ?? "notStarted").toBe("notStarted");
  });

  it("renders the current Part II split as verified then paper-only", () => {
    const detail = JSON.parse(readFileSync(
      resolve(process.cwd(), "../../generated/examples/erdos-64.json"),
      "utf8",
    )) as ExampleDetail;
    expect(detail.manuscript).not.toBeNull();
    if (!detail.manuscript) return;

    const part = ERDOS_PROOF_FLOW_PARTS.find((candidate) => candidate.part === 2);
    expect(part).toBeDefined();
    if (!part) return;
    const nodeStatuses = Object.fromEntries(
      erdosProofFlowElements(part, detail.manuscript)
        .filter((element) => element.data.kind === "proofFlowNode")
        .map((element) => [element.data.proofNodeId, element.data.status]),
    );

    expect(nodeStatuses).toEqual({
      26: "implemented",
      27: "implemented",
      28: "implemented",
      29: "implemented",
      30: "implemented",
      31: "implemented",
      32: "implemented",
      33: "implemented",
      34: "implemented",
    });
  });
});
