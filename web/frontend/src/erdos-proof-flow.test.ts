import { readFileSync } from "node:fs";
import { resolve } from "node:path";

import { describe, expect, it } from "vitest";

import {
  ERDOS_PROOF_FLOW_NODES,
  ERDOS_PROOF_FLOW_PARTS,
  AUDITED_ERDOS_NODE_OBLIGATIONS,
  ORIGINAL_ERDOS_NODE_OBLIGATIONS,
  ORIGINAL_ERDOS_PROOF_NODE_IDS,
  erdosProofFlowElements,
  isOriginalErdosProofNode,
  proofFlowNodeElementId,
  proofFlowNodeNumber,
  proofFlowObligationProgress,
  proofFlowNodeObligationProgress,
  proofFlowNodeObligations,
  proofFlowNodeSteps,
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
  it("contains all eleven paper diagrams and exactly the original node set", () => {
    expect(ERDOS_PROOF_FLOW_PARTS).toHaveLength(11);
    expect(ERDOS_PROOF_FLOW_NODES).toHaveLength(157);
    expect(ERDOS_PROOF_FLOW_NODES.map((node) => node.nodeId).sort((a, b) => a - b)).toEqual(
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

  it("matches the original manuscript's diagram nodes without supplements", () => {
    const originalManuscript = readFileSync(
      resolve(process.cwd(), "../../original_erdos_64_proof.tex"),
      "utf8",
    );
    const manuscriptNodeIds = new Set(
      [...originalManuscript.matchAll(/\\textbf\{\[(\d+)\]\}/g)]
        .map((match) => Number(match[1])),
    );

    expect([...ORIGINAL_ERDOS_PROOF_NODE_IDS]).toEqual([...manuscriptNodeIds]);
    expect(isOriginalErdosProofNode(157)).toBe(true);
    expect(ERDOS_PROOF_FLOW_NODES.every(({ nodeId }) => isOriginalErdosProofNode(nodeId))).toBe(true);
  });

  it("matches every node displayed by the current Lean-indexed manuscript", () => {
    const currentManuscript = readFileSync(
      resolve(process.cwd(), "../../proofs/erdos_64_eg/erdos_64_proof.tex"),
      "utf8",
    );
    const manuscriptNodeIds = [...new Set(
      [...currentManuscript.matchAll(/\\textbf\{\[(\d+)\]\}/g)]
        .map((match) => Number(match[1])),
    )].sort((left, right) => left - right);

    expect(ERDOS_PROOF_FLOW_NODES.map(({ nodeId }) => nodeId).sort((a, b) => a - b))
      .toEqual(manuscriptNodeIds);
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
      proofOrigin: "original",
    });
    expect(elements.find((element) => element.data.id === "proof-node:19")?.data).toMatchObject({
      verified: false,
      status: "next",
    });
    expect(elements.find((element) => element.data.id === "proof-node:2")?.data).toMatchObject({
      verified: false,
      status: "partial",
      obligationsProved: 0,
      obligationsTotal: 1,
      obligationsRemaining: 1,
    });
    expect(elements.find((element) => element.data.id === "proof-node:2")?.data.label)
      .toContain("Obligations 0/1 · 1 left");
    expect(proofFlowNodeObligationProgress(manuscript, 2)).toEqual({
      proved: 0,
      total: 1,
      remaining: 1,
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
    const auditedCompleteNotFormalized = Object.entries(AUDITED_ERDOS_NODE_OBLIGATIONS)
      .filter(([nodeId, obligations]) =>
        obligations.length > 0
          && obligations.every((obligation) => obligation.status === "proved")
          && !detail.manuscript?.formalizedNodeIds.includes(Number(nodeId)))
      .length;
    expect(ERDOS_PROOF_FLOW_NODES).toHaveLength(
      detail.manuscript.coverage.totalDiagramNodes,
    );
    expect(verified).toHaveLength(
      detail.manuscript.coverage.verifiedDiagramNodes + auditedCompleteNotFormalized,
    );
    expect(statuses.get(3)).toBe("implemented");
    expect(statuses.get(19)).toBe("implemented");
    expect(statuses.get(131)).toBe("partial");
    expect(statuses.get(132)).toBe("partial");
    expect(statuses.get(155)).toBe("partial");
    for (const nodeId of [133, 134, 135, 136, 137, 138, 139, 141]) {
      expect(statuses.get(nodeId)).toBe("partial");
    }
    for (const nodeId of [...Array.from({ length: 28 }, (_, index) => index + 1), 145, 146, 148, 149]) {
      expect(statuses.get(nodeId)).toBe("implemented");
    }
    for (const nodeId of [75, 80, 81, 82, 83, 84, 125, 140, 142, 143, 144, 151, 152]) {
      expect(statuses.get(nodeId)).toBe("partial");
    }
    expect([...statuses.keys()].every((nodeId) => nodeId <= 157)).toBe(true);

    const partOneElements = erdosProofFlowElements(ERDOS_PROOF_FLOW_PARTS[0], detail.manuscript);
    expect(partOneElements.find((element) => element.data.id === "proof-node:3")?.data)
      .toMatchObject({ status: "implemented", closure: "closed" });

    const partTen = ERDOS_PROOF_FLOW_PARTS.find((part) => part.part === 10);
    expect(partTen).toBeDefined();
    if (!partTen) return;
    expect(erdosProofFlowElements(partTen, detail.manuscript)
      .find((element) => element.data.id === "proof-node:138")?.data)
      .toMatchObject({ status: "partial", closure: "open" });
    expect(erdosProofFlowElements(partTen, detail.manuscript)
      .find((element) => element.data.id === "proof-node:144")?.data)
      .toMatchObject({ status: "partial", closure: "open", proofOrigin: "original" });
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
    expect(partialNodeIds).toEqual([
      40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
      57, 58, 59, 60, 61, 62, 63, 67, 68, 69,
      70, 71, 72, 73, 74, 75, 78, 79, 80, 81, 82, 83, 84, 86, 87, 88, 89,
      125, 126, 127,
      128, 129, 130, 131,
      132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 147, 150, 151,
      152, 153, 154, 155,
    ]);
    expect(Object.values(ORIGINAL_ERDOS_NODE_OBLIGATIONS).every(
      (obligations) => obligations.length > 0 && obligations.every((item) =>
        item.obligationId.trim()
          && item.title.trim()
          && item.statement.trim()
          && item.status === "missing"
          && item.evidenceStepIds.length === 0),
    )).toBe(true);
    const indexedSteps = proofFlowNodeSteps(detail.manuscript);
    for (const nodeId of partialNodeIds) {
      const steps = (indexedSteps.get(nodeId) ?? []).map((stepId) =>
        detail.manuscript?.proofSteps.find((step) => step.stepId === stepId));
      const implemented = steps.filter((step) => step?.status === "implemented");
      expect(implemented.length, `node ${nodeId} implemented progress`).toBeGreaterThan(0);
      expect(
        implemented.flatMap((step) => step?.declarationGroups ?? []).length,
        `node ${nodeId} declaration groups`,
      ).toBeGreaterThan(0);
      expect(
        steps.every((step) => Boolean(step?.scopeNotes.trim())),
        `node ${nodeId} remaining scope`,
      ).toBe(true);
    }
    for (const node of ERDOS_PROOF_FLOW_NODES) {
      const obligations = proofFlowNodeObligations(detail.manuscript, node.nodeId);
      expect(obligations.length, `node ${node.nodeId} obligation tasks`).toBeGreaterThan(0);
      expect(new Set(obligations.map((item) => item.obligationId)).size)
        .toBe(obligations.length);
      for (const obligation of obligations) {
        expect(obligation.title.trim()).not.toBe("");
        expect(obligation.statement.trim()).not.toBe("");
        if (obligation.status === "proved" && !AUDITED_ERDOS_NODE_OBLIGATIONS[node.nodeId]) {
          expect(
            obligation.evidenceStepIds.length,
            `node ${node.nodeId} proved task ${obligation.obligationId} evidence`,
          ).toBeGreaterThan(0);
        }
        for (const stepId of obligation.evidenceStepIds) {
          const evidence = detail.manuscript.proofSteps.find((step) => step.stepId === stepId);
          if (!evidence && AUDITED_ERDOS_NODE_OBLIGATIONS[node.nodeId]) {
            continue;
          }
          expect(evidence?.status, `${obligation.obligationId} evidence ${stepId}`).toBe("implemented");
          expect(evidence?.manuscriptRefs.some((reference) =>
            reference.nodeIds.includes(node.nodeId)), `${obligation.obligationId} node provenance`)
            .toBe(true);
        }
      }
    }
    expect(statuses.get(3)).toBe("implemented");
    expect(statuses.get(22)).toBe("implemented");
    expect(statuses.get(23)).toBe("implemented");
    expect(statuses.get(24)).toBe("implemented");
    expect(statuses.get(25)).toBe("implemented");
    expect(statuses.get(26)).toBe("implemented");
    expect(statuses.get(145)).toBe("implemented");
    expect(statuses.get(151)).toBe("partial");
    expect(statuses.get(152)).toBe("partial");
    expect(statuses.get(153)).toBe("partial");
    expect(statuses.get(64) ?? "notStarted").toBe("notStarted");
    expect(statuses.get(65) ?? "notStarted").toBe("notStarted");
    expect(statuses.get(66) ?? "notStarted").toBe("notStarted");
  });

  it("matches the audited frontier, Part X, and Part XI property counts exactly", () => {
    const detail = JSON.parse(readFileSync(
      resolve(process.cwd(), "../../generated/examples/erdos-64.json"),
      "utf8",
    )) as ExampleDetail;
    expect(detail.manuscript).not.toBeNull();
    if (!detail.manuscript) return;

    const expected: Record<number, [number, number]> = {
      23: [3, 3], 24: [11, 11], 25: [5, 5], 26: [1, 1],
      57: [1, 2], 58: [2, 3], 59: [2, 3], 60: [0, 1],
      61: [4, 5], 62: [3, 4], 63: [4, 5],
      86: [4, 5], 87: [4, 5], 88: [5, 6], 89: [7, 8],
      125: [2, 6], 126: [4, 5], 127: [4, 5], 128: [5, 6],
      145: [6, 6], 146: [3, 3], 147: [4, 9], 148: [8, 8],
      149: [6, 6], 150: [8, 9], 151: [4, 5], 152: [4, 5],
      153: [7, 17], 154: [5, 7], 155: [1, 2], 156: [1, 3],
      157: [1, 4],
    };
    for (const [nodeIdText, [proved, total]] of Object.entries(expected)) {
      const nodeId = Number(nodeIdText);
      expect(proofFlowNodeObligationProgress(detail.manuscript, nodeId)).toEqual({
        proved,
        total,
        remaining: total - proved,
      });
      expect(AUDITED_ERDOS_NODE_OBLIGATIONS[nodeId].map((task) => task.obligationId))
        .toEqual([...new Set(AUDITED_ERDOS_NODE_OBLIGATIONS[nodeId]
          .map((task) => task.obligationId))]);
    }
    expect(AUDITED_ERDOS_NODE_OBLIGATIONS[147].filter((task) =>
      task.status === "missing")).toHaveLength(5);
    expect(AUDITED_ERDOS_NODE_OBLIGATIONS[150].filter((task) =>
      task.status === "missing")).toHaveLength(1);
    expect(AUDITED_ERDOS_NODE_OBLIGATIONS[153].find((task) =>
      task.obligationId === "XI-153-08")?.status).toBe("proved");
    expect(AUDITED_ERDOS_NODE_OBLIGATIONS[153].find((task) =>
      task.obligationId === "XI-153-08-PRODUCERS")?.status).toBe("missing");
  });

  it("does not count Lean evidence groups as separate manuscript obligations", () => {
    const detail = JSON.parse(readFileSync(
      resolve(process.cwd(), "../../generated/examples/erdos-64.json"),
      "utf8",
    )) as ExampleDetail;
    expect(detail.manuscript).not.toBeNull();
    if (!detail.manuscript) return;

    const green = proofFlowNodeObligations(detail.manuscript, 1);
    expect(green).toHaveLength(1);
    expect(green[0].obligationId).toBe("node-1-paper-cell");
    expect(green[0].status).toBe("proved");

    const unauditedPartial = proofFlowNodeObligations(detail.manuscript, 25);
    expect(unauditedPartial.some((task) =>
      task.obligationId.includes("-evidence-"))).toBe(false);
  });

  it("aggregates header task progress from the node obligation ledgers", () => {
    const manuscript = manuscriptWithStatuses();
    const expected = ERDOS_PROOF_FLOW_NODES
      .map((node) => proofFlowNodeObligationProgress(manuscript, node.nodeId))
      .reduce(
        (progress, nodeProgress) => ({
          proved: progress.proved + nodeProgress.proved,
          total: progress.total + nodeProgress.total,
          remaining: progress.remaining + nodeProgress.remaining,
        }),
        { proved: 0, total: 0, remaining: 0 },
      );

    expect(proofFlowObligationProgress(manuscript)).toEqual(expected);
    expect(expected.proved + expected.remaining).toBe(expected.total);
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
