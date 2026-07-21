import { readFileSync } from "node:fs";
import { resolve } from "node:path";

import { describe, expect, it } from "vitest";

import {
  ERDOS_PROOF_FLOW_NODES,
  ERDOS_PROOF_FLOW_PARTS,
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
    formalizedNodeIds: [1, 3, 18],
    nodeObligations: [
      {
        nodeId: 1,
        obligationId: "compiled-node-1",
        title: "Compiled partial ledger",
        statement: "A partial ledger cannot demote a formalized node.",
        status: "partial",
        evidenceStepIds: ["implemented"],
      },
      {
        nodeId: 2,
        obligationId: "compiled-node-2",
        title: "Compiled node-file ledger",
        statement: "An existing unchecked node file is yellow.",
        status: "partial",
        evidenceStepIds: ["implemented"],
      },
      {
        nodeId: 19,
        obligationId: "compiled-node-19",
        title: "Compiled frontier ledger",
        statement: "A missing node file can be frontier-orange when its parent is green.",
        status: "missing",
        evidenceStepIds: [],
      },
    ],
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
        manuscriptRefs: [{ label: "implemented", title: "Implemented", nodeIds: [1, 2, 4] }],
        declarationGroups: [],
        scopeNotes: "None.",
        workBound: "Finite.",
      },
    ],
  };
}

function proofDiagramBody(source: string, label: string): string {
  const figures = [...source.matchAll(/\\begin\{figure\}[\s\S]*?\\end\{figure\}/g)];
  const figure = figures.find((candidate) =>
    candidate[0].includes(`\\label{${label}}`));
  if (!figure) throw new Error(`missing proof diagram ${label}`);
  const tikz = figure[0].match(
    /\\begin\{tikzpicture\}[\s\S]*?\\end\{tikzpicture\}%?/,
  );
  if (!tikz) throw new Error(`missing TikZ body for ${label}`);
  return tikz[0];
}

function generatedManuscript(): ExampleManuscript {
  const detail = JSON.parse(readFileSync(
    resolve(process.cwd(), "../../generated/examples/erdos-64.json"),
    "utf8",
  )) as ExampleDetail;
  if (!detail.manuscript) throw new Error("The generated Erdős artifact has no manuscript.");
  return detail.manuscript;
}

function implementedEvidenceNodeIds(manuscript: ExampleManuscript): Set<number> {
  return new Set(
    manuscript.proofSteps
      .filter((step) => step.status === "implemented")
      .flatMap((step) => step.manuscriptRefs.flatMap((reference) => reference.nodeIds))
      .filter(isOriginalErdosProofNode),
  );
}

describe("Erdős Chapter 1 proof flow", () => {
  it("contains all eleven paper diagrams and exactly the immutable node set", () => {
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

  it("matches the original and current manuscript diagram nodes without supplements", () => {
    const originalManuscript = readFileSync(
      resolve(process.cwd(), "../../original_erdos_64_proof.tex"),
      "utf8",
    );
    const originalNodeIds = new Set(
      [...originalManuscript.matchAll(/\\textbf\{\[(\d+)\]\}/g)]
        .map((match) => Number(match[1])),
    );
    expect([...ORIGINAL_ERDOS_PROOF_NODE_IDS]).toEqual([...originalNodeIds]);

    const currentManuscript = readFileSync(
      resolve(process.cwd(), "../../proofs/erdos_64_eg/erdos_64_proof.tex"),
      "utf8",
    );
    const currentNodeIds = [...new Set(
      [...currentManuscript.matchAll(/\\textbf\{\[(\d+)\]\}/g)]
        .map((match) => Number(match[1])),
    )].sort((left, right) => left - right);

    expect(ERDOS_PROOF_FLOW_NODES.map(({ nodeId }) => nodeId).sort((a, b) => a - b))
      .toEqual(currentNodeIds);
    expect(isOriginalErdosProofNode(157)).toBe(true);
    expect(isOriginalErdosProofNode(158)).toBe(false);
  });

  it("keeps every live Chapter 1 diagram identical to the original TikZ source", () => {
    const originalManuscript = readFileSync(
      resolve(process.cwd(), "../../original_erdos_64_proof.tex"),
      "utf8",
    );
    const currentManuscript = readFileSync(
      resolve(process.cwd(), "../../proofs/erdos_64_eg/erdos_64_proof.tex"),
      "utf8",
    );
    const parts = ["i", "ii", "iii", "iv", "v", "vi", "vii", "viii", "ix", "x", "xi"];

    for (const part of parts) {
      const label = `fig:proof-diagram-part-${part}`;
      expect(proofDiagramBody(currentManuscript, label), label)
        .toBe(proofDiagramBody(originalManuscript, label));
    }
  });

  it("ships cropped original-figure assets rather than full manuscript pages", () => {
    for (let part = 1; part <= 11; part += 1) {
      const svg = readFileSync(
        resolve(process.cwd(), `public/assets/erdos-original/part-${part}.svg`),
        "utf8",
      );
      expect(svg, `Part ${part} must be an isolated figure`).toMatch(/<[^>]*svg[^>]*viewBox=/);
      expect(svg, `Part ${part} must not be a 612×792 manuscript page`)
        .not.toContain('viewBox="0 0 612 792"');
    }
  });

  it("uses formalizedNodeIds as the sole green authority", () => {
    const manuscript = manuscriptWithStatuses();
    const statuses = proofFlowNodeStatuses(manuscript);
    const formalized = new Set(manuscript.formalizedNodeIds);

    for (const node of ERDOS_PROOF_FLOW_NODES) {
      const status = statuses.get(node.nodeId) ?? "notStarted";
      expect(status === "implemented", "node " + node.nodeId).toBe(formalized.has(node.nodeId));
    }

    expect(statuses.get(1)).toBe("implemented");
    expect(statuses.get(3)).toBe("implemented");
    expect(statuses.get(18)).toBe("implemented");
    expect(statuses.get(2)).toBe("partial");
    expect(statuses.get(4)).toBeUndefined();
    expect(statuses.get(19)).toBe("next");
  });

  it("renders green, yellow, frontier, and untouched nodes from compiled status data", () => {
    const manuscript = manuscriptWithStatuses();
    const elements = erdosProofFlowElements(ERDOS_PROOF_FLOW_PARTS[0], manuscript);

    expect(elements.find((element) => element.data.id === "proof-node:3")?.data)
      .toMatchObject({
        proofNodeId: 3,
        verified: true,
        status: "implemented",
        closure: "closed",
        proofOrigin: "original",
      });
    expect(elements.find((element) => element.data.id === "proof-node:2")?.data)
      .toMatchObject({
        verified: false,
        status: "partial",
        obligationsProved: 0,
        obligationsTotal: 1,
        obligationsRemaining: 1,
      });
    expect(elements.find((element) => element.data.id === "proof-node:4")?.data)
      .toMatchObject({
        verified: false,
        status: "notStarted",
        obligationsProved: 0,
        obligationsTotal: 1,
        obligationsRemaining: 1,
      });
    expect(elements.find((element) => element.data.id === "proof-node:19")?.data)
      .toMatchObject({ verified: false, status: "next" });
    expect(elements.find((element) => element.data.id === "proof-node:5")?.data)
      .toMatchObject({ verified: false, status: "notStarted" });

    expect(elements.find((element) => element.data.id === "proof-node:2")?.data.label)
      .toContain("Obligations 0/1 · 1 left");
    expect(proofFlowNodeSteps(manuscript).get(2)).toEqual(["paper", "implemented"]);
  });

  it("prefers compiled node obligations and otherwise projects one whole paper cell", () => {
    const manuscript = manuscriptWithStatuses();

    expect(proofFlowNodeObligations(manuscript, 1)).toEqual(
      manuscript.nodeObligations?.filter((obligation) => obligation.nodeId === 1),
    );
    expect(proofFlowNodeObligations(manuscript, 2)).toEqual(
      manuscript.nodeObligations?.filter((obligation) => obligation.nodeId === 2),
    );

    expect(proofFlowNodeObligations(manuscript, 3)).toEqual([{
      obligationId: "node-3-paper-cell",
      title: "Original diagram-cell responsibility",
      statement: "not a counterexample",
      status: "proved",
      evidenceStepIds: [],
    }]);
    expect(proofFlowNodeObligations(manuscript, 4)).toEqual([{
      obligationId: "node-4-paper-cell",
      title: "Original diagram-cell responsibility",
      statement: "choose a lexicographically minimal counterexample",
      status: "partial",
      evidenceStepIds: ["implemented"],
    }]);
    expect(proofFlowNodeObligations(manuscript, 5)).toEqual([{
      obligationId: "node-5-paper-cell",
      title: "Original diagram-cell responsibility",
      statement: "target algebra: every oriented edge has no Mersenne return",
      status: "missing",
      evidenceStepIds: [],
    }]);
    expect(proofFlowNodeObligations(manuscript, 158)).toEqual([]);
  });

  it("round-trips proof node element IDs", () => {
    expect(proofFlowNodeElementId(157)).toBe("proof-node:157");
    expect(proofFlowNodeNumber("proof-node:157")).toBe(157);
    expect(proofFlowNodeNumber("proof-edge:1:1")).toBeNull();
  });

  it("matches green and yellow nodes to the current compiled artifact", () => {
    const manuscript = generatedManuscript();
    const statuses = proofFlowNodeStatuses(manuscript);
    const formalized = new Set(manuscript.formalizedNodeIds);

    const greenNodeIds = ERDOS_PROOF_FLOW_NODES
      .filter((node) => statuses.get(node.nodeId) === "implemented")
      .map((node) => node.nodeId)
      .sort((left, right) => left - right);
    expect(greenNodeIds).toEqual([...formalized].sort((left, right) => left - right));
    expect(greenNodeIds).toHaveLength(manuscript.coverage.verifiedDiagramNodes);
    expect(ERDOS_PROOF_FLOW_NODES).toHaveLength(manuscript.coverage.totalDiagramNodes);

    const partialNodeIds = [...statuses.entries()]
      .filter(([, status]) => status === "partial")
      .map(([nodeId]) => nodeId)
      .sort((left, right) => left - right);
    const expectedPartialNodeIds = (manuscript.nodeObligations ?? [])
      .filter((obligation) => obligation.status === "partial")
      .map((obligation) => obligation.nodeId)
      .filter((nodeId, index, nodeIds) => nodeIds.indexOf(nodeId) === index)
      .sort((left, right) => left - right);
    expect(partialNodeIds).toEqual(expectedPartialNodeIds);
  });

  it("projects only compiled ledgers or one whole-cell fallback in the current artifact", () => {
    const manuscript = generatedManuscript();
    const formalized = new Set(manuscript.formalizedNodeIds);
    const evidenceNodes = implementedEvidenceNodeIds(manuscript);

    for (const node of ERDOS_PROOF_FLOW_NODES) {
      const compiled = (manuscript.nodeObligations ?? []).filter(
        (obligation) => obligation.nodeId === node.nodeId,
      );
      const projected = proofFlowNodeObligations(manuscript, node.nodeId);

      if (compiled.length > 0) {
        expect(projected, "node " + node.nodeId).toEqual(compiled);
        continue;
      }

      expect(projected, "node " + node.nodeId).toHaveLength(1);
      expect(projected[0]).toMatchObject({
        obligationId: "node-" + node.nodeId + "-paper-cell",
        statement: node.label,
        status: formalized.has(node.nodeId)
          ? "proved"
          : evidenceNodes.has(node.nodeId)
            ? "partial"
            : "missing",
      });
    }
  });

  it("aggregates progress from the same compiled-or-whole-cell projections", () => {
    const manuscript = generatedManuscript();
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

  it("contains no frontend-authored obligation or gap ledgers", () => {
    const source = readFileSync(resolve(process.cwd(), "src/erdos-proof-flow.ts"), "utf8");
    for (const legacyName of [
      "ORIGINAL_ERDOS_NODE_PAPER_GAPS",
      "DEMOTED_PREDECESSOR_GAPS",
      "ORIGINAL_ERDOS_NODE_REMAINING",
      "ORIGINAL_ERDOS_NODE_OBLIGATIONS",
      "AUDITED_ERDOS_NODE_OBLIGATIONS",
    ]) {
      expect(source).not.toContain(legacyName);
    }
  });
});
