import { useEffect, useMemo, useState } from "react";

import {
  ERDOS_PROOF_FLOW_NODES,
  ERDOS_PROOF_FLOW_PARTS,
  erdosProofFlowElements,
  proofFlowNodeElementId,
  proofFlowNodeNumber,
  proofFlowNodeStatuses,
  proofFlowNodeSteps,
} from "../erdos-proof-flow";
import type { ExampleManuscript, SelectedGraphElement } from "../types";
import { GraphCanvas } from "./GraphCanvas";

interface ErdosProofFlowDiagramProps {
  manuscript: ExampleManuscript;
  activeNodeId: number | null;
  onNodeSelect: (nodeId: number) => void;
}

function partForNode(nodeId: number | null) {
  if (nodeId === null) return ERDOS_PROOF_FLOW_PARTS[0];
  return ERDOS_PROOF_FLOW_PARTS.find((part) =>
    part.nodes.some((node) => node.nodeId === nodeId)) ?? ERDOS_PROOF_FLOW_PARTS[0];
}

function statusLabel(
  status: "implemented" | "partial" | "next" | "notStarted",
  unconditionallyClosed = false,
) {
  if (unconditionallyClosed) return "Unconditionally closed in Lean";
  if (status === "implemented") return "Formalized in Lean";
  if (status === "partial") return "Partially formalized in Lean";
  if (status === "next") return "Current formalization frontier";
  return "Paper proof only";
}

export function ErdosProofFlowDiagram({
  manuscript,
  activeNodeId,
  onNodeSelect,
}: ErdosProofFlowDiagramProps) {
  const [activePartNumber, setActivePartNumber] = useState(
    () => partForNode(activeNodeId).part,
  );
  const statuses = useMemo(() => proofFlowNodeStatuses(manuscript), [manuscript]);
  const nodeSteps = useMemo(() => proofFlowNodeSteps(manuscript), [manuscript]);

  useEffect(() => {
    if (activeNodeId !== null) {
      setActivePartNumber(partForNode(activeNodeId).part);
    }
  }, [activeNodeId]);

  const activePart = ERDOS_PROOF_FLOW_PARTS.find(
    (part) => part.part === activePartNumber,
  ) ?? ERDOS_PROOF_FLOW_PARTS[0];
  const elements = useMemo(
    () => erdosProofFlowElements(activePart, manuscript),
    [activePart, manuscript],
  );
  const activeNode = activeNodeId === null
    ? null
    : ERDOS_PROOF_FLOW_NODES.find((node) => node.nodeId === activeNodeId) ?? null;
  const activeStatus = activeNode
    ? statuses.get(activeNode.nodeId) ?? "notStarted"
    : null;
  const activePartForNode = activeNode ? partForNode(activeNode.nodeId) : null;
  const activeUnconditionallyClosed = Boolean(
    activeNode
      && activeStatus === "implemented"
      && activeNode.kind === "terminal"
      && !activePartForNode?.continuations.some(
        (continuation) => continuation.source === activeNode.nodeId,
      ),
  );
  const activeSteps = activeNode
    ? (nodeSteps.get(activeNode.nodeId) ?? [])
      .map((stepId) => manuscript.proofSteps.find((step) => step.stepId === stepId))
      .filter((step) => Boolean(step))
    : [];

  const handleGraphSelect = (selection: SelectedGraphElement | null) => {
    if (!selection || selection.group !== "node") return;
    const nodeId = proofFlowNodeNumber(selection.id);
    if (nodeId !== null) onNodeSelect(nodeId);
  };

  return (
    <div className="proof-flow" aria-label="Complete Chapter 1 proof dependency diagram">
      <div className="proof-flow__intro">
        <div>
          <span className="eyebrow">All eleven Chapter 1 diagrams</span>
          <strong>{ERDOS_PROOF_FLOW_NODES.length}-node proof dependency map</strong>
        </div>
        <p>
          Every numbered cell below is a paper node. Green means that the complete
          displayed assertion is formalized in Lean; darker green marks a verified
          terminal leaf that closes its branch unconditionally. Yellow marks partial
          Lean coverage, amber marks the declared next frontier, and white is paper-only.
        </p>
      </div>

      <div className="proof-flow-overview" aria-label="Chapter 1 proof parts">
        {ERDOS_PROOF_FLOW_PARTS.map((part) => {
          const verified = part.nodes.filter(
            (node) => statuses.get(node.nodeId) === "implemented",
          ).length;
          return (
            <section
              className={`proof-flow-part-card ${part.part === activePart.part ? "is-active" : ""}`}
              key={part.part}
            >
              <button
                type="button"
                className="proof-flow-part-card__heading"
                aria-pressed={part.part === activePart.part}
                onClick={() => setActivePartNumber(part.part)}
              >
                <span>Part {part.roman}</span>
                <small>{verified}/{part.nodes.length} formalized</small>
              </button>
              <div className="proof-flow-part-card__nodes">
                {part.nodes.map((node) => {
                  const status = statuses.get(node.nodeId) ?? "notStarted";
                  const unconditionallyClosed = status === "implemented"
                    && node.kind === "terminal"
                    && !part.continuations.some(
                      (continuation) => continuation.source === node.nodeId,
                    );
                  return (
                    <button
                      type="button"
                      className={`proof-flow-node-chip proof-flow-node-chip--${status} ${unconditionallyClosed ? "proof-flow-node-chip--closed" : ""} ${activeNodeId === node.nodeId ? "is-active" : ""}`}
                      aria-label={`Node ${node.nodeId}: ${node.label}. ${statusLabel(status, unconditionallyClosed)}`}
                      title={`[${node.nodeId}] ${node.label} — ${statusLabel(status, unconditionallyClosed)}`}
                      onClick={() => onNodeSelect(node.nodeId)}
                      key={node.nodeId}
                    >
                      {node.nodeId}
                    </button>
                  );
                })}
              </div>
            </section>
          );
        })}
      </div>

      <section className="proof-flow-detail" aria-label={`Proof dependency diagram Part ${activePart.roman}`}>
        <header>
          <div>
            <span className="eyebrow">Proof-dependency diagram · Part {activePart.roman}</span>
            <h2>{activePart.title}</h2>
            <p>{activePart.summary}</p>
          </div>
          <span>{activePart.nodes[0]?.nodeId}–{activePart.nodes.at(-1)?.nodeId}</span>
        </header>
        <GraphCanvas
          mode="proofFlow"
          elements={elements}
          selectedId={activeNodeId === null ? null : proofFlowNodeElementId(activeNodeId)}
          onSelect={handleGraphSelect}
        />
        {activePart.continuations.length ? (
          <nav className="proof-flow-continuations" aria-label={`Part ${activePart.roman} continuations`}>
            <strong>Cross-part continuations</strong>
            {activePart.continuations.map((continuation) => (
              <button
                type="button"
                onClick={() => onNodeSelect(continuation.target)}
                key={`${continuation.source}-${continuation.target}`}
              >
                [{continuation.source}] → [{continuation.target}] {continuation.label}
              </button>
            ))}
          </nav>
        ) : null}
      </section>

      <section className="proof-flow-selection" aria-live="polite">
        {activeNode && activeStatus ? (
          <>
            <div>
              <span className={`proof-flow-status proof-flow-status--${activeUnconditionallyClosed ? "closed" : activeStatus}`}>
                {statusLabel(activeStatus, activeUnconditionallyClosed)}
              </span>
              <strong>[{activeNode.nodeId}] {activeNode.label}</strong>
            </div>
            <p>
              {activeSteps.length && activeStatus === "partial"
                ? `Lean evidence covers part of this paper node through ${activeSteps.map((step) => step?.title).join(", ")}; the complete displayed assertion is not yet formalized.`
                : activeSteps.length
                  ? `Indexed by ${activeSteps.map((step) => step?.title).join(", ")}. Select the node to keep its manuscript and Lean evidence synchronized below.`
                : "No implemented Lean proof step is indexed to this paper node yet."}
            </p>
          </>
        ) : (
          <p>Select any numbered node to inspect its formalization status.</p>
        )}
      </section>
    </div>
  );
}
