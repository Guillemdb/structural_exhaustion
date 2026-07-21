import { useEffect, useMemo, useState } from "react";

import {
  ERDOS_PROOF_FLOW_NODES,
  ERDOS_PROOF_FLOW_PARTS,
  erdosProofFlowElements,
  proofFlowNodeObligationProgress,
  proofFlowNodeObligations,
  proofFlowNodeElementId,
  proofFlowNodeNumber,
  proofFlowNodeStatuses,
  proofFlowNodeSteps,
} from "../erdos-proof-flow";
import type {
  ExampleManuscript,
  ExampleProofStep,
  SelectedGraphElement,
} from "../types";
import { GraphCanvas } from "./GraphCanvas";

interface ErdosProofFlowDiagramProps {
  manuscript: ExampleManuscript;
  activeNodeId: number | null;
  onNodeSelect: (nodeId: number) => void;
  onEdgeSelect?: (sourceNodeId: number, targetNodeId: number) => void;
  showSelectionDetails?: boolean;
  defaultView?: "implemented" | "paper" | "compare";
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
  if (status === "implemented") return "Kernel-checked NodeX.lean file";
  if (status === "partial") return "NodeX.lean exists but is not kernel checked";
  if (status === "next") return "Frontier: direct parent is green";
  return "No NodeX.lean file";
}

export function ErdosProofFlowDiagram({
  manuscript,
  activeNodeId,
  onNodeSelect,
  onEdgeSelect,
  showSelectionDetails = true,
  defaultView = "implemented",
}: ErdosProofFlowDiagramProps) {
  const [diagramView, setDiagramView] = useState<"implemented" | "paper" | "compare">(
    defaultView,
  );
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
  const activeNodeInPart = activeNode
    && activePart.nodes.some((node) => node.nodeId === activeNode.nodeId)
    ? activeNode
    : null;
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
      .filter((step): step is ExampleProofStep => Boolean(step))
    : [];
  const implementedSteps = activeSteps.filter((step) => step.status === "implemented");
  const obligationLedger = activeNode
    ? proofFlowNodeObligations(manuscript, activeNode.nodeId)
    : [];
  const remainingObligations = obligationLedger.filter(
    (obligation) => obligation.status !== "proved",
  );
  const obligationProgress = activeNode
    ? proofFlowNodeObligationProgress(manuscript, activeNode.nodeId)
    : null;

  const handleGraphSelect = (selection: SelectedGraphElement | null) => {
    if (!selection) return;
    if (selection.group === "node") {
      const nodeId = proofFlowNodeNumber(selection.id);
      if (nodeId !== null) onNodeSelect(nodeId);
      return;
    }

    const sourceNodeId = typeof selection.data.source === "string"
      ? proofFlowNodeNumber(selection.data.source)
      : null;
    const targetNodeId = typeof selection.data.target === "string"
      ? proofFlowNodeNumber(selection.data.target)
      : null;
    if (sourceNodeId !== null && targetNodeId !== null) {
      onEdgeSelect?.(sourceNodeId, targetNodeId);
    }
  };

  const graphView = (
    <GraphCanvas
      mode="proofFlow"
      elements={elements}
      selectedId={activeNodeId === null ? null : proofFlowNodeElementId(activeNodeId)}
      onSelect={handleGraphSelect}
    />
  );
  const paperView = (
    <figure className="proof-flow-paper-view">
      <img
        src={`/assets/erdos-original/part-${activePart.part}.svg`}
        alt={`Original reference-paper proof-dependency diagram, Part ${activePart.roman}`}
      />
      <figcaption>
        Original reference manuscript · page {activePart.part + 10} · Part {activePart.roman}
      </figcaption>
    </figure>
  );

  return (
    <div className="proof-flow" aria-label="Complete Chapter 1 proof dependency diagram">
      <div className="proof-flow__intro">
        <div>
          <span className="eyebrow">All eleven Chapter 1 diagrams</span>
          <strong>{ERDOS_PROOF_FLOW_NODES.length}-node proof dependency map</strong>
        </div>
        <p>
          {diagramView === "implemented"
            ? "Green means the corresponding direct NodeX.lean file has a fresh kernel-checked artifact. Yellow means the direct NodeX.lean file exists but is not checked. Orange marks a no-file frontier node with a green direct parent, and white means no direct Lean node file."
            : diagramView === "paper"
              ? "This is the typeset page from the original reference manuscript, preserving its exact TikZ geometry, labels, arrows, mathematical notation, and caption for direct comparison with the implemented flowchart."
              : "The interactive Lean map and the exact typeset paper diagram are shown together. Select a numbered node on the left to keep its original-paper counterpart identified on the right."}
        </p>
        <div className="proof-flow-view-switch" role="group" aria-label="Diagram view">
          <button
            type="button"
            aria-pressed={diagramView === "implemented"}
            onClick={() => setDiagramView("implemented")}
          >
            Implemented flowchart
          </button>
          <button
            type="button"
            aria-pressed={diagramView === "paper"}
            onClick={() => setDiagramView("paper")}
          >
            Original paper
          </button>
          <button
            type="button"
            aria-pressed={diagramView === "compare"}
            onClick={() => setDiagramView("compare")}
          >
            Compare side by side
          </button>
        </div>
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
                  const nodeObligationProgress = proofFlowNodeObligationProgress(
                    manuscript,
                    node.nodeId,
                  );
                  const unconditionallyClosed = status === "implemented"
                    && node.kind === "terminal"
                    && !part.continuations.some(
                      (continuation) => continuation.source === node.nodeId,
                    );
                  return (
                    <button
                      type="button"
                      className={`proof-flow-node-chip proof-flow-node-chip--${status} ${unconditionallyClosed ? "proof-flow-node-chip--closed" : ""} ${activeNodeId === node.nodeId ? "is-active" : ""}`}
                      aria-label={`Node ${node.nodeId}: ${node.label}. ${statusLabel(status, unconditionallyClosed)}${status === "partial" ? `. Obligations: ${nodeObligationProgress.proved} of ${nodeObligationProgress.total} proved; ${nodeObligationProgress.remaining} remaining` : ""}`}
                      title={`[${node.nodeId}] ${node.label} — ${statusLabel(status, unconditionallyClosed)}${status === "partial" ? ` — obligations ${nodeObligationProgress.proved}/${nodeObligationProgress.total}, ${nodeObligationProgress.remaining} remaining` : ""}`}
                      onClick={() => onNodeSelect(node.nodeId)}
                      key={node.nodeId}
                    >
                      <span>{node.nodeId}</span>
                      {status === "partial" ? (
                        <small aria-hidden="true">
                          {nodeObligationProgress.proved}/{nodeObligationProgress.total}
                        </small>
                      ) : null}
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
        {diagramView === "implemented" ? graphView : null}
        {diagramView === "paper" ? paperView : null}
        {diagramView === "compare" ? (
          <div className="proof-flow-compare" aria-label="Implemented and original proof diagrams">
            <section>
              <h3>Interactive Lean map</h3>
              {graphView}
            </section>
            <section>
              <h3>Original paper</h3>
              {paperView}
              <aside
                className="proof-flow-paper-callout"
                aria-label="Selected paper node"
                aria-live="polite"
              >
                <span>Selected correspondence</span>
                {activeNodeInPart ? (
                  <>
                    <strong>[{activeNodeInPart.nodeId}] {activeNodeInPart.label}</strong>
                    <p>
                      This numbered cell is the original-paper counterpart of the selected
                      node in the interactive map.
                    </p>
                  </>
                ) : activeNode ? (
                  <p>
                    The selected node [{activeNode.nodeId}] belongs to Part{" "}
                    {partForNode(activeNode.nodeId).roman}. Select a node in the current map
                    to identify its paper cell here.
                  </p>
                ) : (
                  <p>Select a numbered node in the interactive map to identify its paper cell.</p>
                )}
              </aside>
            </section>
          </div>
        ) : null}
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

      {showSelectionDetails ? (
        <section className="proof-flow-selection" aria-live="polite">
        {activeNode && activeStatus ? (
          <>
            <div className="proof-flow-selection__heading">
              <span className={`proof-flow-status proof-flow-status--${activeUnconditionallyClosed ? "closed" : activeStatus}`}>
                {statusLabel(
                  activeStatus,
                  activeUnconditionallyClosed,
                )}
              </span>
              <strong>[{activeNode.nodeId}] {activeNode.label}</strong>
              {activeStatus === "partial" && obligationProgress ? (
                <span
                  className="proof-flow-selection__obligation-progress"
                  aria-label={`${obligationProgress.proved} of ${obligationProgress.total} obligations proved; ${obligationProgress.remaining} remaining`}
                >
                  <b>{obligationProgress.proved}/{obligationProgress.total}</b>
                  <small>{obligationProgress.remaining} remaining</small>
                </span>
              ) : null}
            </div>
            <p>
              {activeSteps.length && activeStatus === "partial"
                ? `Lean evidence covers part of this paper node through ${activeSteps.map((step) => step?.title).join(", ")}; the complete displayed assertion is not yet formalized.`
                : activeSteps.length
                  ? `Indexed by ${activeSteps.map((step) => step?.title).join(", ")}. Select the node to keep its manuscript and Lean evidence synchronized below.`
                : "No implemented Lean proof step is indexed to this paper node yet."}
            </p>
            <section
              className="proof-flow-obligation-ledger"
              aria-label="Original-paper obligation ledger"
            >
              <header>
                <div>
                  <span>Auditable node contract</span>
                  <h3>Original-paper obligation ledger</h3>
                </div>
                <strong>{obligationProgress?.proved ?? 0}/{obligationProgress?.total ?? 0} proved · {obligationProgress?.remaining ?? 0} remaining</strong>
              </header>
              <ul>
                {obligationLedger.map((obligation) => (
                  <li key={obligation.obligationId}>
                    <div>
                      <strong>{obligation.title}</strong>
                      <span className={`proof-obligation-status proof-obligation-status--${obligation.status}`}>
                        {obligation.status}
                      </span>
                    </div>
                    <p>{obligation.statement}</p>
                    {obligation.evidenceStepIds.length ? (
                      <small>Lean evidence: {obligation.evidenceStepIds.join(", ")}</small>
                    ) : null}
                  </li>
                ))}
              </ul>
            </section>
            {activeStatus === "implemented" || activeStatus === "partial" ? (
              <div className="proof-flow-progress">
                <section
                  className={`proof-flow-progress__implemented proof-flow-progress__implemented--${activeStatus}`}
                  aria-label={activeStatus === "implemented"
                    ? "Full Lean implementation"
                    : "Implemented Lean progress"}
                >
                  <header>
                    <div>
                      <span>{activeStatus === "implemented" ? "Complete" : "Done so far"}</span>
                      <h3>{activeStatus === "implemented"
                        ? "Full Lean implementation"
                        : "Implemented Lean progress"}</h3>
                    </div>
                    <strong>{implementedSteps.reduce(
                      (count, step) => count + step.declarationGroups.length,
                      0,
                    )} evidence groups</strong>
                  </header>
                  {implementedSteps.length ? (
                    <div className="proof-flow-progress__steps">
                      {implementedSteps.map((step) => (
                        <article key={step.stepId}>
                          <h4>{step.title}</h4>
                          <p>{step.plainExplanation}</p>
                          {step.declarationGroups.length ? (
                            <ul className="proof-flow-evidence-list">
                              {step.declarationGroups.map((group) => (
                                <li key={`${step.stepId}-${group.groupId}`}>
                                  <strong>{group.title}</strong>
                                  <p>{group.explanation}</p>
                                  <details>
                                    <summary>
                                      {group.declarationIds.length} kernel-checked {group.declarationIds.length === 1
                                        ? "declaration"
                                        : "declarations"}
                                    </summary>
                                    <ul>
                                      {group.declarationIds.map((declarationId) => (
                                        <li key={declarationId}><code>{declarationId}</code></li>
                                      ))}
                                    </ul>
                                  </details>
                                </li>
                              ))}
                            </ul>
                          ) : (
                            <p className="empty-copy">This implemented step has no focused declaration group.</p>
                          )}
                        </article>
                      ))}
                    </div>
                  ) : (
                    <p className="empty-copy">No completed Lean evidence is indexed to this node.</p>
                  )}
                </section>

                {remainingObligations.length ? (
                  <section
                    className="proof-flow-progress__remaining"
                    aria-label="Remaining obligations before green"
                  >
                    <header>
                      <div>
                        <span>Still required</span>
                        <h3>Remaining obligations before green</h3>
                      </div>
                      <strong>{remainingObligations.length} {remainingObligations.length === 1
                        ? "obligation"
                        : "obligations"}</strong>
                    </header>
                    <ul>
                      {remainingObligations.map((obligation) => (
                        <li key={`${obligation.obligationId}-remaining`}>
                          <strong>{obligation.title}</strong>
                          <p>{obligation.statement}</p>
                        </li>
                      ))}
                    </ul>
                    {activeSteps.length ? (
                      <details className="proof-flow-progress__scope-audit">
                        <summary>Lean proof-step scope notes</summary>
                        <ul>
                          {activeSteps.map((step) => (
                            <li key={`${step.stepId}-audit`}>
                              <strong>{step.title}</strong>
                              <p>{step.scopeNotes}</p>
                            </li>
                          ))}
                        </ul>
                      </details>
                    ) : null}
                  </section>
                ) : null}
              </div>
            ) : null}
          </>
        ) : (
          <p>Select any numbered node to inspect its formalization status.</p>
        )}
        </section>
      ) : null}
    </div>
  );
}
