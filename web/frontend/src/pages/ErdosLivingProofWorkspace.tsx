import { useMemo, useState } from "react";
import { Link } from "react-router-dom";

import { AppHeader } from "../components/AppHeader";
import {
  ErdosFrameworkImpact,
  type ErdosImpactTour,
} from "../components/ErdosFrameworkImpact";
import {
  ErdosHistoryView,
  type ErdosHistorySnapshot as ErdosHistoryViewSnapshot,
} from "../components/ErdosHistoryView";
import { ErdosNodeStory, type ErdosNodeStoryStatus } from "../components/ErdosNodeStory";
import { ErdosProofFlowDiagram } from "../components/ErdosProofFlowDiagram";
import { LeanSourceViewer } from "../components/LeanSourceViewer";
import {
  ERDOS_PROOF_FLOW_NODES,
  ERDOS_PROOF_FLOW_PARTS,
  ORIGINAL_ERDOS_PROOF_NODE_IDS,
  proofFlowNodeObligations,
  proofFlowNodeStatuses,
} from "../erdos-proof-flow";
import {
  ERDOS_FRAMEWORK_GUIDED_TOURS,
  deriveAllErdosNodeCausalEvidence,
  deriveErdosFrameworkLeverage,
  type ErdosGuidedTour,
  type ErdosNodeCausalEvidence,
} from "../erdos-proof-leverage";
import type {
  ErdosProofHistoryResponse,
  ErdosProofHistorySnapshot,
  ExampleProofStep,
  ExampleResponse,
  ExampleStage,
} from "../types";

type WorkspaceTab = "map" | "impact" | "history" | "method";
type NodeFilter = "all" | "implemented" | "partial" | "paper" | "frontier";

interface ErdosLivingProofWorkspaceProps {
  response: ExampleResponse;
  history: ErdosProofHistoryResponse | null;
  historyError?: string | null;
}

export function ErdosLivingProofWorkspace(props: ErdosLivingProofWorkspaceProps) {
  if (!props.response.example.manuscript) {
    return (
      <div className="app-page app-page--erdos">
        <AppHeader
          verification={props.response.verification}
          artifactWarnings={props.response.artifactWarnings}
          compact
        />
        <main className="standalone-state">This compiled example has no manuscript companion.</main>
      </div>
    );
  }
  return <ErdosLivingProofContent {...props} />;
}

function unique<T>(values: Iterable<T>): T[] {
  return [...new Set(values)];
}

function paperPartForNode(nodeId: number) {
  return ERDOS_PROOF_FLOW_PARTS.find((part) =>
    part.nodes.some((node) => node.nodeId === nodeId));
}

function firstDeclaration(proofSteps: readonly ExampleProofStep[]): string | null {
  for (const step of proofSteps) {
    for (const group of step.declarationGroups) {
      if (group.declarationIds[0]) return group.declarationIds[0];
    }
  }
  return null;
}

function historyChanges(
  snapshot: ErdosProofHistorySnapshot,
  previous: ErdosProofHistorySnapshot | undefined,
): string[] {
  if (!previous) {
    return [
      `Baseline records ${snapshot.formalizedNodeCount} completed original-paper nodes and ${snapshot.implementedWorkflowSteps} implemented workflow steps.`,
    ];
  }
  const changes: string[] = [];
  const nodeDelta = snapshot.formalizedNodeCount - previous.formalizedNodeCount;
  const stepDelta = snapshot.implementedWorkflowSteps - previous.implementedWorkflowSteps;
  const transitionDelta = snapshot.frameworkLeverage.registeredTransitionCount
    - previous.frameworkLeverage.registeredTransitionCount;
  if (nodeDelta) changes.push(`${nodeDelta > 0 ? "+" : ""}${nodeDelta} completed original-paper nodes.`);
  if (stepDelta) changes.push(`${stepDelta > 0 ? "+" : ""}${stepDelta} implemented workflow steps.`);
  if (transitionDelta) {
    changes.push(
      `${transitionDelta > 0 ? "+" : ""}${transitionDelta} registered transitions in use.`,
    );
  }
  return changes.length ? changes : ["No change in the displayed proof and reuse counters."];
}

function historyViewSnapshots(
  snapshots: readonly ErdosProofHistorySnapshot[],
): ErdosHistoryViewSnapshot[] {
  return snapshots.map((snapshot, index) => ({
    snapshotId: snapshot.artifactSha256,
    label: index === snapshots.length - 1 ? "Latest recorded artifact" : `Recorded artifact ${index + 1}`,
    capturedAt: snapshot.provenance.recordedAt,
    artifactHash: snapshot.artifactSha256.slice(0, 16),
    metrics: [
      {
        metricId: "paper-nodes",
        label: "Original nodes complete",
        value: `${snapshot.formalizedNodeCount}/${ORIGINAL_ERDOS_PROOF_NODE_IDS.size}`,
      },
      {
        metricId: "workflow-steps",
        label: "Implemented workflow steps",
        value: snapshot.implementedWorkflowSteps,
      },
      {
        metricId: "automated-links",
        label: "Framework-automated links",
        value: snapshot.frameworkLeverage.automatedLinkCount,
      },
      {
        metricId: "registered-transitions",
        label: "Registered transitions reused",
        value: snapshot.frameworkLeverage.registeredTransitionCount,
      },
      {
        metricId: "bindings",
        label: "Explicit framework bindings",
        value: snapshot.frameworkLeverage.interfaceBindingCount,
      },
      {
        metricId: "framework-declarations",
        label: "Framework declarations in evidence",
        value: snapshot.frameworkLeverage.declarationFootprint.framework,
        detail: "Namespace-owned declaration footprint; not source lines or hours saved.",
      },
      {
        metricId: "external-declarations",
        label: "Explicit external trust boundary",
        value: snapshot.frameworkLeverage.declarationFootprint.external,
        detail: "External declarations remain separate from both framework and author ownership.",
      },
    ],
    changes: historyChanges(snapshot, snapshots[index - 1]),
  }));
}

function impactTour(
  tour: ErdosGuidedTour,
  evidenceByNode: ReadonlyMap<number, ErdosNodeCausalEvidence>,
): ErdosImpactTour {
  const evidence = tour.nodeIds
    .map((nodeId) => evidenceByNode.get(nodeId))
    .filter((item): item is ErdosNodeCausalEvidence => Boolean(item));
  return {
    tourId: tour.tourId,
    title: tour.title,
    summary: tour.summary,
    stageIds: unique(evidence.flatMap((item) => item.stageIds)),
    authorSupplied: tour.stops.map((stop) => `${stop.title}: ${stop.paperQuestion}`).join(" "),
    frameworkSupplied: tour.stops.map((stop) => stop.frameworkContribution).join(" "),
    verifiedOutcome: tour.stops.map((stop) => stop.evidenceFocus).join(" "),
    tacticIds: unique(evidence.flatMap((item) => item.ctIds)),
  };
}

function storyStatus(
  status: "implemented" | "partial" | "next" | "notStarted",
  nodeId: number,
): ErdosNodeStoryStatus {
  if (status !== "implemented") return status === "partial" ? "partial" : "paper";
  const node = ERDOS_PROOF_FLOW_NODES.find((candidate) => candidate.nodeId === nodeId);
  const part = paperPartForNode(nodeId);
  const closesBranch = node?.kind === "terminal"
    && !part?.continuations.some((continuation) => continuation.source === nodeId);
  return closesBranch ? "closed" : "verified";
}

function nodeStatusLabel(status: "implemented" | "partial" | "next" | "notStarted") {
  if (status === "implemented") return "Checked NodeX.lean";
  if (status === "partial") return "Unchecked NodeX.lean";
  if (status === "next") return "Frontier";
  return "No node file";
}

function ErdosLivingProofContent({
  response,
  history,
  historyError = null,
}: ErdosLivingProofWorkspaceProps) {
  const { example } = response;
  const manuscript = example.manuscript!;

  const statuses = useMemo(() => proofFlowNodeStatuses(manuscript), [manuscript]);
  const leverage = useMemo(() => deriveErdosFrameworkLeverage(response), [response]);
  const causalEvidence = useMemo(() => deriveAllErdosNodeCausalEvidence(response), [response]);
  const evidenceByNode = useMemo(
    () => new Map(causalEvidence.map((evidence) => [evidence.nodeId, evidence])),
    [causalEvidence],
  );
  const frontierNodeIds = useMemo(() => {
    return ERDOS_PROOF_FLOW_NODES
      .filter((node) => statuses.get(node.nodeId) === "next")
      .map((node) => node.nodeId)
      .sort((left, right) => left - right);
  }, [statuses]);
  const frontierNodes = useMemo(() => new Set(frontierNodeIds), [frontierNodeIds]);
  const initialNodeId = frontierNodeIds[0]
    ?? manuscript.formalizedNodeIds.at(-1)
    ?? ERDOS_PROOF_FLOW_NODES[0]?.nodeId
    ?? null;
  const initialSteps = initialNodeId === null
    ? []
    : evidenceByNode.get(initialNodeId)?.proofSteps ?? [];

  const [activeTab, setActiveTab] = useState<WorkspaceTab>("map");
  const [selectedNodeId, setSelectedNodeId] = useState<number | null>(initialNodeId);
  const [activeProofStepId, setActiveProofStepId] = useState<string | null>(initialSteps[0]?.stepId ?? null);
  const [activeDeclarationId, setActiveDeclarationId] = useState<string | null>(firstDeclaration(initialSteps));
  const [selectedEdge, setSelectedEdge] = useState<{ source: number; target: number } | null>(null);
  const [query, setQuery] = useState("");
  const [nodeFilter, setNodeFilter] = useState<NodeFilter>("all");
  const [ctFilter, setCtFilter] = useState("all");
  const [partFilter, setPartFilter] = useState("all");
  const [activeTourId, setActiveTourId] = useState<string | null>(null);
  const [activeSnapshotId, setActiveSnapshotId] = useState<string | null>(
    history?.snapshots.at(-1)?.artifactSha256 ?? null,
  );

  const selectedEvidence = selectedNodeId === null
    ? null
    : evidenceByNode.get(selectedNodeId) ?? null;
  const selectedProofSteps = selectedEvidence ? [...selectedEvidence.proofSteps] : [];
  const selectedStages = selectedEvidence
    ? example.workflows.flatMap((workflow) => workflow.stages)
      .filter((stage) => selectedEvidence.stageIds.includes(stage.stageId))
    : [];
  const activeProofStep = selectedProofSteps.find((step) => step.stepId === activeProofStepId)
    ?? selectedProofSteps[0];
  const rawSelectedStatus = selectedNodeId === null
    ? "notStarted"
    : statuses.get(selectedNodeId) ?? "notStarted";
  const selectedObligations = selectedNodeId === null
    ? []
    : proofFlowNodeObligations(manuscript, selectedNodeId).map((obligation) => ({
        ...obligation,
        nodeId: selectedNodeId,
        evidenceStepIds: [...obligation.evidenceStepIds],
      }));

  const completedCount = manuscript.formalizedNodeIds.filter((nodeId) =>
    ORIGINAL_ERDOS_PROOF_NODE_IDS.has(nodeId)).length;
  const partialCount = ERDOS_PROOF_FLOW_NODES.filter((node) =>
    statuses.get(node.nodeId) === "partial").length;
  const completionPercent = Math.round(
    (completedCount / ORIGINAL_ERDOS_PROOF_NODE_IDS.size) * 100,
  );
  const descriptorHash = example.sourceOfTruth.descriptorSource?.sha256 ?? "unavailable";
  const artifactFresh = Boolean(example.sourceOfTruth.descriptorSource)
    && response.verification.state === "verified"
    && response.artifactWarnings.length === 0;
  const exportedObligations = manuscript.nodeObligations ?? [];
  const exportedObligationsProved = exportedObligations.filter(
    (obligation) => obligation.status === "proved",
  ).length;

  const filteredNodes = useMemo(() => {
    const normalizedQuery = query.trim().toLocaleLowerCase();
    return ERDOS_PROOF_FLOW_NODES.filter((node) => {
      const status = statuses.get(node.nodeId) ?? "notStarted";
      const evidence = evidenceByNode.get(node.nodeId);
      const part = paperPartForNode(node.nodeId);
      const matchesStatus = nodeFilter === "all"
        || (nodeFilter === "implemented" && status === "implemented")
        || (nodeFilter === "partial" && status === "partial")
        || (nodeFilter === "paper" && status !== "implemented" && status !== "partial")
        || (nodeFilter === "frontier" && frontierNodes.has(node.nodeId));
      const matchesCt = ctFilter === "all" || evidence?.ctIds.includes(ctFilter);
      const matchesPart = partFilter === "all" || String(part?.part) === partFilter;
      const searchable = [
        String(node.nodeId),
        node.label,
        ...(evidence?.proofSteps.flatMap((step) => [step.title, step.plainExplanation]) ?? []),
        ...(evidence?.ctIds ?? []),
        ...(evidence?.transitionProfileIds ?? []),
      ].join(" ").toLocaleLowerCase();
      return matchesStatus && matchesCt && matchesPart
        && (!normalizedQuery || searchable.includes(normalizedQuery));
    });
  }, [ctFilter, evidenceByNode, frontierNodes, nodeFilter, partFilter, query, statuses]);

  const impactTours = useMemo(
    () => ERDOS_FRAMEWORK_GUIDED_TOURS.map((tour) => impactTour(tour, evidenceByNode)),
    [evidenceByNode],
  );
  const displayedHistory = useMemo(
    () => historyViewSnapshots(history?.snapshots ?? []),
    [history],
  );

  const selectNode = (nodeId: number) => {
    const evidence = evidenceByNode.get(nodeId);
    const proofSteps = evidence?.proofSteps ?? [];
    setSelectedNodeId(nodeId);
    setActiveProofStepId(proofSteps[0]?.stepId ?? null);
    setActiveDeclarationId(firstDeclaration(proofSteps));
    setSelectedEdge(null);
  };

  const selectStage = (stage: ExampleStage, revealMap = true) => {
    const proofStep = manuscript.proofSteps.find((step) => step.stageId === stage.stageId);
    const nodeId = proofStep?.manuscriptRefs.flatMap((reference) => reference.nodeIds)[0];
    if (nodeId !== undefined) selectNode(nodeId);
    setActiveProofStepId(proofStep?.stepId ?? null);
    setActiveDeclarationId(
      stage.primaryDeclarationId || (proofStep ? firstDeclaration([proofStep]) : null),
    );
    if (revealMap) setActiveTab("map");
  };

  const selectDeclaration = (declarationId: string | null) => {
    setActiveDeclarationId(declarationId);
    if (!declarationId) return;
    const proofStep = selectedProofSteps.find((step) => step.declarationGroups.some((group) =>
      group.declarationIds.includes(declarationId)));
    if (proofStep) setActiveProofStepId(proofStep.stepId);
  };

  return (
    <div className="app-page app-page--erdos erdos-living-proof">
      <AppHeader
        verification={response.verification}
        artifactWarnings={response.artifactWarnings}
        compact
      />

      <header className="erdos-living-proof__hero">
        <div>
          <nav className="breadcrumbs" aria-label="Breadcrumb">
            <Link to="/framework/core">Framework</Link><span>/</span><strong>Erdős–Gyárfás Problem 64</strong>
          </nav>
          <span className="eyebrow">A living proof and framework case study</span>
          <h1>Erdős–Gyárfás Problem 64</h1>
          <p>
            Navigate every original-paper decision, inspect its Lean evidence, and see exactly
            where reusable structural-exhaustion contracts replace repeated proof plumbing.
          </p>
        </div>
        <aside className={`erdos-artifact-provenance ${artifactFresh ? "is-fresh" : "is-stale"}`}>
          <span>{artifactFresh ? "Fresh compiled descriptor" : "Artifact needs regeneration"}</span>
          <strong>{example.sourceOfTruth.descriptor}</strong>
          <code>{descriptorHash === "unavailable" ? descriptorHash : descriptorHash.slice(0, 16)}</code>
          <small>Proof state comes from this Lean-owned descriptor, never from the browser.</small>
        </aside>
      </header>

      <section className="erdos-living-progress" aria-label="Formalization progress">
        <article>
          <span>Original proof coverage</span>
          <strong>{completedCount}/{ORIGINAL_ERDOS_PROOF_NODE_IDS.size}</strong>
          <small>complete paper nodes</small>
        </article>
        <article>
          <span>Implemented evidence</span>
          <strong>{partialCount}</strong>
          <small>yellow, partially formalized nodes</small>
        </article>
        <article>
          <span>Directed frontier</span>
          <strong>{frontierNodeIds.length}</strong>
          <small>{frontierNodeIds.length ? `nodes ${frontierNodeIds.map((id) => `[${id}]`).join(", ")}` : "no next nodes exported"}</small>
        </article>
        <article>
          <span>Lean-owned node ledger</span>
          <strong>{exportedObligationsProved}/{exportedObligations.length}</strong>
          <small>exported obligations proved</small>
        </article>
        <div className="erdos-living-progress__bar" aria-label={`${completionPercent}% of original nodes complete`}>
          <span style={{ width: `${completionPercent}%` }} />
        </div>
      </section>

      <aside className="erdos-scope-banner">
        <strong>Kernel-checked partial formalization.</strong>
        <span>
          Green means the direct NodeX.lean file is kernel checked; yellow means the direct
          node file exists but is not checked. Orange marks no-file frontier nodes whose direct
          parent is green, and white marks no direct node file.
        </span>
      </aside>

      <nav className="erdos-workspace-tabs" aria-label="Living proof views">
        {([
          ["map", "Proof map"],
          ["impact", "Framework impact"],
          ["history", "Implementation history"],
          ["method", "How to read this"],
        ] as const).map(([tabId, label]) => (
          <button
            type="button"
            aria-current={activeTab === tabId ? "page" : undefined}
            onClick={() => setActiveTab(tabId)}
            key={tabId}
          >
            {label}
          </button>
        ))}
      </nav>

      {activeTab === "map" ? (
        <main className="erdos-map-workspace">
          <aside className="erdos-proof-index" aria-label="Search and filter paper nodes">
            <header>
              <span className="eyebrow">Original paper index</span>
              <strong>{filteredNodes.length} of {ERDOS_PROOF_FLOW_NODES.length} nodes</strong>
            </header>
            <label className="erdos-proof-index__search">
              <span>Search claim, Lean step, CT, or transition profile</span>
              <input
                type="search"
                value={query}
                placeholder="e.g. rank, CT15, node 31"
                onChange={(event) => setQuery(event.target.value)}
              />
            </label>
            <div className="erdos-proof-index__filters">
              <label>
                <span>Status</span>
                <select value={nodeFilter} onChange={(event) => setNodeFilter(event.target.value as NodeFilter)}>
                  <option value="all">All statuses</option>
                  <option value="implemented">Green · checked file</option>
                  <option value="partial">Yellow · unchecked file</option>
                  <option value="paper">White · no file</option>
                  <option value="frontier">Orange · frontier</option>
                </select>
              </label>
              <label>
                <span>Framework capability</span>
                <select value={ctFilter} onChange={(event) => setCtFilter(event.target.value)}>
                  <option value="all">All CTs</option>
                  {leverage.ctIds.map((ctId) => <option value={ctId} key={ctId}>{ctId}</option>)}
                </select>
              </label>
              <label>
                <span>Paper part</span>
                <select value={partFilter} onChange={(event) => setPartFilter(event.target.value)}>
                  <option value="all">All eleven parts</option>
                  {ERDOS_PROOF_FLOW_PARTS.map((part) => (
                    <option value={part.part} key={part.part}>Part {part.roman}</option>
                  ))}
                </select>
              </label>
            </div>
            <div className="erdos-proof-index__results">
              {filteredNodes.map((node) => {
                const status = statuses.get(node.nodeId) ?? "notStarted";
                const evidence = evidenceByNode.get(node.nodeId);
                return (
                  <button
                    type="button"
                    className={`erdos-proof-index__node erdos-proof-index__node--${status}${selectedNodeId === node.nodeId ? " is-active" : ""}${frontierNodes.has(node.nodeId) ? " is-frontier" : ""}`}
                    onClick={() => selectNode(node.nodeId)}
                    key={node.nodeId}
                  >
                    <span className="erdos-proof-index__number">{node.nodeId}</span>
                    <span>
                      <strong>{node.label}</strong>
                      <small>{nodeStatusLabel(status)} · Part {paperPartForNode(node.nodeId)?.roman}</small>
                      {evidence?.ctIds.length ? (
                        <span className="erdos-proof-index__cts">
                          {evidence.ctIds.slice(0, 3).map((ctId) => <b key={ctId}>{ctId}</b>)}
                        </span>
                      ) : null}
                    </span>
                  </button>
                );
              })}
              {!filteredNodes.length ? <p className="empty-copy">No paper nodes match these filters.</p> : null}
            </div>
            <section className="erdos-proof-index__tours">
              <span className="eyebrow">Guided framework slices</span>
              {ERDOS_FRAMEWORK_GUIDED_TOURS.map((tour) => (
                <button
                  type="button"
                  onClick={() => {
                    setActiveTourId(tour.tourId);
                    selectNode(tour.nodeIds[0]);
                  }}
                  key={tour.tourId}
                >
                  <strong>{tour.title}</strong>
                  <small>Nodes {tour.nodeIds.map((nodeId) => `[${nodeId}]`).join("–")}</small>
                </button>
              ))}
            </section>
          </aside>

          <section className="erdos-map-canvas">
            {selectedEdge ? (
              <aside className="erdos-edge-inspector" aria-live="polite">
                <span>Selected paper dependency</span>
                <strong>[{selectedEdge.source}] → [{selectedEdge.target}]</strong>
                <button type="button" onClick={() => selectNode(selectedEdge.source)}>Inspect source</button>
                <button type="button" onClick={() => selectNode(selectedEdge.target)}>Inspect target</button>
              </aside>
            ) : null}
            <ErdosProofFlowDiagram
              manuscript={manuscript}
              activeNodeId={selectedNodeId}
              onNodeSelect={selectNode}
              onEdgeSelect={(source, target) => setSelectedEdge({ source, target })}
              showSelectionDetails={false}
              defaultView="compare"
            />
          </section>

          <section className="erdos-map-story">
            <ErdosNodeStory
              nodeId={selectedNodeId}
              status={selectedNodeId === null ? "paper" : storyStatus(rawSelectedStatus, selectedNodeId)}
              isFrontier={selectedNodeId !== null && frontierNodes.has(selectedNodeId)}
              manuscript={manuscript}
              proofSteps={selectedProofSteps}
              obligations={selectedObligations}
              stages={selectedStages}
              bindings={selectedEvidence ? [...selectedEvidence.bindings] : []}
              declarations={example.declarations}
              onDeclarationSelect={selectDeclaration}
              onStageSelect={(stage) => selectStage(stage, false)}
            />
          </section>

          <section className="erdos-source-companion">
            <header>
              <div>
                <span className="eyebrow">Exact paper ↔ Lean companion</span>
                <h2>Inspect the implementation, not just the status</h2>
              </div>
              {selectedProofSteps.length > 1 ? (
                <label>
                  <span>Proof step for node [{selectedNodeId}]</span>
                  <select
                    value={activeProofStep?.stepId ?? ""}
                    onChange={(event) => {
                      const next = selectedProofSteps.find((step) => step.stepId === event.target.value);
                      setActiveProofStepId(event.target.value);
                      setActiveDeclarationId(next ? firstDeclaration([next]) : null);
                    }}
                  >
                    {selectedProofSteps.map((step) => (
                      <option value={step.stepId} key={step.stepId}>{step.title}</option>
                    ))}
                  </select>
                </label>
              ) : null}
            </header>
            <LeanSourceViewer
              sources={example.sources}
              declarations={example.declarations}
              activeDeclarationId={activeDeclarationId}
              onDeclarationSelect={selectDeclaration}
              manuscript={manuscript}
              proofStep={activeProofStep}
              paperEnabled
            />
          </section>
        </main>
      ) : null}

      {activeTab === "impact" ? (
        <main className="erdos-tab-panel">
          <ErdosFrameworkImpact
            response={response}
            leverage={leverage}
            tours={impactTours}
            activeTourId={activeTourId}
            selectedNodeId={selectedNodeId}
            onTourSelect={(tourId) => setActiveTourId(tourId)}
            onStageSelect={(stage) => selectStage(stage)}
          />
        </main>
      ) : null}

      {activeTab === "history" ? (
        <main className="erdos-tab-panel">
          {historyError ? (
            <aside className="erdos-history-error" role="status">
              The proof map is available, but its engineering history could not be loaded: {historyError}
            </aside>
          ) : null}
          <ErdosHistoryView
            snapshots={displayedHistory}
            activeSnapshotId={activeSnapshotId}
            onSnapshotSelect={setActiveSnapshotId}
          />
        </main>
      ) : null}

      {activeTab === "method" ? (
        <main className="erdos-tab-panel erdos-reading-guide">
          <header>
            <span className="eyebrow">Interpretation contract</span>
            <h2>How to read this living proof</h2>
            <p>Proof truth, implementation telemetry, and claims about framework leverage are deliberately separate.</p>
          </header>
          <div>
            <article>
              <span>01</span>
              <h3>Read color as proof status</h3>
              <p><b>Green</b> means the direct NodeX.lean file is kernel checked. <b>Yellow</b> means that direct node file exists but is not checked. White means no direct node file.</p>
            </article>
            <article>
              <span>02</span>
              <h3>Read orange as frontier</h3>
              <p>Orange identifies a no-file node whose direct parent is green, so it is dependency-ready to expand next.</p>
            </article>
            <article>
              <span>03</span>
              <h3>Audit the speedup claim through reuse</h3>
              <p>The impact view counts explicit bindings, typed transitions, framework-owned declarations, automated links, and finite-work statements. These are reproducible facts—not a fabricated estimate of programmer-hours saved.</p>
            </article>
            <article>
              <span>04</span>
              <h3>Follow the causal chain</h3>
              <p>For a selected node, separate what the Erdős proof supplies from what Core, Graph, CT profiles, and Routes supply, then inspect the exact declarations establishing the result.</p>
            </article>
            <article>
              <span>05</span>
              <h3>Compare with the unchanged paper topology</h3>
              <p>The 157 nodes and their directed edges are the reference diagram. The side-by-side view links implementation evidence to that stable structure instead of redrawing the proof around the code.</p>
            </article>
            <article>
              <span>06</span>
              <h3>Treat history as engineering telemetry</h3>
              <p>Each append-only snapshot records artifact hashes and raw progress/reuse counters. The current kernel-checked descriptor remains the sole source of proof status.</p>
            </article>
          </div>
        </main>
      ) : null}
    </div>
  );
}
