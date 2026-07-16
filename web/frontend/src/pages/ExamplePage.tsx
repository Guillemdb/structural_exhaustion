import { useEffect, useMemo, useRef, useState } from "react";
import { Link, useParams } from "react-router-dom";

import { fetchExample } from "../api";
import { AppHeader } from "../components/AppHeader";
import { ErdosProofFlowDiagram } from "../components/ErdosProofFlowDiagram";
import { ExampleInspector } from "../components/ExampleInspector";
import { GraphCanvas } from "../components/GraphCanvas";
import { LeanSourceViewer } from "../components/LeanSourceViewer";
import { ErrorState, LoadingState } from "../components/LoadState";
import { ProofRoadmap } from "../components/ProofRoadmap";
import { exampleGraphElements } from "../graph-data";
import type {
  ExampleLink,
  ExampleResponse,
  ExampleStage,
  ExampleWorkflow,
  SelectedGraphElement,
} from "../types";

function firstDeclarationForSelection(
  workflow: ExampleWorkflow,
  selection: SelectedGraphElement | null,
  bindings: ExampleResponse["example"]["interfaceBindings"],
): string | null {
  if (!selection) return workflow.stages[0]?.primaryDeclarationId ?? null;
  let stages: ExampleStage[] = [];
  if (selection.group === "node") {
    const stage = workflow.stages.find((candidate) => candidate.stageId === selection.id);
    if (stage) stages = [stage];
  } else {
    const link = workflow.links.find((candidate) => candidate.linkId === selection.id);
    if (link) {
      stages = [link.sourceStageId, link.targetStageId]
        .map((id) => workflow.stages.find((candidate) => candidate.stageId === id))
        .filter((stage): stage is ExampleStage => Boolean(stage));
    }
  }
  for (const stage of stages) {
    const direct = stage.primaryDeclarationId ?? stage.evidenceDeclarationIds[0];
    if (direct) return direct;
    const bound = bindings.find(
      (binding) =>
        binding.workflowId === workflow.workflowId && binding.stageId === stage.stageId,
    )?.problemDeclarationId;
    if (bound) return bound;
  }
  return null;
}

export function ExampleWorkspace({
  response,
  mode = "generic",
}: {
  response: ExampleResponse;
  mode?: "generic" | "erdos";
}) {
  const { example } = response;
  const isErdos = mode === "erdos";
  const pendingNavigation = useRef<{
    stageId: string;
    declarationId: string | null;
    proofStepId: string;
    proofNodeId?: number;
  } | null>(null);
  const [activeWorkflowId, setActiveWorkflowId] = useState(example.workflows[0]?.workflowId ?? "");
  const [selected, setSelected] = useState<SelectedGraphElement | null>(null);
  const [activeDeclarationId, setActiveDeclarationId] = useState<string | null>(null);
  const [activeProofStepId, setActiveProofStepId] = useState<string | null>(null);
  const [activeProofNodeId, setActiveProofNodeId] = useState<number | null>(null);
  const workflow = example.workflows.find(
    (candidate) => candidate.workflowId === activeWorkflowId,
  ) ?? example.workflows[0];

  useEffect(() => {
    if (!workflow) return;
    const pending = pendingNavigation.current;
    const targetStage = pending
      ? workflow.stages.find((stage) => stage.stageId === pending.stageId)
      : undefined;
    const initialStage = targetStage ?? workflow.stages[0];
    const initial = initialStage
      ? {
          id: initialStage.stageId,
          group: "node" as const,
          data: { id: initialStage.stageId },
        }
      : null;
    setSelected(initial);
    setActiveDeclarationId(
      targetStage && pending?.declarationId
        ? pending.declarationId
        : firstDeclarationForSelection(workflow, initial, example.interfaceBindings),
    );
    const initialProofStep = targetStage && pending
      ? example.manuscript?.proofSteps.find((step) => step.stepId === pending.proofStepId)
      : example.manuscript?.proofSteps.find(
          (step) => step.stageId === initialStage?.stageId,
        );
    setActiveProofStepId(initialProofStep?.stepId ?? null);
    setActiveProofNodeId(
      pending?.proofNodeId
        ?? initialProofStep?.manuscriptRefs.flatMap((reference) => reference.nodeIds).at(0)
        ?? null,
    );
    pendingNavigation.current = null;
  }, [activeWorkflowId, example.interfaceBindings, example.manuscript, workflow]);

  const activeProofStep = example.manuscript?.proofSteps.find(
    (step) => step.stepId === activeProofStepId,
  );

  const elements = useMemo(
    () => workflow ? exampleGraphElements(workflow) : [],
    [workflow],
  );

  if (!workflow) {
    return <main className="standalone-state"><ErrorState message="This example has no workflows." /></main>;
  }

  const selectedStage: ExampleStage | undefined = selected?.group === "node"
    ? workflow.stages.find((candidate) => candidate.stageId === selected.id)
    : undefined;
  const selectedLink: ExampleLink | undefined = selected?.group === "edge"
    ? workflow.links.find((candidate) => candidate.linkId === selected.id)
    : undefined;
  const handleGraphSelect = (next: SelectedGraphElement | null) => {
    setSelected(next);
    const proofStep = next?.group === "node"
      ? example.manuscript?.proofSteps.find((step) => step.stageId === next.id)
      : undefined;
    setActiveProofStepId(proofStep?.stepId ?? null);
    setActiveProofNodeId(
      proofStep?.manuscriptRefs.flatMap((reference) => reference.nodeIds).at(0) ?? null,
    );
    const declarationId = firstDeclarationForSelection(
      workflow,
      next,
      example.interfaceBindings,
    );
    if (declarationId) setActiveDeclarationId(declarationId);
  };

  const handleProofStepSelect = (stepId: string) => {
    const step = example.manuscript?.proofSteps.find((candidate) => candidate.stepId === stepId);
    if (!step) return;
    setActiveProofStepId(stepId);
    setActiveProofNodeId(
      step.manuscriptRefs.flatMap((reference) => reference.nodeIds).at(0) ?? null,
    );
    if (!step.stageId) {
      setSelected(null);
      setActiveDeclarationId(null);
      return;
    }
    const owner = example.workflows.find((candidate) =>
      candidate.stages.some((stage) => stage.stageId === step.stageId));
    if (owner && owner.workflowId !== workflow.workflowId) {
      const ownerStage = owner.stages.find((stage) => stage.stageId === step.stageId);
      pendingNavigation.current = {
        stageId: step.stageId,
        declarationId: ownerStage
          ? firstDeclarationForSelection(owner, {
              id: ownerStage.stageId,
              group: "node",
              data: { id: ownerStage.stageId },
            }, example.interfaceBindings)
          : null,
        proofStepId: step.stepId,
      };
      setActiveWorkflowId(owner.workflowId);
      return;
    }
    const stage = workflow.stages.find((candidate) => candidate.stageId === step.stageId);
    if (!stage) return;
    const next = {
      id: stage.stageId,
      group: "node" as const,
      data: { id: stage.stageId },
    };
    setSelected(next);
    setActiveDeclarationId(
      firstDeclarationForSelection(workflow, next, example.interfaceBindings),
    );
  };

  const handleProofNodeSelect = (nodeId: number) => {
    setActiveProofNodeId(nodeId);
    const step = example.manuscript?.proofSteps.find((candidate) =>
      candidate.manuscriptRefs.some((reference) => reference.nodeIds.includes(nodeId)));
    if (step) {
      handleProofStepSelect(step.stepId);
      if (pendingNavigation.current?.proofStepId === step.stepId) {
        pendingNavigation.current.proofNodeId = nodeId;
      }
      setActiveProofNodeId(nodeId);
      return;
    }
    setActiveProofStepId(null);
    setSelected(null);
    setActiveDeclarationId(null);
  };

  const handleDeclarationSelect = (declarationId: string | null) => {
    setActiveDeclarationId(declarationId);
    if (!declarationId || !example.manuscript) return;
    const step = example.manuscript.proofSteps.find((candidate) =>
      candidate.declarationGroups.some((group) =>
        group.declarationIds.includes(declarationId)));
    if (!step) return;
    setActiveProofStepId(step.stepId);
    setActiveProofNodeId(
      step.manuscriptRefs.flatMap((reference) => reference.nodeIds).at(0) ?? null,
    );
    if (!step.stageId) return;
    const owner = example.workflows.find((candidate) =>
      candidate.stages.some((stage) => stage.stageId === step.stageId));
    if (owner && owner.workflowId !== workflow.workflowId) {
      pendingNavigation.current = {
        stageId: step.stageId,
        declarationId,
        proofStepId: step.stepId,
      };
      setActiveWorkflowId(owner.workflowId);
      return;
    }
    setSelected({
      id: step.stageId,
      group: "node",
      data: { id: step.stageId },
    });
  };

  return (
    <div className={`app-page app-page--example ${isErdos ? "app-page--erdos" : ""}`}>
      <AppHeader
        verification={response.verification}
        artifactWarnings={response.artifactWarnings}
        compact
      />
      <div className="example-titlebar">
        <div>
          <nav className="breadcrumbs" aria-label="Breadcrumb">
            {isErdos ? (
              <><Link to="/framework">Framework</Link><span>/</span><strong>Erdős–Gyárfás Problem 64</strong></>
            ) : (
              <><Link to="/examples">Examples</Link><span>/</span><strong>{example.title}</strong></>
            )}
          </nav>
          <h1>{isErdos ? "Erdős–Gyárfás Problem 64" : example.title}</h1>
          <p>{example.summary}</p>
        </div>
        <div className="example-titlebar__meta">
          <span className={`proof-status proof-status--${example.proofStatus}`}>
            {example.proofStatus}
          </span>
          <div className="ct-chip-list" aria-label="Closure tactics used">
            {example.tacticIds.map((tacticId) => (
              <Link to={`/ct/${tacticId}`} key={tacticId}>{tacticId}</Link>
            ))}
          </div>
        </div>
      </div>
      {isErdos && example.manuscript ? (
        <section className="erdos-progress" aria-label="Erdős–Gyárfás formalization progress">
          <div title="Unique labeled theorems, lemmas, propositions, corollaries, claims, definitions, and remarks referenced by implemented Lean proof steps, out of all such objects in the TeX manuscript.">
            <strong>{example.manuscript.coverage.verifiedMathematicalObjects}/{example.manuscript.coverage.totalMathematicalObjects}</strong>
            <span>paper objects mapped to verified Lean</span>
          </div>
          <div title="Unique bracketed node IDs referenced by implemented Lean proof steps, out of all numbered nodes in the Chapter 1 proof-flow diagram.">
            <strong>{example.manuscript.coverage.verifiedDiagramNodes}/{example.manuscript.coverage.totalDiagramNodes}</strong>
            <span>Chapter 1 flow nodes verified</span>
          </div>
          <div title="Manuscript-indexed workflow steps whose status is implemented and whose Lean stage is present.">
            <strong>{example.manuscript.coverage.verifiedWorkflowSteps}</strong>
            <span>verified workflow steps</span>
          </div>
        </section>
      ) : null}
      {example.proofStatus === "partial" ? (
        <div className={`example-status-banner example-status-banner--${example.proofStatus}`}>
          {isErdos
            ? "This is a kernel-checked partial formalization. Implemented and future paper stages are distinguished explicitly; the workflow does not claim the full conjecture."
            : "This generated descriptor marks the example as a partial proof slice; the graph does not imply a completed theorem."}
        </div>
      ) : null}

      <main className="example-workspace">
        <aside className="workflow-nav" aria-label="Example workflows">
          <div className="workflow-nav__heading">
            <span className="eyebrow">{isErdos ? "EG proof stages" : "Proof views"}</span>
            <strong>
              {isErdos && example.manuscript
                ? `${example.manuscript.proofSteps.length} indexed steps`
                : `${example.workflows.length} workflow${example.workflows.length === 1 ? "" : "s"}`}
            </strong>
          </div>
          <nav>
            {example.workflows.map((candidate) => (
              <button
                type="button"
                className={candidate.workflowId === workflow.workflowId ? "is-active" : ""}
                onClick={() => setActiveWorkflowId(candidate.workflowId)}
                key={candidate.workflowId}
              >
                <span>{candidate.title}</span>
                <small>{candidate.purpose}</small>
                <i className={`proof-status proof-status--${candidate.completion}`}>
                  {candidate.completion}
                </i>
              </button>
            ))}
          </nav>
          <div className="workflow-purpose">
            <span className="eyebrow">Purpose</span>
            <p>{workflow.purpose}</p>
          </div>
          {example.manuscript ? (
            <ProofRoadmap
              manuscript={example.manuscript}
              activeStepId={activeProofStepId}
              onSelect={handleProofStepSelect}
            />
          ) : null}
        </aside>

        <section className="example-diagram-panel">
          <div className="machine-panel__heading">
            <div>
              <span className="eyebrow">{isErdos ? "Verified EG proof flow" : "Composition graph"}</span>
              <strong>{isErdos ? "Complete Chapter 1 dependency map" : workflow.title}</strong>
            </div>
            {isErdos ? (
              <div className="proof-flow-legend" aria-label="Proof formalization legend">
                <span><i className="proof-flow-legend__verified" /> formalized in Lean</span>
                <span><i className="proof-flow-legend__closed" /> unconditionally closed branch</span>
                <span><i className="proof-flow-legend__partial" /> partially formalized</span>
                <span><i className="proof-flow-legend__next" /> next frontier</span>
                <span><i className="proof-flow-legend__paper" /> paper only</span>
              </div>
            ) : (
              <div className="example-legend" aria-label="Composition relationship legend">
                <span><i className="example-legend__route" /> registered route</span>
                <span><i className="example-legend__proof" /> proof data</span>
                <span><i className="example-legend__validation" /> validation</span>
              </div>
            )}
          </div>
          {isErdos && example.manuscript ? (
            <ErdosProofFlowDiagram
              manuscript={example.manuscript}
              activeNodeId={activeProofNodeId}
              onNodeSelect={handleProofNodeSelect}
            />
          ) : (
            <GraphCanvas
              mode="example"
              elements={elements}
              selectedId={selected?.id}
              onSelect={handleGraphSelect}
            />
          )}
          <ExampleInspector
            workflow={workflow}
            stage={selectedStage}
            link={selectedLink}
            bindings={example.interfaceBindings}
            declarations={example.declarations}
            proofStep={activeProofStep}
            activeDeclarationId={activeDeclarationId}
            onDeclarationSelect={handleDeclarationSelect}
          />
        </section>

        <LeanSourceViewer
          sources={example.sources}
          declarations={example.declarations}
          activeDeclarationId={activeDeclarationId}
          onDeclarationSelect={handleDeclarationSelect}
          manuscript={isErdos ? example.manuscript : null}
          proofStep={isErdos ? activeProofStep : undefined}
          paperEnabled={isErdos && Boolean(example.manuscript)}
        />
      </main>
    </div>
  );
}

export function ExamplePage() {
  const { exampleId = "" } = useParams();
  const [response, setResponse] = useState<ExampleResponse | null>(null);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    const controller = new AbortController();
    setResponse(null);
    setError(null);
    fetchExample(exampleId, controller.signal)
      .then(setResponse)
      .catch((reason: unknown) => {
        if (!controller.signal.aborted) {
          setError(reason instanceof Error ? reason.message : String(reason));
        }
      });
    return () => controller.abort();
  }, [exampleId]);

  if (error) return <main className="standalone-state"><ErrorState message={error} /></main>;
  if (!response) return <main className="standalone-state"><LoadingState label="Loading example…" /></main>;
  return <ExampleWorkspace response={response} />;
}
