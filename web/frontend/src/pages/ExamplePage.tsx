import { useEffect, useMemo, useRef, useState } from "react";
import { Link, useParams } from "react-router-dom";

import { fetchExample } from "../api";
import { AppHeader } from "../components/AppHeader";
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

function ExampleWorkspace({ response }: { response: ExampleResponse }) {
  const { example } = response;
  const pendingNavigation = useRef<{
    stageId: string;
    declarationId: string | null;
    proofStepId: string;
  } | null>(null);
  const [activeWorkflowId, setActiveWorkflowId] = useState(example.workflows[0]?.workflowId ?? "");
  const [selected, setSelected] = useState<SelectedGraphElement | null>(null);
  const [activeDeclarationId, setActiveDeclarationId] = useState<string | null>(null);
  const [activeProofStepId, setActiveProofStepId] = useState<string | null>(null);
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
    setActiveProofStepId(
      targetStage && pending
        ? pending.proofStepId
        : example.manuscript?.proofSteps.find(
            (step) => step.stageId === initialStage?.stageId,
          )?.stepId ?? null,
    );
    pendingNavigation.current = null;
  }, [activeWorkflowId, example.interfaceBindings, example.manuscript, workflow]);

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
  const activeProofStep = example.manuscript?.proofSteps.find(
    (step) => step.stepId === activeProofStepId,
  );

  const handleGraphSelect = (next: SelectedGraphElement | null) => {
    setSelected(next);
    setActiveProofStepId(
      next?.group === "node"
        ? example.manuscript?.proofSteps.find((step) => step.stageId === next.id)?.stepId ?? null
        : null,
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

  const handleDeclarationSelect = (declarationId: string | null) => {
    setActiveDeclarationId(declarationId);
    if (!declarationId || !example.manuscript) return;
    const step = example.manuscript.proofSteps.find((candidate) =>
      candidate.declarationGroups.some((group) =>
        group.declarationIds.includes(declarationId)));
    if (!step) return;
    setActiveProofStepId(step.stepId);
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
    <div className="app-page app-page--example">
      <AppHeader verification={response.verification} compact />
      <div className="example-titlebar">
        <div>
          <nav className="breadcrumbs" aria-label="Breadcrumb">
            <Link to="/examples">Examples</Link><span>/</span><strong>{example.title}</strong>
          </nav>
          <h1>{example.title}</h1>
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
      {example.proofStatus === "partial" ? (
        <div className={`example-status-banner example-status-banner--${example.proofStatus}`}>
          This generated descriptor marks the example as a partial proof slice; the graph does not imply a completed theorem.
        </div>
      ) : null}

      <main className="example-workspace">
        <aside className="workflow-nav" aria-label="Example workflows">
          <div className="workflow-nav__heading">
            <span className="eyebrow">Proof views</span>
            <strong>{example.workflows.length} workflow{example.workflows.length === 1 ? "" : "s"}</strong>
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
              <span className="eyebrow">Composition graph</span>
              <strong>{workflow.title}</strong>
            </div>
            <div className="example-legend" aria-label="Composition relationship legend">
              <span><i className="example-legend__route" /> registered route</span>
              <span><i className="example-legend__proof" /> proof data</span>
              <span><i className="example-legend__validation" /> validation</span>
            </div>
          </div>
          <GraphCanvas
            mode="example"
            elements={elements}
            selectedId={selected?.id}
            onSelect={handleGraphSelect}
          />
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
