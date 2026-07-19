import { Link } from "react-router-dom";

import type {
  ExampleDeclaration,
  ExampleDeclarationRole,
  ExampleInterfaceBinding,
  ExampleLink,
  ExampleProofStep,
  ExampleStage,
  ExampleWorkflow,
} from "../types";
import { MathFormula } from "./MathFormula";

const relationDescriptions: Record<ExampleLink["kind"], string> = {
  registeredRoute:
    "A route registered by the earlier structural-exhaustion contract; it maps to the corresponding transition profile.",
  registeredTransition:
    "A transition profile registered and checked by the structural-exhaustion framework.",
  frameworkComposition: "Problem-specific orchestration between framework components.",
  proofData: "The earlier stage supplies proved data consumed by the later stage.",
  validation: "A closure tactic validates a certificate or result built elsewhere.",
  scheduleAudit: "This execution audits a schedule; it is not itself consumed as proof data.",
  sharedProblem: "These stages share a problem or profile without forming an execution pipeline.",
};

const roleLabels: Record<ExampleDeclarationRole, string> = {
  mathematicalDefinition: "Mathematical definition",
  semanticTheorem: "Semantic theorem",
  encodingBridge: "Encoding bridge",
  tacticExecution: "Tactic execution",
  executionAudit: "Execution audit",
  soundnessTotality: "Soundness / totality",
  workBound: "Work bound",
  compositionProvenance: "Composition / provenance",
  frameworkInterface: "Framework interface",
  externalTheorem: "External theorem",
  fixture: "Fixture",
};

const correspondenceLabels: Record<ExampleProofStep["correspondence"], string> = {
  exact: "Exact",
  equivalentEncoding: "Equivalent encoding",
  specialization: "Reusable specialization",
  composite: "Composite correspondence",
  support: "Implementation support",
  partial: "Partial / future",
};

function ProofStepCompanion({
  step,
  activeDeclaration,
}: {
  step: ExampleProofStep;
  activeDeclaration?: ExampleDeclaration;
}) {
  const group = activeDeclaration
    ? step.declarationGroups.find((candidate) =>
        candidate.declarationIds.includes(activeDeclaration.declarationId))
    : undefined;

  return (
    <div className="proof-companion">
      <div className="proof-companion__status">
        <span className={`implementation-status implementation-status--${step.status}`}>
          {step.status === "notStarted" ? "not started" : step.status}
        </span>
        <span className={`correspondence-chip correspondence-chip--${step.correspondence}`}>
          {correspondenceLabels[step.correspondence]}
        </span>
      </div>
      <section>
        <h3>Plain language</h3>
        <p>{step.plainExplanation}</p>
      </section>
      <section>
        <h3>Formal mathematics</h3>
        <MathFormula value={step.formalStatement} label={`${step.title} mathematical statement`} />
      </section>
      <section>
        <h3>Paper correspondence</h3>
        {step.manuscriptRefs.length ? (
          <ul className="manuscript-ref-list">
            {step.manuscriptRefs.map((reference) => (
              <li key={reference.label}>
                <code>{reference.label}</code>
                <span>{reference.title}</span>
                {reference.nodeIds.length ? (
                  <small>nodes {reference.nodeIds.map((node) => `[${node}]`).join(", ")}</small>
                ) : null}
              </li>
            ))}
          </ul>
        ) : (
          <p className="empty-copy">Implementation support; no manuscript claim is assigned.</p>
        )}
      </section>
      {activeDeclaration && group ? (
        <section className="active-declaration-explanation">
          <div>
            <h3>Selected Lean declaration</h3>
            <span className={`declaration-role declaration-role--${group.role}`}>
              {roleLabels[group.role]}
            </span>
          </div>
          <code>{activeDeclaration.name}</code>
          <p>{group.explanation}</p>
          <details>
            <summary>Exact kernel-checked type</summary>
            <pre>{activeDeclaration.type}</pre>
          </details>
        </section>
      ) : null}
      <section className="proof-companion__audit">
        <div>
          <h3>Faithfulness and scope</h3>
          <p>{step.scopeNotes}</p>
        </div>
        <div>
          <h3>Finite work audit</h3>
          <p>{step.workBound}</p>
        </div>
      </section>
    </div>
  );
}

function DeclarationButtons({
  declarationIds,
  declarations,
  onSelect,
}: {
  declarationIds: string[];
  declarations: ExampleDeclaration[];
  onSelect: (declarationId: string) => void;
}) {
  const evidence = declarationIds
    .map((id) => declarations.find((declaration) => declaration.declarationId === id))
    .filter((declaration): declaration is ExampleDeclaration => Boolean(declaration));

  if (!evidence.length) return <p className="empty-copy">No focused declaration is attached.</p>;

  return (
    <ul className="example-declaration-list">
      {evidence.map((declaration) => (
        <li key={declaration.declarationId}>
          <button type="button" onClick={() => onSelect(declaration.declarationId)}>
            <code>{declaration.name}</code>
            <span>{declaration.kind} · lines {declaration.startLine}–{declaration.endLine}</span>
          </button>
        </li>
      ))}
    </ul>
  );
}

export function ExampleInspector({
  workflow,
  stage,
  link,
  bindings,
  declarations,
  proofStep,
  activeDeclarationId,
  onDeclarationSelect,
}: {
  workflow: ExampleWorkflow;
  stage?: ExampleStage;
  link?: ExampleLink;
  bindings: ExampleInterfaceBinding[];
  declarations: ExampleDeclaration[];
  proofStep?: ExampleProofStep;
  activeDeclarationId: string | null;
  onDeclarationSelect: (declarationId: string) => void;
}) {
  const activeDeclaration = declarations.find(
    (declaration) => declaration.declarationId === activeDeclarationId,
  );

  if (stage) {
    const stageBindings = bindings.filter(
      (binding) =>
        binding.workflowId === workflow.workflowId && binding.stageId === stage.stageId,
    );
    const declarationIds = Array.from(
      new Set([
        stage.primaryDeclarationId,
        ...stage.evidenceDeclarationIds,
        ...stageBindings.flatMap((binding) => [
          binding.problemDeclarationId,
          binding.frameworkDeclarationId,
        ]),
      ]),
    );

    return (
      <article className="example-inspector" aria-live="polite">
        <div className="example-inspector__heading">
          <span className={`kind-chip kind-chip--${stage.kind}`}>{stage.kind}</span>
          <h2>{stage.title}</h2>
          <p>{stage.summary}</p>
          {stage.tacticId ? (
            <Link className="ct-open-link" to={`/ct/${stage.tacticId}`}>
              Open {stage.tacticId} machine <span aria-hidden="true">→</span>
            </Link>
          ) : null}
        </div>
        {proofStep ? (
          <ProofStepCompanion step={proofStep} activeDeclaration={activeDeclaration} />
        ) : null}
        <section>
          <h3>Problem ↔ framework interface</h3>
          {stageBindings.length ? (
            <div className="binding-list">
              {stageBindings.map((binding) => (
                <div key={binding.bindingId}>
                  <strong>{binding.role}</strong>
                  <p>{binding.summary}</p>
                  <dl>
                    <div>
                      <dt>Problem code</dt>
                      <dd><code>{declarations.find((item) => item.declarationId === binding.problemDeclarationId)?.name ?? binding.problemDeclarationId}</code></dd>
                    </div>
                    <div>
                      <dt>Framework API</dt>
                      <dd><code>{declarations.find((item) => item.declarationId === binding.frameworkDeclarationId)?.name ?? binding.frameworkDeclarationId}</code></dd>
                    </div>
                  </dl>
                </div>
              ))}
            </div>
          ) : <p className="empty-copy">No explicit interface binding is attached to this stage.</p>}
        </section>
        <section>
          <h3>Kernel-checked declarations</h3>
          <DeclarationButtons
            declarationIds={declarationIds}
            declarations={declarations}
            onSelect={onDeclarationSelect}
          />
        </section>
      </article>
    );
  }

  if (proofStep) {
    return (
      <article className="example-inspector" aria-live="polite">
        <div className="example-inspector__heading">
          <span className="eyebrow">Proof roadmap</span>
          <h2>{proofStep.title}</h2>
        </div>
        <ProofStepCompanion step={proofStep} activeDeclaration={activeDeclaration} />
      </article>
    );
  }

  if (link) {
    const source = workflow.stages.find((candidate) => candidate.stageId === link.sourceStageId);
    const target = workflow.stages.find((candidate) => candidate.stageId === link.targetStageId);
    return (
      <article className="example-inspector" aria-live="polite">
        <div className="example-inspector__heading">
          <span className={`kind-chip kind-chip--${link.kind}`}>{link.kind}</span>
          <h2>{link.label}</h2>
          <p>{link.summary}</p>
        </div>
        <section>
          <h3>Relationship semantics</h3>
          <p>{relationDescriptions[link.kind]}</p>
          <div className="example-link-endpoints">
            <span>{source?.title ?? link.sourceStageId}</span>
            <span aria-hidden="true">→</span>
            <span>{target?.title ?? link.targetStageId}</span>
          </div>
          {link.transitionProfileId ? (
            <code className="transition-profile-id">{link.transitionProfileId}</code>
          ) : null}
        </section>
        {link.automationDeclarationIds.length ? (
          <section>
            <h3>Framework automation</h3>
            <p>
              This transition is executed or certified by the following reusable
              framework declaration{link.automationDeclarationIds.length === 1 ? "" : "s"}.
            </p>
            <DeclarationButtons
              declarationIds={link.automationDeclarationIds}
              declarations={declarations}
              onSelect={onDeclarationSelect}
            />
          </section>
        ) : null}
        <section>
          <h3>Kernel-checked evidence</h3>
          <DeclarationButtons
            declarationIds={link.evidenceDeclarationIds}
            declarations={declarations}
            onSelect={onDeclarationSelect}
          />
        </section>
      </article>
    );
  }

  return (
    <article className="example-inspector" aria-live="polite">
      <div className="example-inspector__heading">
        <span className="eyebrow">Workflow</span>
        <h2>{workflow.title}</h2>
        <p>{workflow.summary}</p>
      </div>
      <section>
        <h3>Purpose</h3>
        <p>{workflow.purpose}</p>
      </section>
    </article>
  );
}
