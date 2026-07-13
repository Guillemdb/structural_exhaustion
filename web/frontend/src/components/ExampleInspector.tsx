import { Link } from "react-router-dom";

import type {
  ExampleDeclaration,
  ExampleInterfaceBinding,
  ExampleLink,
  ExampleStage,
  ExampleWorkflow,
} from "../types";

const relationDescriptions: Record<ExampleLink["kind"], string> = {
  registeredRoute: "A route registered and checked by the structural-exhaustion framework.",
  frameworkComposition: "Problem-specific orchestration between framework components.",
  proofData: "The earlier stage supplies proved data consumed by the later stage.",
  validation: "A closure tactic validates a certificate or result built elsewhere.",
  scheduleAudit: "This execution audits a schedule; it is not itself consumed as proof data.",
  sharedProblem: "These stages share a problem or profile without forming an execution pipeline.",
};

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
  onDeclarationSelect,
}: {
  workflow: ExampleWorkflow;
  stage?: ExampleStage;
  link?: ExampleLink;
  bindings: ExampleInterfaceBinding[];
  declarations: ExampleDeclaration[];
  onDeclarationSelect: (declarationId: string) => void;
}) {
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
          {link.routeId ? <code className="route-id">{link.routeId}</code> : null}
        </section>
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
