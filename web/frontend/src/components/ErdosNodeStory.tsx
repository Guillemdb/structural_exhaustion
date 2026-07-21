import type {
  ExampleDeclaration,
  ExampleDeclarationGroup,
  ExampleInterfaceBinding,
  ExampleManuscript,
  ExampleNodeObligation,
  ExampleProofStep,
  ExampleStage,
} from "../types";
import { MathFormula } from "./MathFormula";

export type ErdosNodeStoryStatus = "verified" | "closed" | "partial" | "paper";

export interface ErdosNodeStoryProps {
  nodeId: number | null;
  status: ErdosNodeStoryStatus;
  isFrontier?: boolean;
  manuscript: ExampleManuscript;
  proofSteps: ExampleProofStep[];
  obligations: ExampleNodeObligation[];
  stages: ExampleStage[];
  bindings: ExampleInterfaceBinding[];
  declarations: ExampleDeclaration[];
  onDeclarationSelect?: (declarationId: string) => void;
  onStageSelect?: (stage: ExampleStage) => void;
}

const statusLabels: Record<ErdosNodeStoryStatus, string> = {
  verified: "Checked NodeX.lean file",
  closed: "Checked terminal NodeX.lean file",
  partial: "Unchecked NodeX.lean file",
  paper: "No direct node file",
};

const authorRoles = new Set<ExampleDeclarationGroup["role"]>([
  "mathematicalDefinition",
  "semanticTheorem",
  "encodingBridge",
  "fixture",
]);

const externalRoles = new Set<ExampleDeclarationGroup["role"]>(["externalTheorem"]);

const frameworkRoles = new Set<ExampleDeclarationGroup["role"]>([
  "tacticExecution",
  "executionAudit",
  "soundnessTotality",
  "workBound",
  "compositionProvenance",
  "frameworkInterface",
]);

function uniqueGroups(groups: ExampleDeclarationGroup[]): ExampleDeclarationGroup[] {
  const seen = new Set<string>();
  return groups.filter((group) => {
    if (seen.has(group.groupId)) return false;
    seen.add(group.groupId);
    return true;
  });
}

function declarationName(
  declarationId: string,
  declarations: ExampleDeclaration[],
): string {
  return declarations.find((declaration) => declaration.declarationId === declarationId)?.name
    ?? declarationId;
}

function EvidenceGroups({
  groups,
  declarations,
  onDeclarationSelect,
}: {
  groups: ExampleDeclarationGroup[];
  declarations: ExampleDeclaration[];
  onDeclarationSelect?: (declarationId: string) => void;
}) {
  if (!groups.length) return null;
  return (
    <ul className="erdos-node-story__evidence-groups">
      {groups.map((group) => (
        <li key={group.groupId}>
          <strong>{group.title}</strong>
          <p>{group.explanation}</p>
          {group.declarationIds.length ? (
            <ul className="erdos-node-story__declarations">
              {group.declarationIds.map((declarationId) => (
                <li key={declarationId}>
                  {onDeclarationSelect ? (
                    <button type="button" onClick={() => onDeclarationSelect(declarationId)}>
                      <code>{declarationName(declarationId, declarations)}</code>
                    </button>
                  ) : (
                    <code>{declarationName(declarationId, declarations)}</code>
                  )}
                </li>
              ))}
            </ul>
          ) : null}
        </li>
      ))}
    </ul>
  );
}

/**
 * Explains a selected paper node as a causal chain. Its status is supplied by
 * the caller so the component cannot promote a yellow node to green.
 */
export function ErdosNodeStory({
  nodeId,
  status,
  isFrontier = false,
  manuscript,
  proofSteps,
  obligations,
  stages,
  bindings,
  declarations,
  onDeclarationSelect,
  onStageSelect,
}: ErdosNodeStoryProps) {
  if (nodeId === null) {
    return (
      <aside className="erdos-node-story erdos-node-story--empty" aria-label="Selected proof-node story">
        <span className="eyebrow">Paper ↔ Lean ↔ framework</span>
        <h2>Select a proof node</h2>
        <p>Choose a node in the proof map to inspect its exact paper claim and verified Lean evidence.</p>
      </aside>
    );
  }

  const groups = uniqueGroups(proofSteps.flatMap((step) => step.declarationGroups));
  const authorGroups = groups.filter((group) => authorRoles.has(group.role));
  const frameworkGroups = groups.filter((group) => frameworkRoles.has(group.role));
  const externalGroups = groups.filter((group) => externalRoles.has(group.role));
  const refs = proofSteps.flatMap((step) =>
    step.manuscriptRefs.filter((reference) => reference.nodeIds.includes(nodeId)));
  const uniqueRefs = refs.filter((reference, index) =>
    refs.findIndex((candidate) => candidate.label === reference.label) === index);
  const nodeBindings = bindings.filter((binding) =>
    stages.some((stage) => stage.stageId === binding.stageId));

  return (
    <aside
      className={`erdos-node-story erdos-node-story--${status}`}
      aria-labelledby="erdos-node-story-title"
      aria-live="polite"
    >
      <header className="erdos-node-story__heading">
        <div>
          <span className="eyebrow">Paper ↔ Lean ↔ framework</span>
          <h2 id="erdos-node-story-title">Paper node [{nodeId}]</h2>
        </div>
        <div className="erdos-node-story__state">
          <span className={`erdos-node-status erdos-node-status--${status}`}>{statusLabels[status]}</span>
          {isFrontier ? <span className="erdos-node-frontier">Frontier</span> : null}
        </div>
      </header>

      <section className="erdos-node-story__paper">
        <h3>Paper claim</h3>
        {uniqueRefs.length ? (
          <ul className="erdos-node-story__manuscript-refs">
            {uniqueRefs.map((reference) => (
              <li key={reference.label}>
                <code>{reference.label}</code>
                <span>{reference.title}</span>
              </li>
            ))}
          </ul>
        ) : (
          <p className="empty-copy">No manuscript fragment is indexed for this paper node.</p>
        )}
        {proofSteps.map((step) => (
          <article className="erdos-node-story__proof-step" key={step.stepId}>
            <h4>{step.title}</h4>
            <p>{step.plainExplanation}</p>
            <MathFormula value={step.formalStatement} label={`${step.title} formal statement`} />
            <small>{step.scopeNotes}</small>
          </article>
        ))}
        {!proofSteps.length ? (
          <p className="empty-copy">This paper node does not yet have an indexed Lean proof step.</p>
        ) : null}
        <footer>
          <span>{manuscript.title}</span>
          <code>{manuscript.path}</code>
        </footer>
      </section>

      <section className="erdos-node-story__author">
        <h3>Author supplied</h3>
        <p>The problem-specific definitions, semantic bridges, and mathematical facts written for this proof.</p>
        {stages.length ? (
          <ul className="erdos-node-story__stages">
            {stages.map((stage) => (
              <li key={stage.stageId}>
                {onStageSelect ? (
                  <button type="button" onClick={() => onStageSelect(stage)}>
                    <strong>{stage.title}</strong>
                    <small>{stage.summary}</small>
                  </button>
                ) : (
                  <><strong>{stage.title}</strong><small>{stage.summary}</small></>
                )}
              </li>
            ))}
          </ul>
        ) : null}
        <EvidenceGroups
          groups={authorGroups}
          declarations={declarations}
          onDeclarationSelect={onDeclarationSelect}
        />
        {!stages.length && !authorGroups.length ? (
          <p className="empty-copy">No author-input evidence is attached to this node yet.</p>
        ) : null}
      </section>

      <section className="erdos-node-story__framework">
        <h3>Framework supplied</h3>
        <p>The reusable interfaces, executions, audits, transitions, and work bounds consumed by this node.</p>
        {nodeBindings.length ? (
          <ul className="erdos-node-story__bindings">
            {nodeBindings.map((binding) => (
              <li key={binding.bindingId}>
                <strong>{binding.role}</strong>
                <p>{binding.summary}</p>
                <div>
                  <span>Problem</span>
                  <code>{declarationName(binding.problemDeclarationId, declarations)}</code>
                  <span aria-hidden="true">→</span>
                  <span>Framework</span>
                  <code>{declarationName(binding.frameworkDeclarationId, declarations)}</code>
                </div>
              </li>
            ))}
          </ul>
        ) : null}
        <EvidenceGroups
          groups={frameworkGroups}
          declarations={declarations}
          onDeclarationSelect={onDeclarationSelect}
        />
        {!nodeBindings.length && !frameworkGroups.length ? (
          <p className="empty-copy">No framework-contribution evidence is attached to this node yet.</p>
        ) : null}
      </section>

      {externalGroups.length ? (
        <section className="erdos-node-story__external">
          <h3>External trust boundary</h3>
          <p>
            Imported mathematical facts remain explicit and are not counted as author- or
            framework-owned acceleration.
          </p>
          <EvidenceGroups
            groups={externalGroups}
            declarations={declarations}
            onDeclarationSelect={onDeclarationSelect}
          />
        </section>
      ) : null}

      <section className="erdos-node-story__result">
        <h3>Verified result and remaining work</h3>
        {obligations.length ? (
          <ul className="erdos-node-story__obligations">
            {obligations.map((obligation) => (
              <li
                className={`erdos-node-obligation erdos-node-obligation--${obligation.status}`}
                key={obligation.obligationId}
              >
                <span>{obligation.status}</span>
                <strong>{obligation.title}</strong>
                <p>{obligation.statement}</p>
              </li>
            ))}
          </ul>
        ) : (
          <p className="empty-copy">No per-node obligation ledger is attached to this node.</p>
        )}
        {proofSteps.some((step) => step.workBound) ? (
          <details>
            <summary>Finite work audit</summary>
            <ul>
              {proofSteps.map((step) => <li key={step.stepId}>{step.workBound}</li>)}
            </ul>
          </details>
        ) : null}
      </section>
    </aside>
  );
}
