import type { ExampleManuscript } from "../types";

export function ProofRoadmap({
  manuscript,
  activeStepId,
  onSelect,
}: {
  manuscript: ExampleManuscript;
  activeStepId: string | null;
  onSelect: (stepId: string) => void;
}) {
  const { coverage } = manuscript;
  return (
    <section className="proof-roadmap" aria-label="Manuscript implementation roadmap">
      <div className="proof-roadmap__heading">
        <span className="eyebrow">Paper ↔ Lean</span>
        <strong>{coverage.implementedSteps}/{coverage.totalSteps} steps implemented</strong>
        <small>
          {coverage.explainedDeclarations}/{coverage.displayedDeclarations} displayed declarations explained
        </small>
      </div>
      <ol>
        {manuscript.proofSteps.map((step) => (
          <li key={step.stepId}>
            <button
              type="button"
              className={step.stepId === activeStepId ? "is-active" : ""}
              onClick={() => onSelect(step.stepId)}
            >
              <i className={`roadmap-dot roadmap-dot--${step.status}`} aria-hidden="true" />
              <span>
                <strong>{step.title}</strong>
                <small>
                  {step.manuscriptRefs.flatMap((reference) => reference.nodeIds)
                    .map((node) => `[${node}]`).join(" ") || "support"}
                </small>
              </span>
              <em>{step.status === "notStarted" ? "not started" : step.status}</em>
            </button>
          </li>
        ))}
      </ol>
      <footer>
        <span>{manuscript.title}</span>
        <code>{manuscript.path}</code>
      </footer>
    </section>
  );
}
