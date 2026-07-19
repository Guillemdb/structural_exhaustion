import type { ExampleResponse, ExampleStage, ExampleWorkflow } from "../types";
import type { ErdosFrameworkLeverageSummary } from "../erdos-proof-leverage";

export interface ErdosImpactTour {
  tourId: string;
  title: string;
  summary: string;
  stageIds: string[];
  authorSupplied: string;
  frameworkSupplied: string;
  verifiedOutcome: string;
  tacticIds?: string[];
}

export interface ErdosFrameworkImpactProps {
  response: ExampleResponse;
  tours?: ErdosImpactTour[];
  activeTourId?: string | null;
  selectedNodeId?: number | null;
  leverage?: ErdosFrameworkLeverageSummary;
  onTourSelect?: (tourId: string) => void;
  onStageSelect?: (stage: ExampleStage, workflow: ExampleWorkflow) => void;
}

function distinct(values: Array<string | null | undefined>): string[] {
  return Array.from(new Set(values.filter((value): value is string => Boolean(value))));
}

/**
 * Presents auditable framework reuse without turning reuse counts into an
 * unsupported claim about elapsed time or proof completion.
 */
export function ErdosFrameworkImpact({
  response,
  tours = [],
  activeTourId = null,
  selectedNodeId = null,
  leverage,
  onTourSelect,
  onStageSelect,
}: ErdosFrameworkImpactProps) {
  const { example } = response;
  const links = example.workflows.flatMap((workflow) => workflow.links);
  const frameworkBackedLinks = links.filter(
    (link) =>
      link.automationDeclarationIds.length > 0 || Boolean(link.transitionProfileId),
  );
  const transitionProfileIds = distinct(
    frameworkBackedLinks.map((link) => link.transitionProfileId),
  );
  const automationDeclarationIds = distinct(
    frameworkBackedLinks.flatMap((link) => link.automationDeclarationIds),
  );
  const frameworkDeclarationIds = distinct([
    ...automationDeclarationIds,
    ...example.interfaceBindings.map((binding) => binding.frameworkDeclarationId),
  ]);

  const stageOwners = new Map<string, { stage: ExampleStage; workflow: ExampleWorkflow }>();
  for (const workflow of example.workflows) {
    for (const stage of workflow.stages) {
      stageOwners.set(stage.stageId, { stage, workflow });
    }
  }

  const cards = leverage ? [
    {
      label: "Problem ↔ framework bindings",
      value: leverage.counts.interfaceBindings,
      explanation: "Explicit bridges between Erdős-specific declarations and reusable framework APIs.",
    },
    {
      label: "Framework-automated transitions",
      value: leverage.counts.linksWithAutomation,
      explanation: "Workflow transitions naming kernel-checked framework automation evidence.",
    },
    {
      label: "Registered transition profiles",
      value: leverage.counts.registeredTransitions,
      explanation: "Distinct registered transition profiles reused by this formalization.",
    },
    {
      label: "Framework declarations reused",
      value: leverage.counts.frameworkOwnedDeclarations,
      explanation: "Distinct declarations owned by StructuralExhaustion namespaces in the compiled artifact.",
    },
    {
      label: "Audited finite-work statements",
      value: leverage.counts.workBounds,
      explanation: "Proof steps with an explicit finite-search or no-new-scan work statement.",
    },
  ] : [
    {
      label: "Problem ↔ framework bindings",
      value: example.interfaceBindings.length,
      explanation: "Explicit bridges between Erdős-specific declarations and reusable framework APIs.",
    },
    {
      label: "Framework-backed transitions",
      value: frameworkBackedLinks.length,
      explanation: "Workflow transitions carrying a profile or named automation evidence.",
    },
    {
      label: "Registered transition profiles",
      value: transitionProfileIds.length,
      explanation: "Distinct registered transition profiles reused by this formalization.",
    },
    {
      label: "Framework declarations reused",
      value: frameworkDeclarationIds.length,
      explanation: "Distinct framework interfaces and automation declarations named by the artifact.",
    },
  ];

  return (
    <section className="erdos-framework-impact" aria-labelledby="erdos-framework-impact-title">
      <header className="erdos-framework-impact__heading">
        <div>
          <span className="eyebrow">Verified framework leverage</span>
          <h2 id="erdos-framework-impact-title">What the framework contributes</h2>
        </div>
        {selectedNodeId !== null ? (
          <span className="erdos-framework-impact__selection">Paper node [{selectedNodeId}] selected</span>
        ) : null}
      </header>

      <p className="erdos-framework-impact__scope-note">
        These counts describe declarations and transition profiles recorded by the compiled
        artifact. They are evidence of reuse, not a percentage of the proof automated and not an
        estimate of time saved.
      </p>

      <dl className="erdos-impact-metrics" aria-label="Auditable framework reuse">
        {cards.map((card) => (
          <div className="erdos-impact-metric" key={card.label}>
            <dt>{card.label}</dt>
            <dd>{card.value}</dd>
            <small>{card.explanation}</small>
          </div>
        ))}
      </dl>

      {leverage ? (
        <section className="erdos-impact-ownership" aria-labelledby="erdos-impact-ownership-title">
          <div>
            <span className="eyebrow">Compiled declaration ownership</span>
            <h3 id="erdos-impact-ownership-title">The implementation boundary is visible</h3>
            <p>
              The author-owned side supplies Erdős-specific mathematics; the framework-owned side
              supplies reusable machinery. External declarations remain a separate trust boundary.
            </p>
          </div>
          <dl>
            <div><dt>Author-owned</dt><dd>{leverage.counts.authorOwnedDeclarations}</dd></div>
            <div><dt>Framework-owned</dt><dd>{leverage.counts.frameworkOwnedDeclarations}</dd></div>
            <div><dt>External</dt><dd>{leverage.counts.externalDeclarations}</dd></div>
          </dl>
        </section>
      ) : null}

      <div className="erdos-impact-tours">
        <header>
          <span className="eyebrow">Guided proof slices</span>
          <h3>Follow author input through reusable machinery</h3>
        </header>
        {tours.length ? (
          <div className="erdos-impact-tour-list">
            {tours.map((tour) => {
              const stages = tour.stageIds
                .map((stageId) => stageOwners.get(stageId))
                .filter((owner): owner is { stage: ExampleStage; workflow: ExampleWorkflow } =>
                  Boolean(owner));
              return (
                <article
                  className={`erdos-impact-tour${tour.tourId === activeTourId ? " is-active" : ""}`}
                  key={tour.tourId}
                >
                  <header>
                    <div>
                      <h4>{tour.title}</h4>
                      <p>{tour.summary}</p>
                    </div>
                    {onTourSelect ? (
                      <button type="button" onClick={() => onTourSelect(tour.tourId)}>
                        Explore this slice
                      </button>
                    ) : null}
                  </header>
                  {tour.tacticIds?.length ? (
                    <ul className="erdos-impact-tour__tactics" aria-label={`${tour.title} tactics`}>
                      {tour.tacticIds.map((tacticId) => <li key={tacticId}>{tacticId}</li>)}
                    </ul>
                  ) : null}
                  <div className="erdos-impact-tour__causal-chain">
                    <section>
                      <h5>Author supplied</h5>
                      <p>{tour.authorSupplied}</p>
                    </section>
                    <span aria-hidden="true">→</span>
                    <section>
                      <h5>Framework supplied</h5>
                      <p>{tour.frameworkSupplied}</p>
                    </section>
                    <span aria-hidden="true">→</span>
                    <section>
                      <h5>Verified outcome</h5>
                      <p>{tour.verifiedOutcome}</p>
                    </section>
                  </div>
                  {stages.length ? (
                    <ol className="erdos-impact-tour__stages" aria-label={`${tour.title} Lean stages`}>
                      {stages.map(({ stage, workflow }) => (
                        <li key={stage.stageId}>
                          {onStageSelect ? (
                            <button type="button" onClick={() => onStageSelect(stage, workflow)}>
                              <span>{stage.title}</span>
                              <small>{workflow.title}</small>
                            </button>
                          ) : (
                            <span>{stage.title}</span>
                          )}
                        </li>
                      ))}
                    </ol>
                  ) : null}
                </article>
              );
            })}
          </div>
        ) : (
          <p className="empty-copy">
            Guided slices will appear when curated author-input and framework-output evidence is attached.
          </p>
        )}
      </div>
    </section>
  );
}
