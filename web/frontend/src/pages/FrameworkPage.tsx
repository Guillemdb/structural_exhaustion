import { useEffect, useMemo, useState } from "react";
import { Link, useNavigate } from "react-router-dom";

import { fetchDocumentation, fetchFramework } from "../api";
import { useDocumentationAudience } from "../audience";
import { AppHeader } from "../components/AppHeader";
import { ErrorState, LoadingState } from "../components/LoadState";
import { GraphCanvas } from "../components/GraphCanvas";
import { frameworkGraphElements, transitionProfileLabel } from "../graph-data";
import { exampleDestination } from "../routes";
import type {
  FrameworkResponse,
  DocumentationResponse,
  DocumentationTacticGuide,
  SelectedGraphElement,
  TacticSummary,
} from "../types";

function TacticCard({ tactic, guide, leanView }: { tactic: TacticSummary; guide?: DocumentationTacticGuide; leanView: boolean }) {
  return (
    <Link className="tactic-card" to={`/ct/${tactic.tacticId}`}>
      <span className="tactic-card__id">{tactic.tacticId}</span>
      <h3>{tactic.title}</h3>
      {guide ? <p>{leanView ? guide.leanEntry : guide.useWhen}</p> : null}
      <div className="tactic-card__counts">
        <span>{tactic.nodeCount} nodes</span>
        <span>{tactic.terminalCount} terminals</span>
        <span>{tactic.residualCount} residuals</span>
      </div>
      <span className="tactic-card__open">Explore machine <span aria-hidden="true">→</span></span>
    </Link>
  );
}

export function FrameworkPage() {
  const [framework, setFramework] = useState<FrameworkResponse | null>(null);
  const [documentation, setDocumentation] = useState<DocumentationResponse | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [query, setQuery] = useState("");
  const [selected, setSelected] = useState<SelectedGraphElement | null>(null);
  const navigate = useNavigate();
  const { audience } = useDocumentationAudience();

  useEffect(() => {
    const controller = new AbortController();
    Promise.all([fetchFramework(controller.signal), fetchDocumentation(controller.signal)])
      .then(([catalog, docs]) => {
        setFramework(catalog);
        setDocumentation(docs);
      })
      .catch((reason: unknown) => {
        if (!controller.signal.aborted) {
          setError(reason instanceof Error ? reason.message : String(reason));
        }
      });
    return () => controller.abort();
  }, []);

  const filtered = useMemo(() => {
    if (!framework || !documentation) return [];
    const needle = query.trim().toLowerCase();
    if (!needle) return framework.tactics;
    return framework.tactics.filter((tactic) => {
      const guide = documentation.tacticGuides.find((item) => item.tacticId === tactic.tacticId);
      return [tactic.tacticId, tactic.title, guide?.role ?? "", guide?.useWhen ?? "", guide?.leanEntry ?? ""]
        .some((value) => value.toLowerCase().includes(needle));
    });
  }, [documentation, framework, query]);

  if (error) return <main className="standalone-state"><ErrorState message={error} /></main>;
  if (!framework || !documentation) return <main className="standalone-state"><LoadingState /></main>;

  const publicFramework = {
    ...framework,
    implementedTransitions: framework.implementedTransitions.filter(
      (transition) => transition.exampleId !== "erdos-64",
    ),
  };

  const selectedTactic =
    selected?.group === "node"
      ? framework.tactics.find((tactic) => tactic.tacticId === selected.id)
      : undefined;
  const selectedProfile =
    selected?.group === "edge"
      ? framework.transitionProfiles.find((profile) => profile.profileId === selected.id)
      : undefined;
  const selectedTransition =
    selected?.group === "edge"
      ? publicFramework.implementedTransitions.find(
          (transition) => transition.transitionId === selected.id,
        )
      : undefined;
  const sourceKind = String(framework.catalog.sourceOfTruth.kind ?? "compiled framework");

  return (
    <div className="app-page app-page--overview">
      <AppHeader
        verification={framework.verification}
        artifactWarnings={framework.artifactWarnings}
        showAudienceToggle
      />
      <main>
        <section className="hero">
          <div>
            <span className="eyebrow">Closure tactic library</span>
            <h1>Choose the finite proof move that matches your branch.</h1>
            <p>
              Navigate CT1–CT17 by mathematical role, inspect their executable
              machines, and follow verified transition profiles between residuals.
            </p>
          </div>
          <div className="catalog-stamp">
            <span>Catalog {framework.catalog.schemaVersion}</span>
            <code>{framework.catalog.catalogHash.slice(0, 12)}</code>
            <small>{sourceKind.replaceAll("_", " ")}</small>
          </div>
        </section>

        <section className="stat-strip" aria-label="Framework totals">
          <div><strong>{framework.totals.tactics}</strong><span>tactics</span></div>
          <div><strong>{framework.totals.nodes}</strong><span>nodes</span></div>
          <div><strong>{framework.totals.transitions}</strong><span>typed transitions</span></div>
          <div><strong>{framework.totals.terminals}</strong><span>terminals</span></div>
          <div>
            <strong>{framework.totals.transitionFamilies}</strong>
            <span>transition families</span>
          </div>
          <div>
            <strong>{framework.totals.transitionProfiles}</strong>
            <span>transition profiles</span>
          </div>
          <div><strong>{publicFramework.implementedTransitions.length}</strong><span>example CT links</span></div>
        </section>

        <section className="overview-grid">
          <div className="catalog-panel">
            <div className="section-heading">
              <div>
                <span className="eyebrow">Machine catalog</span>
                <h2>Choose a closure tactic</h2>
              </div>
              <label className="search-box">
                <span className="sr-only">Search tactics</span>
                <input
                  type="search"
                  value={query}
                  onChange={(event) => setQuery(event.target.value)}
                  placeholder="Search CTs…"
                />
              </label>
            </div>
            <div className="tactic-grid">
              {filtered.map((tactic) => (
                <TacticCard
                  tactic={tactic}
                  guide={documentation.tacticGuides.find((guide) => guide.tacticId === tactic.tacticId)}
                  leanView={audience === "leanUser"}
                  key={tactic.tacticId}
                />
              ))}
            </div>
            {!filtered.length ? <p className="empty-search">No tactic matches “{query}”.</p> : null}
          </div>

          <div className="transition-panel">
            <div className="section-heading">
              <div>
                <span className="eyebrow">Cross-CT architecture</span>
                <h2>Registered and implemented transitions</h2>
              </div>
              <span className={`formal-badge formal-badge--${framework.exampleVerification.state}`}>
                Examples {framework.exampleVerification.state}
              </span>
            </div>
            <div className="framework-legend" aria-label="CT transition legend">
              <span>
                <i className="framework-legend__transition-profile" />
                Registered transition profile
              </span>
              <span>
                <i className="framework-legend__transition-use" />
                Implemented profile use
              </span>
              <span><i className="framework-legend__implemented" />Implemented proof composition</span>
              <span><i className="framework-legend__audit" />Implemented schedule audit</span>
            </div>
            <GraphCanvas
              mode="framework"
              elements={frameworkGraphElements(publicFramework)}
              selectedId={selected?.id}
              onSelect={setSelected}
            />
            <div className="transition-selection" aria-live="polite">
              {selectedTactic ? (
                <>
                  <span className="eyebrow">{selectedTactic.tacticId}</span>
                  <strong>{selectedTactic.title}</strong>
                  <button type="button" onClick={() => navigate(`/ct/${selectedTactic.tacticId}`)}>
                    Open machine
                  </button>
                </>
              ) : null}
              {selectedProfile ? (
                <>
                  <span className="eyebrow">
                    {selectedProfile.selectionClass} transition profile
                  </span>
                  <strong>
                    {selectedProfile.sourceTacticId} → {selectedProfile.targetTacticId}
                  </strong>
                  <code>{transitionProfileLabel(selectedProfile)}</code>
                  <small className="transition-selection__provenance">
                    Full-ledger executor
                  </small>
                  <code>{selectedProfile.advanceExecutor}</code>
                  <button
                    type="button"
                    onClick={() => navigate(`/ct/${selectedProfile.targetTacticId}`)}
                  >
                    Follow to {selectedProfile.targetTacticId}
                  </button>
                </>
              ) : null}
              {selectedTransition ? (
                <>
                  <span className="eyebrow">
                    Implemented {selectedTransition.relationshipKind.replace(/([A-Z])/g, " $1").toLowerCase()}
                  </span>
                  <span className="framework-automated-badge">Framework automated</span>
                  <strong>
                    {selectedTransition.sourceTacticId} → {selectedTransition.targetTacticId}
                  </strong>
                  <code>{selectedTransition.label}</code>
                  <p className="transition-selection__summary">{selectedTransition.summary}</p>
                  <small className="transition-selection__provenance">
                    {selectedTransition.exampleTitle} · {selectedTransition.workflowTitle}
                  </small>
                  <dl className="implemented-transition-map">
                    <div>
                      <dt>Source stage</dt>
                      <dd>{selectedTransition.sourceStageTitle}</dd>
                      <code>{selectedTransition.sourceDeclarationId}</code>
                    </div>
                    <div>
                      <dt>Target stage</dt>
                      <dd>{selectedTransition.targetStageTitle}</dd>
                      <code>{selectedTransition.targetDeclarationId}</code>
                    </div>
                  </dl>
                  <details className="implemented-transition-evidence" open>
                    <summary>
                      Framework automation ({selectedTransition.automationDeclarationIds.length})
                    </summary>
                    <ul>
                      {selectedTransition.automationDeclarationIds.map((declarationId) => (
                        <li key={declarationId}><code>{declarationId}</code></li>
                      ))}
                    </ul>
                  </details>
                  <details className="implemented-transition-evidence">
                    <summary>
                      Lean evidence ({selectedTransition.evidenceDeclarationIds.length})
                    </summary>
                    {selectedTransition.evidenceDeclarationIds.length ? (
                      <ul>
                        {selectedTransition.evidenceDeclarationIds.map((declarationId) => (
                          <li key={declarationId}><code>{declarationId}</code></li>
                        ))}
                      </ul>
                    ) : (
                      <p>The compiled source and target stage declarations provide the evidence boundary.</p>
                    )}
                  </details>
                  <button
                    className="transition-selection__proof-button"
                    type="button"
                    onClick={() => navigate(exampleDestination(selectedTransition.exampleId))}
                  >
                    Inspect proof workflow
                  </button>
                </>
              ) : null}
              {!selected ? (
                <p>
                  Select a CT or connection. Purple dashed edges are reusable registered
                  transition profiles; example-backed edges record transitions actually used
                  by compiled proofs.
                </p>
              ) : null}
            </div>
          </div>
        </section>
      </main>
      <footer className="app-footer">
        <span>Structural Exhaustion</span>
        <span>All mathematical data is projected from the compiled Lean catalog.</span>
      </footer>
    </div>
  );
}
