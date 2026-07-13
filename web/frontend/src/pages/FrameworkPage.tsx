import { useEffect, useMemo, useState } from "react";
import { Link, useNavigate } from "react-router-dom";

import { fetchFramework } from "../api";
import { AppHeader } from "../components/AppHeader";
import { ErrorState, LoadingState } from "../components/LoadState";
import { GraphCanvas } from "../components/GraphCanvas";
import { frameworkGraphElements, routeLabel } from "../graph-data";
import type {
  FrameworkResponse,
  SelectedGraphElement,
  TacticSummary,
} from "../types";

function TacticCard({ tactic }: { tactic: TacticSummary }) {
  return (
    <Link className="tactic-card" to={`/ct/${tactic.tacticId}`}>
      <span className="tactic-card__id">{tactic.tacticId}</span>
      <h3>{tactic.title}</h3>
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
  const [error, setError] = useState<string | null>(null);
  const [query, setQuery] = useState("");
  const [selected, setSelected] = useState<SelectedGraphElement | null>(null);
  const navigate = useNavigate();

  useEffect(() => {
    const controller = new AbortController();
    fetchFramework(controller.signal)
      .then(setFramework)
      .catch((reason: unknown) => {
        if (!controller.signal.aborted) {
          setError(reason instanceof Error ? reason.message : String(reason));
        }
      });
    return () => controller.abort();
  }, []);

  const filtered = useMemo(() => {
    if (!framework) return [];
    const needle = query.trim().toLowerCase();
    if (!needle) return framework.tactics;
    return framework.tactics.filter(
      (tactic) =>
        tactic.tacticId.toLowerCase().includes(needle) ||
        tactic.title.toLowerCase().includes(needle),
    );
  }, [framework, query]);

  if (error) return <main className="standalone-state"><ErrorState message={error} /></main>;
  if (!framework) return <main className="standalone-state"><LoadingState /></main>;

  const selectedTactic =
    selected?.group === "node"
      ? framework.tactics.find((tactic) => tactic.tacticId === selected.id)
      : undefined;
  const selectedRoute =
    selected?.group === "edge"
      ? framework.routes.find((route) => route.routeId === selected.id)
      : undefined;
  const sourceKind = String(framework.catalog.sourceOfTruth.kind ?? "compiled framework");

  return (
    <div className="app-page app-page--overview">
      <AppHeader verification={framework.verification} />
      <main>
        <section className="hero">
          <div>
            <span className="eyebrow">Lean-derived proof architecture</span>
            <h1>Explore the closure tactics as executable machines.</h1>
            <p>
              Navigate CT1–CT17, inspect typed transitions, and follow the routes
              registered by the structural-exhaustion framework.
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
          <div><strong>{framework.totals.routes}</strong><span>registered routes</span></div>
          <div><strong>{framework.totals.manualObligations}</strong><span>manual obligations</span></div>
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
              {filtered.map((tactic) => <TacticCard tactic={tactic} key={tactic.tacticId} />)}
            </div>
            {!filtered.length ? <p className="empty-search">No tactic matches “{query}”.</p> : null}
          </div>

          <div className="route-panel">
            <div className="section-heading">
              <div>
                <span className="eyebrow">Residual routing</span>
                <h2>Registered CT routes</h2>
              </div>
              <span className="formal-badge">Lean proved</span>
            </div>
            <GraphCanvas
              mode="framework"
              elements={frameworkGraphElements(framework)}
              selectedId={selected?.id}
              onSelect={setSelected}
            />
            <div className="route-selection" aria-live="polite">
              {selectedTactic ? (
                <>
                  <span className="eyebrow">{selectedTactic.tacticId}</span>
                  <strong>{selectedTactic.title}</strong>
                  <button type="button" onClick={() => navigate(`/ct/${selectedTactic.tacticId}`)}>
                    Open machine
                  </button>
                </>
              ) : null}
              {selectedRoute ? (
                <>
                  <span className="eyebrow">{selectedRoute.selectionClass} route</span>
                  <strong>{selectedRoute.sourceTacticId} → {selectedRoute.targetTacticId}</strong>
                  <code>{routeLabel(selectedRoute)}</code>
                  <button type="button" onClick={() => navigate(`/ct/${selectedRoute.targetTacticId}`)}>
                    Follow to {selectedRoute.targetTacticId}
                  </button>
                </>
              ) : null}
              {!selected ? (
                <p>Select a tactic or dashed route to inspect the framework connection.</p>
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
