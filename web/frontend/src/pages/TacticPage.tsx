import { useEffect, useMemo, useState } from "react";
import { Link, useParams } from "react-router-dom";

import { fetchFramework, fetchTactic } from "../api";
import { AppHeader } from "../components/AppHeader";
import { ErrorState, LoadingState } from "../components/LoadState";
import { GraphCanvas } from "../components/GraphCanvas";
import { Inspector } from "../components/Inspector";
import { RouteList } from "../components/RouteList";
import { machineGraphElements } from "../graph-data";
import type {
  FrameworkResponse,
  SelectedGraphElement,
  TacticResponse,
} from "../types";

export function TacticPage() {
  const { tacticId = "" } = useParams();
  const [response, setResponse] = useState<TacticResponse | null>(null);
  const [framework, setFramework] = useState<FrameworkResponse | null>(null);
  const [selected, setSelected] = useState<SelectedGraphElement | null>(null);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    const controller = new AbortController();
    setResponse(null);
    setSelected(null);
    setError(null);
    Promise.all([
      fetchTactic(tacticId.toUpperCase(), controller.signal),
      fetchFramework(controller.signal),
    ])
      .then(([tactic, catalog]) => {
        setResponse(tactic);
        setFramework(catalog);
      })
      .catch((reason: unknown) => {
        if (!controller.signal.aborted) {
          setError(reason instanceof Error ? reason.message : String(reason));
        }
      });
    return () => controller.abort();
  }, [tacticId]);

  const elements = useMemo(
    () => (response ? machineGraphElements(response) : []),
    [response],
  );

  if (error) return <main className="standalone-state"><ErrorState message={error} /></main>;
  if (!response || !framework) {
    return <main className="standalone-state"><LoadingState label={`Loading ${tacticId.toUpperCase()}…`} /></main>;
  }

  const tactic = response.tactic;
  const node =
    selected?.group === "node"
      ? tactic.nodes.find((candidate) => candidate.nodeId === selected.id)
      : undefined;
  const edge =
    selected?.group === "edge"
      ? tactic.transitions.find((candidate) => candidate.edgeId === selected.id)
      : undefined;
  const entry = tactic.nodes.find((candidate) => candidate.nodeKind === "entry")?.nodeId;

  return (
    <div className="app-page app-page--tactic">
      <AppHeader verification={response.verification} compact />
      <div className="tactic-titlebar">
        <div>
          <nav className="breadcrumbs" aria-label="Breadcrumb">
            <Link to="/framework">Framework</Link><span>/</span><strong>{tactic.tacticId}</strong>
          </nav>
          <h1><span>{tactic.tacticId}</span>{tactic.title}</h1>
        </div>
        <div className="titlebar-stats">
          <span><strong>{tactic.nodes.length}</strong> nodes</span>
          <span><strong>{tactic.transitions.length}</strong> edges</span>
          <span><strong>{tactic.terminals.length}</strong> terminals</span>
        </div>
      </div>

      <main className="tactic-workspace">
        <aside className="tactic-nav" aria-label="Closure tactics">
          <div className="tactic-nav__heading">
            <span className="eyebrow">Catalog</span>
            <strong>CT1–CT17</strong>
          </div>
          <nav>
            {framework.tactics.map((item) => (
              <Link
                to={`/ct/${item.tacticId}`}
                className={item.tacticId === tactic.tacticId ? "is-active" : ""}
                key={item.tacticId}
                title={item.title}
              >
                <span>{item.tacticId}</span>
                <small>{item.title}</small>
              </Link>
            ))}
          </nav>
        </aside>

        <section className="machine-panel">
          <div className="machine-panel__heading">
            <div>
              <span className="eyebrow">Typed execution graph</span>
              <strong>{selected ? selected.id : "Select a node or edge to inspect it"}</strong>
            </div>
            <div className="legend" aria-label="Node legend">
              <span><i className="legend__entry" /> entry</span>
              <span><i className="legend__compute" /> computation</span>
              <span><i className="legend__residual" /> residual</span>
              <span><i className="legend__certificate" /> certificate</span>
            </div>
          </div>
          <GraphCanvas
            mode="machine"
            elements={elements}
            entryId={entry}
            selectedId={selected?.id}
            onSelect={setSelected}
          />
          <div className="machine-routes">
            <span className="eyebrow">Cross-CT routes</span>
            <RouteList inbound={response.inboundRoutes} outbound={response.outboundRoutes} />
          </div>
        </section>

        <Inspector
          key={selected?.id ?? tactic.tacticId}
          tactic={tactic}
          node={node}
          edge={edge}
          inboundRoutes={response.inboundRoutes}
          outboundRoutes={response.outboundRoutes}
        />
      </main>
    </div>
  );
}
