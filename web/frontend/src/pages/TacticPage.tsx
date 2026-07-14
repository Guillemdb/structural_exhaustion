import { useEffect, useMemo, useRef, useState } from "react";
import { Link, useNavigate, useParams } from "react-router-dom";

import { fetchFramework, fetchTactic, fetchTacticInternals } from "../api";
import { AppHeader } from "../components/AppHeader";
import { ErrorState, LoadingState } from "../components/LoadState";
import { GraphCanvas } from "../components/GraphCanvas";
import { Inspector } from "../components/Inspector";
import { NodeInternalsInspector } from "../components/NodeInternalsInspector";
import { RouteList } from "../components/RouteList";
import { expandedMachineGraphElements, machineGraphElements } from "../graph-data";
import type {
  FrameworkResponse,
  SelectedGraphElement,
  TacticResponse,
  TacticInternalsResponse,
} from "../types";

export function TacticPage() {
  const { tacticId = "" } = useParams();
  const navigate = useNavigate();
  const [response, setResponse] = useState<TacticResponse | null>(null);
  const [framework, setFramework] = useState<FrameworkResponse | null>(null);
  const [selected, setSelected] = useState<SelectedGraphElement | null>(null);
  const [showOutboundRoutes, setShowOutboundRoutes] = useState(false);
  const [internals, setInternals] = useState<TacticInternalsResponse | null>(null);
  const [expandedNodeId, setExpandedNodeId] = useState<string | null>(null);
  const [expandedDeclarations, setExpandedDeclarations] = useState<Set<string>>(
    () => new Set(),
  );
  const [internalsLoading, setInternalsLoading] = useState(false);
  const [internalsError, setInternalsError] = useState<string | null>(null);
  const [routesBeforeInternals, setRoutesBeforeInternals] = useState(false);
  const internalsRequest = useRef<AbortController | null>(null);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    const controller = new AbortController();
    setResponse(null);
    setSelected(null);
    setInternals(null);
    setExpandedNodeId(null);
    setExpandedDeclarations(new Set());
    setInternalsError(null);
    setInternalsLoading(false);
    internalsRequest.current?.abort();
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
    return () => {
      controller.abort();
      internalsRequest.current?.abort();
    };
  }, [tacticId]);

  useEffect(() => {
    if (response && response.outboundRoutes.length === 0) {
      setShowOutboundRoutes(false);
    }
  }, [response]);

  const elements = useMemo(() => {
    if (!response) return [];
    if (expandedNodeId && internals) {
      return expandedMachineGraphElements(
        response,
        internals,
        expandedNodeId,
        expandedDeclarations,
      );
    }
    return machineGraphElements(response, {
          includeOutboundRoutes: showOutboundRoutes,
          targetTactics: framework?.tactics,
    });
  }, [expandedDeclarations, expandedNodeId, framework, internals, response, showOutboundRoutes]);

  const openInternals = async (nodeId: string) => {
    if (!response || internalsLoading) return;
    const restoreRoutes = showOutboundRoutes;
    setRoutesBeforeInternals(restoreRoutes);
    setShowOutboundRoutes(false);
    setInternalsError(null);
    setInternalsLoading(true);
    try {
      let detail = internals;
      if (!detail) {
        internalsRequest.current?.abort();
        const controller = new AbortController();
        internalsRequest.current = controller;
        detail = await fetchTacticInternals(response.tactic.tacticId, controller.signal);
      }
      if (detail.catalogHash !== response.catalogHash) {
        throw new Error("The low-level artifact does not match the displayed catalog.");
      }
      setInternals(detail);
      setExpandedDeclarations(new Set());
      setExpandedNodeId(nodeId);
    } catch (reason: unknown) {
      if (!(reason instanceof DOMException && reason.name === "AbortError")) {
        setInternalsError(reason instanceof Error ? reason.message : String(reason));
        setShowOutboundRoutes(restoreRoutes);
      }
    } finally {
      setInternalsLoading(false);
    }
  };

  const closeInternals = () => {
    const nodeId = expandedNodeId;
    setExpandedNodeId(null);
    setExpandedDeclarations(new Set());
    setShowOutboundRoutes(routesBeforeInternals);
    if (nodeId) {
      setSelected({ id: nodeId, group: "node", data: { id: nodeId } });
    }
  };

  const handleGraphSelect = (next: SelectedGraphElement | null) => {
    const nextTactic = next?.group === "node" && next.data.kind === "routedTactic"
      ? next.data.tacticId
      : undefined;
    if (typeof nextTactic === "string") {
      navigate(`/ct/${nextTactic}`);
      return;
    }
    setSelected(next);
  };

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
  const internalSelection = selected?.data.internalKind ? selected : undefined;
  const entry = tactic.nodes.find((candidate) => candidate.nodeKind === "entry")?.nodeId;
  const artifactWarnings = Array.from(
    new Map(
      [...response.artifactWarnings, ...(internals?.artifactWarnings ?? [])].map(
        (warning) => [warning.message, warning],
      ),
    ).values(),
  );

  return (
    <div className="app-page app-page--tactic">
      <AppHeader
        verification={response.verification}
        artifactWarnings={artifactWarnings}
        compact
      />
      <div className="tactic-titlebar">
        <div>
          <nav className="breadcrumbs" aria-label="Breadcrumb">
            <Link to="/framework">Framework</Link><span>/</span><strong>{tactic.tacticId}</strong>
          </nav>
          <h1><span>{tactic.tacticId}</span>{tactic.title}</h1>
        </div>
        <div className="titlebar-stats">
          <span><strong>{tactic.nodes.length}</strong> nodes</span>
          <span><strong>{tactic.transitions.length}</strong> typed transitions</span>
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
              {internalsError ? (
                <span className="machine-internals-error" role="alert">{internalsError}</span>
              ) : null}
            </div>
            <div className="machine-view-controls">
              <div className="internal-view-controls">
                {expandedNodeId ? (
                  <button type="button" onClick={closeInternals}>Return to overview</button>
                ) : (
                  <button
                    type="button"
                    disabled={!node || internalsLoading}
                    onClick={() => node && void openInternals(node.nodeId)}
                  >
                    {internalsLoading ? "Loading Lean internals…" : "Expand selected node"}
                  </button>
                )}
                {expandedNodeId && expandedDeclarations.size ? (
                  <button
                    type="button"
                    onClick={() => setExpandedDeclarations(new Set())}
                  >
                    Hide declaration dependencies
                  </button>
                ) : null}
              </div>
              <label className="route-toggle">
                <input
                  type="checkbox"
                  checked={showOutboundRoutes}
                  disabled={expandedNodeId !== null || response.outboundRoutes.length === 0}
                  onChange={(event) => {
                    setShowOutboundRoutes(event.currentTarget.checked);
                    setSelected(null);
                  }}
                />
                <span>
                  {response.outboundRoutes.length === 0
                    ? "No outbound CT routes"
                    : "Show routes to other CTs"}
                </span>
              </label>
              <div className="legend" aria-label="Node legend">
                {expandedNodeId ? (
                  <>
                    <span><i className="legend__author" /> author object</span>
                    <span><i className="legend__operation" /> operation</span>
                    <span><i className="legend__theorem" /> theorem</span>
                    <span><i className="legend__dependency" /> dependency</span>
                    <span><i className="legend__transition" /> CT transition</span>
                  </>
                ) : (
                  <>
                    <span><i className="legend__entry" /> entry</span>
                    <span><i className="legend__compute" /> computation</span>
                    <span><i className="legend__residual" /> residual</span>
                    <span><i className="legend__certificate" /> certificate</span>
                    <span><i className="legend__transition" /> typed transition</span>
                    {showOutboundRoutes ? <span><i className="legend__route" /> CT route</span> : null}
                  </>
                )}
              </div>
            </div>
          </div>
          <GraphCanvas
            mode={expandedNodeId ? "internals" : "machine"}
            elements={elements}
            entryId={entry}
            selectedId={selected?.id}
            onSelect={handleGraphSelect}
          />
          <div className="machine-routes">
            <span className="eyebrow">Cross-CT routes</span>
            <RouteList inbound={response.inboundRoutes} outbound={response.outboundRoutes} />
          </div>
        </section>

        {expandedNodeId && internalSelection && internals ? (
          <NodeInternalsInspector
            key={selected?.id}
            nodeId={expandedNodeId}
            selected={internalSelection}
            response={internals}
            expandedDeclarations={expandedDeclarations}
            onExpandDeclaration={(declarationId) => {
              setExpandedDeclarations((current) => new Set(current).add(declarationId));
            }}
          />
        ) : (
          <Inspector
            key={selected?.id ?? tactic.tacticId}
            tactic={tactic}
            node={node}
            edge={edge}
            inboundRoutes={response.inboundRoutes}
            outboundRoutes={response.outboundRoutes}
          />
        )}
      </main>
    </div>
  );
}
