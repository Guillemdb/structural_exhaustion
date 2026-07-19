import { useEffect, useMemo, useState } from "react";
import { Link, useLocation, useNavigate } from "react-router-dom";

import { fetchDocumentation } from "../api";
import { useDocumentationAudience } from "../audience";
import { AppHeader } from "../components/AppHeader";
import { ErrorState, LoadingState } from "../components/LoadState";
import { exampleDestination } from "../routes";
import type {
  DocumentationCapability,
  DocumentationResponse,
} from "../types";

type Layer = "core" | "graph";

const layerCopy = {
  core: {
    eyebrow: "Problem-independent proof machinery",
    title: "Build finite, auditable structural arguments.",
    description:
      "Core turns local finite data into deterministic searches, exact residual states, typed handoffs, and certified work bounds.",
    flow: ["Problem and context", "Finite local data", "Verified computation", "Residual and provenance", "Certificate and work bound"],
  },
  graph: {
    eyebrow: "Reusable Mathlib graph profiles",
    title: "Assemble graph proofs from verified capabilities.",
    description:
      "The Graph layer specializes Core and the closure tactics to paths, cycles, reductions, packings, coloring, and extremal counting.",
    flow: ["Finite Mathlib graph", "Graph profile", "CT execution", "Typed residual or certificate", "Mathematical theorem"],
  },
} as const;

function WorkflowExcerpt({ capability }: { capability: DocumentationCapability }) {
  const { audience } = useDocumentationAudience();
  if (!capability.examples.length) return null;
  return (
    <section className="doc-walkthroughs" aria-label="Example walkthroughs">
      <div className="section-heading">
        <div>
          <span className="eyebrow">Verified examples</span>
          <h3>See this capability in a proof</h3>
        </div>
      </div>
      {capability.examples.map((example) => (
        <article className="doc-walkthrough" key={`${example.exampleId}:${example.workflowId}`}>
          <header>
            <div>
              <span>{example.exampleTitle}</span>
              <h4>{example.workflow.title}</h4>
              <p>{example.workflow.summary}</p>
            </div>
            <Link to={exampleDestination(example.exampleId)}>Open full workflow →</Link>
          </header>
          <ol className="doc-stage-list">
            {example.workflow.stages.map((stage) => (
              <li key={stage.stageId}>
                <span>{stage.tacticId ?? "Proof"}</span>
                <div>
                  <strong>{stage.title}</strong>
                  <p>{stage.summary}</p>
                  {audience === "leanUser" ? <code>{stage.primaryDeclarationId}</code> : null}
                </div>
              </li>
            ))}
          </ol>
        </article>
      ))}
    </section>
  );
}

function DocumentationPage({ layer }: { layer: Layer }) {
  const [response, setResponse] = useState<DocumentationResponse | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [query, setQuery] = useState("");
  const [selectedId, setSelectedId] = useState<string | null>(null);
  const { audience } = useDocumentationAudience();
  const location = useLocation();
  const navigate = useNavigate();

  useEffect(() => {
    const controller = new AbortController();
    fetchDocumentation(controller.signal)
      .then(setResponse)
      .catch((reason: unknown) => {
        if (!controller.signal.aborted) {
          setError(reason instanceof Error ? reason.message : String(reason));
        }
      });
    return () => controller.abort();
  }, []);

  useEffect(() => {
    const capabilityId = decodeURIComponent(location.hash.replace(/^#/, ""));
    if (capabilityId) setSelectedId(capabilityId);
  }, [location.hash]);

  const selectCapability = (capabilityId: string) => {
    setSelectedId(capabilityId);
    navigate({ hash: capabilityId }, { replace: true });
  };

  const capabilities = useMemo(() => {
    const needle = query.trim().toLowerCase();
    return (response?.capabilities ?? []).filter((capability) => {
      if (capability.layer !== layer) return false;
      const copy = capability[audience];
      return !needle || [capability.title, capability.category, copy.summary, ...capability.relatedTacticIds]
        .some((value) => value.toLowerCase().includes(needle));
    });
  }, [audience, layer, query, response]);

  const selected = capabilities.find((capability) => capability.capabilityId === selectedId)
    ?? capabilities[0];
  const categories = Array.from(new Set(capabilities.map((capability) => capability.category)));
  const copy = layerCopy[layer];

  if (error) return <main className="standalone-state"><ErrorState message={error} /></main>;
  if (!response) return <main className="standalone-state"><LoadingState label={`Loading ${layer} documentation…`} /></main>;

  return (
    <div className={`app-page app-page--overview app-page--documentation app-page--documentation-${layer}`}>
      <AppHeader verification={response.verification} artifactWarnings={response.artifactWarnings} showAudienceToggle />
      <main>
        <section className="hero documentation-hero">
          <div>
            <span className="eyebrow">{copy.eyebrow}</span>
            <h1>{copy.title}</h1>
            <p>{copy.description}</p>
          </div>
          <div className="catalog-stamp">
            <span>{capabilities.length} public capabilities</span>
            <code>{response.catalogHash.slice(0, 12)}</code>
            <small>{audience === "mathematician" ? "mathematical view" : "Lean API view"}</small>
          </div>
        </section>

        <ol className="documentation-flow" aria-label={`${layer} capability flow`}>
          {copy.flow.map((step, index) => (
            <li key={step}><span>{index + 1}</span><strong>{step}</strong></li>
          ))}
        </ol>

        <section className="documentation-browser">
          <aside className="documentation-index">
            <div className="section-heading">
              <div><span className="eyebrow">Public surface</span><h2>Capabilities</h2></div>
            </div>
            <label className="search-box">
              <span className="sr-only">Search capabilities</span>
              <input value={query} onChange={(event) => setQuery(event.target.value)} placeholder="Search capabilities or CTs…" />
            </label>
            {categories.map((category) => (
              <section key={category} className="documentation-category">
                <h3>{category}</h3>
                {capabilities.filter((capability) => capability.category === category).map((capability) => (
                  <button
                    type="button"
                    className={capability.capabilityId === selected?.capabilityId ? "is-active" : ""}
                    onClick={() => selectCapability(capability.capabilityId)}
                    key={capability.capabilityId}
                  >
                    <strong>{capability.title}</strong>
                    <small>{capability[audience].summary}</small>
                  </button>
                ))}
              </section>
            ))}
            {!capabilities.length ? <p className="empty-search">No capability matches “{query}”.</p> : null}
          </aside>

          {selected ? (
            <article className="documentation-detail" id={selected.capabilityId} key={`${selected.capabilityId}:${audience}`}>
              <span className="eyebrow">{selected.category}</span>
              <h2>{selected.title}</h2>
              <p className="documentation-detail__lead">{selected[audience].summary}</p>
              <dl className="documentation-contract">
                <div><dt>{audience === "mathematician" ? "Assume or construct" : "Author provides"}</dt><dd>{selected[audience].inputs}</dd></div>
                <div><dt>{audience === "mathematician" ? "Conclude" : "Framework provides"}</dt><dd>{selected[audience].result}</dd></div>
              </dl>
              {selected.relatedCapabilityIds.length ? (
                <div className="documentation-relations">
                  <span>Builds on</span>
                  {selected.relatedCapabilityIds.map((id) => {
                    const related = response.capabilities.find((capability) => capability.capabilityId === id);
                    if (!related) return null;
                    return related.layer === layer
                      ? <button key={id} type="button" onClick={() => selectCapability(id)}>{related.title}</button>
                      : <Link key={id} to={`/framework/${related.layer}#${id}`}>{related.title}</Link>;
                  })}
                </div>
              ) : null}
              {selected.relatedTacticIds.length ? (
                <div className="ct-chip-list" aria-label="Related closure tactics">
                  {selected.relatedTacticIds.map((tacticId) => <Link key={tacticId} to={`/ct/${tacticId}`}>{tacticId}</Link>)}
                </div>
              ) : null}
              {audience === "leanUser" ? (
                <details className="documentation-declarations" open>
                  <summary>Principal Lean declarations ({selected.declarations.length})</summary>
                  <ul>{selected.declarations.map((declaration) => <li key={declaration}><code>{declaration}</code></li>)}</ul>
                </details>
              ) : null}
              <WorkflowExcerpt capability={selected} />
            </article>
          ) : null}
        </section>
      </main>
      <footer className="app-footer"><span>Structural Exhaustion</span><span>Documentation projected from compiled Lean descriptors.</span></footer>
    </div>
  );
}

export function CoreDocumentationPage() {
  return <DocumentationPage layer="core" />;
}

export function GraphDocumentationPage() {
  return <DocumentationPage layer="graph" />;
}
