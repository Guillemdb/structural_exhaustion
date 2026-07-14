import { useEffect, useMemo, useState } from "react";
import { Link } from "react-router-dom";

import { fetchExamples } from "../api";
import { AppHeader } from "../components/AppHeader";
import { ErrorState, LoadingState } from "../components/LoadState";
import { exampleDestination } from "../routes";
import type { ExampleSummary, ExamplesResponse } from "../types";

export function filterExamples(examples: ExampleSummary[], query: string): ExampleSummary[] {
  const needle = query.trim().toLowerCase();
  if (!needle) return examples;
  return examples.filter((example) =>
    [example.exampleId, example.title, example.summary, ...example.tacticIds]
      .some((value) => value.toLowerCase().includes(needle)),
  );
}

function ExampleCard({ example }: { example: ExampleSummary }) {
  return (
    <Link className="example-card" to={exampleDestination(example.exampleId)}>
      <div className="example-card__topline">
        <span className={`proof-status proof-status--${example.proofStatus}`}>
          {example.proofStatus}
        </span>
        <span>{example.workflowCount} workflow{example.workflowCount === 1 ? "" : "s"}</span>
      </div>
      <h2>{example.title}</h2>
      <p>{example.summary}</p>
      <div className="ct-chip-list" aria-label="Closure tactics used">
        {example.tacticIds.map((tacticId) => <span key={tacticId}>{tacticId}</span>)}
      </div>
      <strong className="example-card__open">Inspect proof architecture <span aria-hidden="true">→</span></strong>
    </Link>
  );
}

export function ExamplesPage() {
  const [response, setResponse] = useState<ExamplesResponse | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [query, setQuery] = useState("");

  useEffect(() => {
    const controller = new AbortController();
    fetchExamples(controller.signal)
      .then(setResponse)
      .catch((reason: unknown) => {
        if (!controller.signal.aborted) {
          setError(reason instanceof Error ? reason.message : String(reason));
        }
      });
    return () => controller.abort();
  }, []);

  const filtered = useMemo(
    () => filterExamples(response?.examples ?? [], query),
    [query, response],
  );

  if (error) return <main className="standalone-state"><ErrorState message={error} /></main>;
  if (!response) return <main className="standalone-state"><LoadingState label="Loading examples…" /></main>;

  const completeCount = response.examples.filter((example) => example.proofStatus === "complete").length;
  return (
    <div className="app-page app-page--overview app-page--examples">
      <AppHeader
        verification={response.verification}
        artifactWarnings={response.artifactWarnings}
      />
      <main>
        <section className="hero examples-hero">
          <div>
            <span className="eyebrow">Lean-derived examples</span>
            <h1>See how closure tactics solve concrete problems.</h1>
            <p>
              Select an implemented example, follow each proof workflow, and inspect
              the exact problem code where it meets the framework.
            </p>
          </div>
          <div className="catalog-stamp">
            <span>{response.examples.length} examples</span>
            <code>{response.catalog.catalogHash.slice(0, 12)}</code>
            <small>{completeCount} complete · {response.examples.length - completeCount} partial</small>
          </div>
        </section>
        <section className="examples-catalog">
          <div className="section-heading">
            <div>
              <span className="eyebrow">Example catalog</span>
              <h2>Choose a proof</h2>
            </div>
            <label className="search-box examples-search">
              <span className="sr-only">Search examples</span>
              <input
                type="search"
                value={query}
                onChange={(event) => setQuery(event.target.value)}
                placeholder="Search examples or CTs…"
              />
            </label>
          </div>
          <div className="example-grid">
            {filtered.map((example) => <ExampleCard example={example} key={example.exampleId} />)}
          </div>
          {!filtered.length ? <p className="empty-search">No example matches “{query}”.</p> : null}
        </section>
      </main>
      <footer className="app-footer">
        <span>Structural Exhaustion</span>
        <span>Example composition and source ranges are generated from compiled Lean packages.</span>
      </footer>
    </div>
  );
}
