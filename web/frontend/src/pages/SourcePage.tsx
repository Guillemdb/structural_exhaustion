import { useCallback } from "react";
import { Link, useParams, useSearchParams } from "react-router-dom";

import { fetchSourceExcerpt } from "../api";
import { CopyButton } from "../components/CopyButton";
import { useApiResource } from "../hooks/useApiResource";
import { useDocumentMetadata } from "../hooks/useDocumentMetadata";
import type { SourceExcerptView } from "../v2-types";

const PAGE_SPAN = 160;

function sourceHref(sourceId: string, start: number, end: number): string {
  const query = new URLSearchParams({ start: String(start), end: String(end) });
  return `/source/${encodeURIComponent(sourceId)}?${query.toString()}`;
}

function SourceFailure({ error }: { error: Error }) {
  return (
    <section className="request-state request-error" role="alert">
      <span aria-hidden="true">!</span>
      <h1>We could not open this source</h1>
      <p>{error.message}</p>
      <button type="button" onClick={() => window.location.reload()}>
        Try again
      </button>
      <Link to="/reference">Return to the API reference</Link>
    </section>
  );
}

function SourceDocument({ source }: { source: SourceExcerptView }) {
  const lines = source.content === "" ? [] : source.content.split("\n");
  const hasPrevious = source.startLine > 1;
  const hasNext = source.endLine < source.totalLines;
  const previousEnd = source.startLine - 1;
  const previousStart = Math.max(1, previousEnd - PAGE_SPAN + 1);
  const nextStart = source.endLine + 1;
  const nextEnd = Math.min(source.totalLines, nextStart + PAGE_SPAN - 1);

  return (
    <article className="source-page">
      <header className="source-hero">
        <div>
          <nav className="breadcrumbs" aria-label="Breadcrumb">
            <ol>
              <li><Link to="/">Home</Link></li>
              <li><Link to="/reference">Reference</Link></li>
              <li aria-current="page">Source</li>
            </ol>
          </nav>
          <p className="hero-eyebrow">Published Lean source</p>
          <h1>{source.path}</h1>
          <p>
            Lines {source.startLine}–{source.endLine} of {source.totalLines}, served from the
            backend's allowlisted and request-time revalidated source set.
          </p>
          <dl className="source-metadata">
            <div>
              <dt>Source ID</dt>
              <dd>{source.sourceId}</dd>
            </div>
            <div>
              <dt>SHA-256</dt>
              <dd>{source.sha256}</dd>
            </div>
          </dl>
        </div>
      </header>

      <section className="source-body" aria-labelledby="source-excerpt-heading">
        <div className="source-toolbar">
          <div>
            <p className="section-eyebrow">Exact excerpt</p>
            <h2 id="source-excerpt-heading">
              Lines {source.startLine}–{source.endLine}
            </h2>
          </div>
          <nav className="source-pagination" aria-label="Source excerpt pages">
            {hasPrevious ? (
              <Link to={sourceHref(source.sourceId, previousStart, previousEnd)}>
                ← Previous lines
              </Link>
            ) : <span />}
            {hasNext ? (
              <Link to={sourceHref(source.sourceId, nextStart, nextEnd)}>
                Next lines →
              </Link>
            ) : null}
          </nav>
        </div>

        <figure className="source-viewer">
          <figcaption>
            <span>{source.path}</span>
            <span className="code-actions">
              <span className="source-language">Lean</span>
              <CopyButton text={source.content} label="source excerpt" />
            </span>
          </figcaption>
          <div className="source-code-scroll" tabIndex={0} aria-label="Lean source excerpt">
            {lines.length > 0 ? (
              <ol className="source-lines" start={source.startLine}>
                {lines.map((line, index) => (
                  <li key={source.startLine + index}>
                    <code>{line || "\u00a0"}</code>
                  </li>
                ))}
              </ol>
            ) : (
              <p className="source-empty">This source file is empty.</p>
            )}
          </div>
        </figure>

        <nav className="source-pagination source-pagination-bottom" aria-label="More source lines">
          {hasPrevious ? (
            <Link to={sourceHref(source.sourceId, previousStart, previousEnd)}>
              ← Lines {previousStart}–{previousEnd}
            </Link>
          ) : <span />}
          {hasNext ? (
            <Link to={sourceHref(source.sourceId, nextStart, nextEnd)}>
              Lines {nextStart}–{nextEnd} →
            </Link>
          ) : null}
        </nav>
      </section>
    </article>
  );
}

export default function SourcePage() {
  const { sourceId = "" } = useParams();
  const [searchParameters] = useSearchParams();
  const start = searchParameters.get("start");
  const end = searchParameters.get("end");
  const load = useCallback(
    (signal: AbortSignal) => fetchSourceExcerpt(sourceId, { start, end }, signal),
    [end, sourceId, start],
  );
  const resource = useApiResource(load, [sourceId, start, end]);
  const title = resource.state === "ready" ? resource.data.path : "Lean source";
  const description = resource.state === "ready"
    ? `Published Hypostructure source lines ${resource.data.startLine}–${resource.data.endLine}.`
    : "Published Hypostructure Lean source.";
  useDocumentMetadata(title, description, `/source/${encodeURIComponent(sourceId)}`);

  if (resource.state === "loading") {
    return (
      <section className="request-state" role="status">
        <span className="loading-mark" aria-hidden="true" />
        <p>Opening verified source…</p>
      </section>
    );
  }
  if (resource.state === "error") return <SourceFailure error={resource.error} />;
  return <SourceDocument source={resource.data} />;
}
