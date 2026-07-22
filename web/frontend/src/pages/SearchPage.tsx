import { useCallback, useEffect, useState } from "react";
import { Link, useSearchParams } from "react-router-dom";

import { fetchSearch } from "../api";
import { SmartLink } from "../components/SmartLink";
import { useApiResource } from "../hooks/useApiResource";
import { useDocumentMetadata } from "../hooks/useDocumentMetadata";
import type { SearchView } from "../v2-types";

export default function SearchPage() {
  useDocumentMetadata(
    "Search",
    "Search Hypostructure concepts, CT contracts, routes, examples, modules, and public Lean declarations.",
    "/search",
  );
  const [parameters, setParameters] = useSearchParams();
  const requestKey = parameters.toString();
  const query = parameters.get("q") ?? "";
  const [input, setInput] = useState(query);
  useEffect(() => setInput(query), [query]);
  const load = useCallback(
    (signal: AbortSignal): Promise<SearchView> => fetchSearch(new URLSearchParams(requestKey), signal),
    [requestKey],
  );
  const resource = useApiResource(load, [requestKey]);

  return (
    <article className="search-page">
      <header className="search-hero">
        <p className="hero-eyebrow">Global reference</p>
        <h1>Search Hypostructure</h1>
        <p>Find concepts, CT contracts, routes, examples, modules, and public Lean declarations.</p>
        <form
          role="search"
          onSubmit={(event) => {
            event.preventDefault();
            const next = new URLSearchParams();
            if (input.trim()) next.set("q", input.trim());
            setParameters(next);
          }}
        >
          <label htmlFor="global-search">Search documentation</label>
          <div>
            <input id="global-search" type="search" value={input} autoFocus onChange={(event) => setInput(event.target.value)} />
            <button type="submit">Search</button>
          </div>
        </form>
      </header>
      <div className="search-body">
        {resource.state === "loading" ? <p role="status">Searching the server index…</p> : null}
        {resource.state === "error" ? <div role="alert"><h2>Search is unavailable</h2><p>{resource.error.message}</p></div> : null}
        {resource.state === "ready" ? (
          <>
            <div className="search-toolbar">
              <p role="status" aria-live="polite" aria-atomic="true">
                <strong>{resource.data.total}</strong> {resource.data.total === 1 ? "result" : "results"}
                {resource.data.query ? <> for “{resource.data.query}”</> : null}
              </p>
              {resource.data.facets.length ? (
                <div className="facets" aria-label="Filter search results">
                  {resource.data.facets.map((facet) => {
                    const next = new URLSearchParams(parameters);
                    if (facet.active) next.delete(facet.field); else next.set(facet.field, facet.value);
                    next.delete("page");
                    return <Link className={facet.active ? "active" : ""} to={`/search?${next}`} key={`${facet.field}:${facet.value}`}>{facet.label} <span>{facet.count}</span></Link>;
                  })}
                </div>
              ) : null}
            </div>
            {resource.data.results.length ? (
              <ol className="search-results" start={(resource.data.page - 1) * resource.data.pageSize + 1}>
                {resource.data.results.map((result) => (
                  <li key={result.id}>
                    <SmartLink href={result.href}>
                      <span className="result-kind">{result.kind}{result.module ? ` · ${result.module}` : ""}</span>
                      <h2>{result.title}</h2>
                      <p>{result.summary}</p>
                      {result.highlights?.map((highlight, index) => (
                        <span className="result-highlight" key={index} dangerouslySetInnerHTML={{ __html: highlight }} />
                      ))}
                    </SmartLink>
                  </li>
                ))}
              </ol>
            ) : <div className="empty-results"><h2>No matches yet</h2><p>Try a declaration name, a CT number, or a mathematical capability.</p></div>}
            {resource.data.total > resource.data.pageSize ? (
              <nav className="pagination" aria-label="Search results pages">
                {resource.data.page > 1 ? <PageLink direction="Previous" page={resource.data.page - 1} parameters={parameters} /> : <span />}
                <span>Page {resource.data.page} of {Math.ceil(resource.data.total / resource.data.pageSize)}</span>
                {resource.data.page * resource.data.pageSize < resource.data.total ? <PageLink direction="Next" page={resource.data.page + 1} parameters={parameters} /> : <span />}
              </nav>
            ) : null}
          </>
        ) : null}
      </div>
    </article>
  );
}

function PageLink({ direction, page, parameters }: { direction: string; page: number; parameters: URLSearchParams }) {
  const next = new URLSearchParams(parameters);
  next.set("page", String(page));
  return <Link to={`/search?${next}`}>{direction}</Link>;
}
