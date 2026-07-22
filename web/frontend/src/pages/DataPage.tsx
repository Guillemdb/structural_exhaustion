import { useCallback } from "react";
import { Link, useParams } from "react-router-dom";

import {
  fetchCt,
  fetchDeclaration,
  fetchErdosNode,
  fetchExamplePage,
  fetchModule,
  fetchPage,
  fetchRoutePage,
} from "../api";
import { PageDocument } from "../components/PageDocument";
import { useApiResource } from "../hooks/useApiResource";
import type { PageView } from "../v2-types";

export type PageSource =
  | { kind: "page"; id: string }
  | { kind: "ct"; parameter: string }
  | { kind: "route"; parameter: string }
  | { kind: "example"; parameter: string }
  | { kind: "erdos-node"; parameter: string }
  | { kind: "module"; parameter: string }
  | { kind: "declaration"; parameter: string };

function PageFailure({ error }: { error: Error }) {
  return (
    <section className="request-state request-error" role="alert">
      <span aria-hidden="true">!</span>
      <h1>We could not load this page</h1>
      <p>{error.message}</p>
      <button type="button" onClick={() => window.location.reload()}>Try again</button>
      <Link to="/">Return home</Link>
    </section>
  );
}

export default function DataPage({ source }: { source: PageSource }) {
  const parameters = useParams();
  const value = source.kind === "page" ? source.id : parameters[source.parameter] ?? "";
  const load = useCallback(
    (signal: AbortSignal): Promise<PageView> => {
      switch (source.kind) {
        case "page": return fetchPage(source.id, signal);
        case "ct": return fetchCt(value, signal);
        case "route": return fetchRoutePage(value, signal);
        case "example": return fetchExamplePage(value, signal);
        case "erdos-node": return fetchErdosNode(value, signal);
        case "module": return fetchModule(value, signal);
        case "declaration": return fetchDeclaration(value, signal);
      }
    },
    [source, value],
  );
  const resource = useApiResource(load, [value, source.kind]);

  if (resource.state === "loading") {
    return (
      <section className="request-state" role="status">
        <span className="loading-mark" aria-hidden="true" />
        <p>Loading verified documentation…</p>
      </section>
    );
  }
  if (resource.state === "error") return <PageFailure error={resource.error} />;
  return <PageDocument page={resource.data} />;
}
