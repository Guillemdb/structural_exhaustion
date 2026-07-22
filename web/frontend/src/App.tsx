import { lazy, Suspense } from "react";
import { Route, Routes } from "react-router-dom";

import { AppShell } from "./components/AppShell";

const DataPage = lazy(() => import("./pages/DataPage"));
const SearchPage = lazy(() => import("./pages/SearchPage"));
const SourcePage = lazy(() => import("./pages/SourcePage"));
const NotFoundPage = lazy(() => import("./pages/NotFoundPage"));

function RouteFallback() {
  return (
    <section className="request-state" role="status">
      <span className="loading-mark" aria-hidden="true" />
      <p>Opening documentation…</p>
    </section>
  );
}

export default function App() {
  return (
    <AppShell>
      <Suspense fallback={<RouteFallback />}>
        <Routes>
          <Route path="/" element={<DataPage source={{ kind: "page", id: "home" }} />} />
          <Route path="/start" element={<DataPage source={{ kind: "page", id: "start" }} />} />
          <Route path="/core" element={<DataPage source={{ kind: "page", id: "core" }} />} />
          <Route path="/core/cts" element={<DataPage source={{ kind: "page", id: "cts" }} />} />
          <Route path="/core/cts/:ctId" element={<DataPage source={{ kind: "ct", parameter: "ctId" }} />} />
          <Route path="/core/routes" element={<DataPage source={{ kind: "page", id: "routes" }} />} />
          <Route path="/core/routes/:routeId" element={<DataPage source={{ kind: "route", parameter: "routeId" }} />} />
          <Route path="/graph" element={<DataPage source={{ kind: "page", id: "graph" }} />} />
          <Route path="/pde" element={<DataPage source={{ kind: "page", id: "pde" }} />} />
          <Route path="/examples" element={<DataPage source={{ kind: "page", id: "examples" }} />} />
          <Route path="/examples/:exampleId" element={<DataPage source={{ kind: "example", parameter: "exampleId" }} />} />
          <Route path="/erdos" element={<DataPage source={{ kind: "page", id: "erdos" }} />} />
          <Route path="/erdos/nodes/:nodeId" element={<DataPage source={{ kind: "erdos-node", parameter: "nodeId" }} />} />
          <Route path="/reference" element={<DataPage source={{ kind: "page", id: "reference" }} />} />
          <Route path="/reference/modules/:moduleId" element={<DataPage source={{ kind: "module", parameter: "moduleId" }} />} />
          <Route path="/reference/declarations/:declarationId" element={<DataPage source={{ kind: "declaration", parameter: "declarationId" }} />} />
          <Route path="/source/:sourceId" element={<SourcePage />} />
          <Route path="/search" element={<SearchPage />} />
          <Route path="*" element={<NotFoundPage />} />
        </Routes>
      </Suspense>
    </AppShell>
  );
}
