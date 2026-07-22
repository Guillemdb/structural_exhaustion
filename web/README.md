# Hypostructure documentation application

The documentation site is a same-origin Flask and React application. Lean and
Python own data discovery, validation, indexing, joins, graph positions,
search ranking, source hashing, and page-view construction. React receives
small typed view models and performs presentation only.

```text
Hypostructure Lean sources
        │ compiled environment export
        ▼
declarations.raw.json ──┐
                        ├─ Python documentation build
curated guides ─────────┘        │
                                 ▼
                         snapshot.json + manifest.json
                                 │ startup validation/indexing
                                 ▼
                         Flask /api/v2 + static React
                                 │ page-sized JSON
                                 ▼
                         accessible React views
```

## Authority and trust

- `hypostructure/Hypostructure/Canonical/WebExport.lean` exports declaration
  names, elaborated types, documentation strings, source ranges, dependency
  edges, CT identities, and route-registry metadata from the compiled Lean
  environment.
- `tools/build_hypostructure_web_data.py` combines that exact framework catalog
  with curated guides and conservatively indexed native fixture/application
  sources. Each declaration records its provenance.
- `generated/hypostructure/web/manifest.json` binds the snapshot and every
  publishable source file by SHA-256. Flask rejects missing, malformed, stale,
  out-of-root, or unpublished inputs at startup and rechecks a source before
  serving an excerpt.
- A route-registry identity is never presented as executable evidence. A route
  is marked executable only when a concrete typed transition and focused
  execution fixture are present.

The JSON contracts live in [`contracts/`](contracts/). The snapshot is
deterministic: its identity is its content hash, not a wall-clock timestamp.

## Backend boundary

Flask owns:

- artifact and source validation;
- page, CT, route, example, Erdős-node, module, and declaration lookup;
- ranked, faceted, paginated search;
- bounded source excerpts;
- ETags, cache policy, security headers, structured errors, and SPA delivery.

The public API is rooted at `/api/v2`. It never exposes the complete snapshot;
clients request a site shell, one page/detail view, a bounded search page, or a
bounded source excerpt.

## Frontend boundary

React renders the backend's `PageView` and `SearchView` contracts. Cytoscape
uses backend-provided nodes, edges, labels, and preset positions. KaTeX renders
a supplied formula string. The browser does not parse Lean, join catalogs,
classify proof state, calculate proof topology, rank results, or read source
files directly.

## Commands

```bash
make web-data   # build/typecheck sources and generate the immutable snapshot
make web-test   # data, Flask, React, type, accessibility, and production checks
make web        # build React and serve Flask + Gunicorn on 127.0.0.1:8000
```

For frontend-only development, run `npm run dev` in `web/frontend`; Vite
proxies `/api` to Flask on port 8000. Production always uses the same origin.
