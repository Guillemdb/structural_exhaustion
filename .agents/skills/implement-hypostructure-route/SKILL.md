---
name: implement-hypostructure-route
description: Implement or complete a framework-owned Hypostructure transition between CT stages. Use for typed Core.Routing profiles and transitions, specialized semantic discovery, generic accumulated edges, disabled residuals, provenance, public target execution, full-ledger preservation, route registry maintenance, and focused route fixtures; never use it to add route plumbing to an application proof.
---

# Implement a Hypostructure Route

Implement routes only in Core, `Hypostructure.Routes`, or a reviewed domain-owned profile. Applications, including Erdős and PDE examples, must invoke a framework-owned node executor and must never author or consume route plumbing.

## Establish what is actually executable

Read completely:

- `hypostructure/Hypostructure/Core/Routing.lean` and the relevant Core execution, residual-ledger, query, and provision modules;
- `hypostructure/Hypostructure/Routes/{Registry,Accumulated}.lean`;
- `hypostructure/Hypostructure/Fixtures/{RouteRegistry,ExecutionRouting}.lean`;
- both endpoint CT vertical slices and domain adapters;
- route rows in `migration/hypostructure/api-feature-matrix.csv` and section 16.4 plus the route checklist in `HYPOSTRUCTURE_MIGRATION_GUIDE.md`.

Distinguish three independent facts:

- `Registry.Status.baseline` records an executable profile in the source migration baseline; it does not make the Hypostructure row executable.
- `Registry.Status.planned` records an EG or PDE requirement; it is metadata only.
- A live route exists only when source code supplies a typed `Core.Routing.Profile`, registers a `Core.Routing.Transition`, exposes its framework executor, and proves it with a focused fixture.

Likewise, `Routes.Registry` and its `Registry.Entry` supply only edge identity, owner, kind, and status. They contain no target capability or discovery theorem. Never infer execution from catalog membership.

If an endpoint, target `Core.Execution` capability, discovery abstraction, or lower Core primitive is missing, pause this route and hand that gap to `$extend-hypostructure-framework`. Never bridge the gap with an application wrapper or a manually called CT executor.

## Choose the route shape

Use the smallest reviewed shape:

- For a row whose live `kind` is `.genericAccumulated`, instantiate one typed profile and reuse `Routes.Accumulated.register` and `Routes.Accumulated.advance`. Do not copy the generic executor for each edge.
- For stable route-specific semantic discovery, implement a dedicated module under `Hypostructure/Routes`, but still use `Core.Routing.Profile`, `Transition.register`, and `Routing.advance` internally.
- For a `.profileRequirement` or `.familyRequirement`, first complete the framework-extension review, both endpoint contracts, status record, and fixture. The equality gate intentionally prevents passing a planned row to `Accumulated.register`.

Do not change a registry status merely to satisfy the constructor. Update the catalog and migration matrix only when the typed implementation and evidence exist.

## Preserve the literal complete ledger

Let `Source` be the exact accumulated stage emitted by the direct predecessor or framework-owned join. Pass that whole value to `Routing.advance`.

Use `Core.Residual.Query.residual`, `latest`, `preserve`, `comap`, `map`, and `and` to discover existing facts. Do not project a current local residual, wrap it in a fresh root ledger, or copy earlier facts into a new carrier. The generated route stage must satisfy:

- `stage.previous = source` by `advance_previous`;
- the stable root residual is unchanged by `advance_residual`;
- every inherited typed query remains reachable through the literal predecessor;
- the new route result is the sole ledger extension.

The full ledger invariant applies on enabled and disabled discovery branches and through joins. Never substitute a bare target result for the accumulated route stage.

## Implement the typed profile

Supply `Core.Routing.Profile Source` with only:

- `Target : Core.Execution.Spec Source`;
- its real `Core.Execution.Capability` in `executor`;
- predecessor-indexed `Seed` and `Blocked` types;
- exhaustive `discover : source -> Discovery (Seed source) (Blocked source)`;
- `targetInput`, constructed from the exact source and discovered seed.

Keep semantic discovery local: inspect only data reachable from the source ledger or its immediate registered domain structure. Preserve observable order. Do not scan an ambient graph, context universe, function space, scale continuum, or synthesized carrier.

Never put a target result, selected terminal, completed trace, route provenance, ledger extension, arbitrary closure proof, or manually chosen target input in the profile. `Routing.advance` must perform discovery and, on `.enabled`, invoke `Core.Execution.run` with `profile.executor` and the framework-constructed input. On `.disabled`, retain the exact typed `Blocked` residual; do not erase it behind an untyped failure.

If a CT endpoint exposes only a CT-specific runner and lacks the registered `Core.Execution.Spec`/`Capability` needed by `Core.Routing.Profile`, that bridge is a framework gap. Extend the owning layer; do not call `CTN.execute` beside `Routing.advance` and pretend the results form one transition.

## Retain provenance and target evidence

Register the exact `Registry.Entry.edge`; profile IDs disambiguate distinct semantics within one CT family. Prove:

- `advance_provenance` records that exact edge;
- `advance_canonical` records exactly the registered discovery;
- enabled execution used the exact discovered seed and `targetInput`;
- target soundness, exhaustiveness/totality, trace semantics, and work bound come from the public target capability;
- disabled discovery returns its typed residual and performs no target execution;
- source evidence required later remains queryable.

Do not expose `Routing.Profile`, `Routing.Transition`, `Accumulated.register`, source projections, or bare `advance` calls to an application. Wrap the completed transition in one framework-owned public node executor whose input is the exact predecessor and whose output is the exact successor stage.

## Register only stable reusable semantics

Add a route family/profile only when the conversion has:

- a stable exact source residual kind;
- a reusable semantic discovery boundary;
- a framework-constructible target input;
- a real target executor;
- typed disabled/failure residuals;
- preserved context and complete ledger;
- stable provenance and a local polynomial work bound;
- at least one Graph or neutral fixture and, when applicable, an honest PDE fixture.

If the conversion is theorem-specific or needed once, put ordinary composition behind the lowest reusable Core, CT, Graph, or PDE node executor. It still consumes and returns the complete ledger; it does not belong in an application-defined route family.

## Validate completion

Extend `Fixtures/RouteRegistry.lean` or add the focused route fixture to cover enabled and disabled discovery, exact edge/profile ID, complete predecessor equality, root residual, inherited queries, canonical discovery, target input and execution, provenance, target trace and work, and exact successor continuation. Keep the registry audit pinning 17 CT IDs, 29 source-baseline profiles, and 25 planned requirements unless a reviewed migration decision changes the catalog.

Compile source CT, route, target CT, and fixture together. Run the package build, import firewall, architecture checks, transitive axiom audit, and migration-record tests. Reject any route whose fixture starts from a copied local residual, chains a bare result, omits a disabled branch, or permits application-owned routing.
