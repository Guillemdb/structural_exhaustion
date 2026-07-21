---
name: implement-hypostructure-ct10
description: Implement Hypostructure CT10 finite refinement classification. Use for residual-owned datum and complete class schedules, first direct classes, first missing classes and promotions, exhaustive class coverage, graph vertex classifiers, or PDE observable-signature classifiers.
---

# Implement Hypostructure CT10

Use CT10 to classify an exact finite datum family already carried by the literal predecessor. Let Hypostructure choose the first direct class, otherwise the first unobserved class, otherwise certify exhaustive coverage.

## Establish the live contract

Before changing a proof, read these files completely:

- `hypostructure/Hypostructure/CT10/{Spec,Capability,State,Search,Execution,Theorems,Automation}.lean`;
- `hypostructure/Hypostructure/Graph/CT10.lean` or `hypostructure/Hypostructure/PDE/CT10.lean` when using that domain;
- `hypostructure/Hypostructure/Fixtures/CT10.lean`;
- the `ct.ct10` and `graph.ct10` rows in `migration/hypostructure/api-feature-matrix.csv`, the relevant PDE row in `pde-row-matrix.csv`, and the applicable public barrel imports.

Treat the migration ledger as a status gate. A present file, a historical `baseline` label, a `planned` row, or a stale object file is not sufficient. Use a layer in an application only when its reviewed status and fresh focused fixture justify that use.

If the required Core, CT10, Graph, PDE, fixture, or public integration layer is missing or below the required status, stop the application implementation and hand the gap to `$extend-hypostructure-framework`. Never reproduce the missing search, carrier, result, or route as application-local code. If only a cross-CT transition is missing, use `$implement-hypostructure-route` after both endpoints are ready.

## Keep the author boundary minimal

Define `CT10.Spec` with only:

- predecessor-dependent `Datum`, `Class`, and `Promotion` types;
- `classOf`, the independently checkable `Direct` predicate, and `promote`.

Define `CT10.Capability` with:

- `data : Core.Residual.Query ... Core.Finite.Enumeration` for the exact incoming data;
- `classes : Core.Residual.Query ... Core.Finite.CompleteEnumeration` for the complete ordered class universe;
- the direct-case decider and the polynomial input-size, coefficient, degree, and bound.

Use `Core.Residual.Query.residual`, `latest`, `preserve`, `comap`, `map`, or `and` to recover data already present in the complete predecessor. Do not create a node-local subtype, image, representative family, filtered carrier, or replacement enumeration. If the predecessor lacks a reusable typed query, add it at the correct Core or domain owner through `$extend-hypostructure-framework`.

Do not supply rows, an observed-class table, a missing class, a promotion result, a terminal, or a trace. Those are framework outputs under `Core.Provision`.

## Execute the classifier

1. Make the datum schedule exactly the local objects exposed by the predecessor.
2. Make the class schedule complete and put it in the mathematically intended observable order.
3. Prove `classOf` and `Direct` express the manuscript definitions.
4. Define `promote previous cls` without choosing which class will be absent.
5. Prove the bound
   `classCount + classCount * datumCount <= coefficient * (inputSize + 1)^degree`.
6. Run `CT10.execute` or `ct10_execute`; do not call the private route machinery or build an `ExecutionResult`.
7. Consume the typed outcome from the generated stage and route every reachable residual through framework-owned continuation machinery.

CT10 scans direct classes first. Only if none is direct does it scan each class row over the incoming data and select the first missing class. Class order is therefore execution data and must be pinned by a fixture.

## Discharge every outcome

Handle the exact terminal grammar:

- `.direct`: retrieve the first `DirectResidual` and its prefix-absence evidence;
- `.promoted`: consume `PromotedResidual`, including global direct absence, the first missing class, earlier observed classes, and the exact computed promotion;
- `.exhaustive`: consume `ExhaustiveCertificate`, proving no class is direct and every declared class is observed.

For each completed invocation prove or reuse:

- literal predecessor retention;
- `OutcomeClaim` soundness through `verified` or `run_verified`;
- `Trace.expectedNodes` through `trace_exact`;
- totality, deterministic reference behavior, and exhaustive terminal grammar;
- exact or bounded checks and `checks_le_polynomial`;
- a typed consumer for every nonclosing residual.

Never recompute the first hit or rebuild a promotion downstream. Preserve the complete stage and retrieve inherited evidence with a typed query.

## Use domain adapters honestly

- Graph: use `Graph.CT10.vertexSpec` and `vertexCapability`. The graph adapter derives only the vertex datum schedule from the queried `FiniteObject`; the complete class schedule remains predecessor-owned.
- PDE: use `PDE.CT10.observableSpec` and `observableCapability`. Enumerate only explicit public observable indices; never enumerate points, functions, windows, scales, or measurable sets.

If the desired classifier ranges over attachments, subgraphs, analytic profiles, or another carrier not already represented by the live adapter, treat that as a framework capability gap. Do not encode it as an application-local CT10 datum family.

## Validate completion

Extend `Hypostructure/Fixtures/CT10.lean` to cover `.direct`, `.promoted`, and `.exhaustive`, including first-hit ordering, exact traces, work, Graph, and PDE instantiations. Run focused Lean checks for every edited layer, then the Hypostructure package, import-firewall, and trust checks required by the migration guide. Keep parity evidence separate from mathematical closure.
