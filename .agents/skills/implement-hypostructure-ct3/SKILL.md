---
name: implement-hypostructure-ct3
description: Implement Hypostructure CT3 exact response compression and table classification. Use for same-boundary or local-context representatives, finite response coordinates, smaller candidates, distinguishing stored rows, known-row transport, or novel-row residuals.
---

# Implement Hypostructure CT3

Use CT3 to compare a predecessor-owned source with scheduled representatives through exact finite response coordinates. Promote finite equality to semantic context equality only through registered symbolic coverage.

## Gate the live contract

1. Read row `ct.ct3` in `migration/hypostructure/api-feature-matrix.csv`.
2. Read `hypostructure/Hypostructure/CT3/{Spec,Capability,State,Search,Execution,Theorems,Automation}.lean` and the underlying `Core/Response` modules used there.
3. Inspect `hypostructure/Hypostructure/Graph/CT3.lean` and `hypostructure/Hypostructure/Fixtures/CT3.lean`.
4. Confirm current declarations and a fresh `.olean`, for example with `cd hypostructure && lake env lean Hypostructure/Fixtures/CT3.lean`. A `kernel_checked` matrix row without matching live declarations is not availability.

The generic and Graph slices are currently implemented. No `Hypostructure/PDE/CT3.lean` adapter currently exists. If a required constructor, output branch, or PDE specialization is missing, do not rebuild it in an application; route the gap to `$extend-hypostructure-framework`.

## Build the queried capability

Define `CT3.Spec` with the representative, candidate, and row types; a `Core.Response.System`; exact `TargetSemantics`; candidate and row representatives; stored row responses; and the primitive `Admissible` and `StrictlySmaller` relations.

Supply `CT3.Capability` with four typed reads from the same literal predecessor:

- `source : Core.Residual.Query ... Representative`;
- `coordinates : Core.Residual.Query ... (Core.Finite.Enumeration Coordinate)`;
- `candidates : Core.Residual.Query ... (Core.Finite.Enumeration Candidate)`; and
- `rows : Core.Residual.Query ... (Core.Finite.Enumeration Row)`.

Also supply response-value equality, primitive admissibility and smaller deciders, symbolic coverage for each scheduled candidate and row, and a polynomial proof for `localCheckBound`. Use `Query.residual`, `latest`, `preserve`, `map`, `and`, or a framework-owned projection; never pass detached schedules to the executor.

Treat these semantic primitives, deciders, coverage laws, and work envelope as author primitives. Treat exact response tables, the selected compression or row evidence, terminal, trace, outcome, and ledger extension as framework outputs in `Core.Provision` metadata.

## Execute all four branches

1. Call `CT3.execute spec capability previous`.
2. Handle only generated outcomes:
   - `.compression` with `CompressionCertificate`;
   - `.distinguishing` with `UncompressibleState` and `DistinguishingCoordinate`;
   - `.knownRow` with `ExactTableState` and `KnownRowCertificate`; or
   - `.novelRow` with `ExactTableState` and `NovelRowState`.
3. Use `CompressionCertificate.target_iff` or `KnownRowCertificate.target_iff` for semantic target transport. Never infer global equivalence from coordinate equality without the registered coverage proof.
4. Prove `stage.previous` is literal, `result.verified`, `result.trace_exact`, `run_total`, `run_deterministic`, `outcome_exhaustive`, `checks_le_limit`, and `checks_le_polynomial`.

For graph gluing, use `Graph.CT3.targetSpec`, `coverageOfExactContexts`, `compression_target_iff`, and `knownRow_target_iff`. Do not enumerate outside graphs or contexts; provide a finite coordinate schedule and a theorem that it realizes the intended semantic contexts.

Use `Fixtures/CT3.lean` as the minimum: pin all four neutral terminals, exact checks and traces, every semantic outcome, polynomial work, and a Graph compression with target transport.

## Practicality and carrier rules

Use the exact bound `candidates * (2 + coordinates) + 2 * rows * coordinates`. Keep all three schedules small, proof-specified, and predecessor-owned. Never create a local universe of boundaried graphs, generated contexts, arbitrary replacements, or canonical rows merely to satisfy the interface; extend Core or the domain layer if the predecessor cannot expose the required family.
