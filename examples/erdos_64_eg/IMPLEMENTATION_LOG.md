# Erdős Problem 64 implementation state

This ledger records the proof content currently checked by Lean in
`examples/erdos_64_eg`. A declaration is listed as verified when it compiles
without admissions and proves its stated result from its displayed
mathematical inputs. This does not mean that `Erdos64EG.OfficialStatement` has
been proved: the package currently contains a partial proof implementation.

Parameterized framework theorems are separated from the unconditional Erdős
frontier. In particular, accepting an author contract that contains the
missing problem-specific data does not count as verifying the corresponding
manuscript stage.

## Official statement and executable target

The public boundary is:

- `Erdos64EG.OfficialStatement`, the pinned Mathlib `SimpleGraph` proposition
  asserting a cycle of length `2 ^ k`, with `k ≥ 2`, in every finite graph of
  minimum degree at least three.

The following problem adapters are fully proved:

- `Erdos64EG.Internal.powerOfTwoLength_iff` proves that the bounded executable
  exponent representation `PowerOfTwoLength` is equivalent to the unbounded
  exponent predicate in the public statement.
- `Erdos64EG.Internal.target_iff_official_conclusion` proves, for every
  `Graph.FiniteObject`, that the internal target is exactly the conclusion of
  `OfficialStatement` for the same Mathlib graph.
- `Erdos64EG.Internal.staticInput` instantiates
  `Graph.MinimumDegreeCycle.StaticInput` with minimum degree three and the
  proved executable power-of-two length predicate.

These declarations establish a faithful executable boundary. They do not
establish that an arbitrary graph satisfying the minimum-degree hypothesis has
the target.

## Verified local CT results

### CT1: explicit target-certificate validation

The concrete Erdős declaration is `Erdos64EG.Internal.runCT1`.

- Input provenance: an `Internal.Object`, its minimum-degree baseline proof,
  and an explicit `Graph.CycleWithLength` whose length satisfies
  `PowerOfTwoLength`.
- Framework surface:
  `Graph.MinimumDegreeCycle.StaticInput.targetEncoding`, which is a
  `CT1.TargetCertificateEncoding`.
- Execution result: `CT1.CertifiedC1Run` at terminal `C1`.
- Typed trace: entry, equivalence certification, realization decision, and the
  `C1` terminal.
- Work bound: exactly one primitive certificate check, exposed by
  `CertifiedC1Run.checks_eq`; the reusable degree-zero certificate budget is
  `CT1.certifiedC1Budget`.
- Semantic result: the accepted certificate decodes to the exact internal
  target, which is connected to the official conclusion by
  `target_iff_official_conclusion`.

`Erdos64EG.Tests.k4CT1Run` is the executable fixture. Its input is the complete
graph on `Fin 4`, the proved minimum-degree baseline, and the explicit cycle
`0-1-2-3-0`. The fixture validates that supplied four-cycle; it is not a search
for a cycle in an arbitrary graph.

In the manuscript flow this reaches the target-cycle terminal represented by
node `[7]` only after a cycle certificate is already available. It does not
formalize the Mersenne return set or the edge-rooted return equivalence at
nodes `[5]`--`[7]` (`lem:return-equivalence`).

### CT2: deletion criticality from minimality

The concrete Erdős declarations are:

- `Erdos64EG.Internal.ct2Capability`;
- `Erdos64EG.Internal.ct2DeletionRule`;
- `Erdos64EG.Internal.heavyDartRun`; and
- `Erdos64EG.Internal.deletionCriticality`.

Their reusable implementation is
`Graph.MinimumDegreeCycle.StaticInput.ct2DeletionRule`. For a dart whose two
endpoints have degree at least four, the graph layer proves:

- deleting the dart strictly decreases the edge-count rank;
- endpoint slack preserves minimum degree at least three; and
- any accepted cycle in the deleted graph maps back to an accepted cycle in
  the original graph.

`heavyDartRun` executes the deletion-only CT2 path. Its terminal is
`deletionC2`, its typed trace is entry, deletion decision, and the deletion-C2
terminal, and its work is exactly one local check; the reusable certificate is
`CT2.localDeletionBudget`.

`deletionCriticality` proves that every dart in a
`Core.MinimalCounterexampleContext` has a degree-three endpoint. This is the
first assertion of manuscript `lem:deletion-critical` at node `[9]`. The proof
is complete for every supplied minimal-counterexample context: the context
contains the minimum-degree baseline, target avoidance, and the rank
minimality kernel consumed by CT2.

The Erdős package does not currently construct that
`MinimalCounterexampleContext` from an assumed counterexample to
`OfficialStatement`. Consequently this CT2 theorem is a verified local
consequence of the framework minimality interface, but it is not yet connected
to CT1 or to a formalized lexicographically minimal Erdős counterexample. The
high-degree-independence corollary at node `[10]` is not exported as a separate
Erdős theorem.

## CT3 reusable surface

`Erdos64EG.Internal.BoundariedCompressionContract` specializes
`CT3.TargetCompressionContract` to the exact Erdős target. Given a value of
that contract, the following declarations are fully generic and checked:

- `targetResponse_eq_true_iff`;
- `sameResponse_target_iff` and `sameResponse_targetIncluded`;
- `runCT3_checkLimit`;
- `runCT3_verified`;
- `runCT3_traceValid`; and
- `runCT3_total`.

The Erdős package contains no concrete value of
`BoundariedCompressionContract`. It therefore does not yet define the
manuscript's boundaried atoms, compatible contexts, finite response
coordinates, candidate representatives, canonical rows, gluing operation, or
strict lexicographic decrease as concrete Lean data. No Erdős CT3 execution is
present.

Accordingly, manuscript nodes `[11]`--`[14]` and
`def:boundaried-gluing`, `lem:degree-profile-fibres`,
`lem:context-universality`, `lem:replacement`, and `cor:uncompressible` are not
part of the unconditional verified frontier.

## Current manuscript-flow frontier

| Manuscript flow | Current Lean status |
|---|---|
| Nodes `[1]`--`[3]`: finite graph and official target | The proposition and its exact executable target bridge are defined and proved equivalent; the proposition itself is open. |
| Node `[4]`: choose a lexicographically minimal counterexample | The generic `MinimalCounterexampleContext` type exists; no Erdős constructor from an assumed counterexample is present. |
| Nodes `[5]`--`[7]`: Mersenne-return target algebra | An explicit dyadic cycle can be validated by CT1; the return-set definitions and `lem:return-equivalence` are not formalized. |
| Node `[8]`: no proper core | `lem:no-proper-core` is not formalized in the Erdős package. |
| Node `[9]`: deletion criticality | `deletionCriticality` is proved for a supplied minimal-counterexample context. |
| Node `[10]`: high-degree independence | The consequence is not exported as an Erdős Lean theorem. |
| Nodes `[11]`--`[14]`: boundaried replacement and uncompressibility | Only the parameterized CT3 author surface is present; no concrete Erdős contract or execution is present. |

There is currently no composed CT execution from the hypotheses of
`OfficialStatement` through CT1, CT2, and CT3. CT1 and CT2 share the exact
internal problem, while their current inputs are independent: CT1 consumes a
target certificate and CT2 consumes a minimal-counterexample context. CT3
imports the preceding modules but does not consume a CT2 execution result.

The next dependency-ready manuscript theorem is the section *Target cycles as
Mersenne returns*, specifically `def:mersenne-return-set` and
`lem:return-equivalence` at nodes `[5]`--`[7]`. Connecting the verified CT2
result to the global contradiction setup also requires constructing the Erdős
minimal-counterexample context and formalizing the node `[8]` proper-core
consequence.

## Independent API reuse

The reusable APIs used by this package have non-Erdős instantiations:

- `examples/even_cycle/EvenCycleExample/CT1Instance.lean` and
  `CT2Audit.lean` reuse `Graph.MinimumDegreeCycle.StaticInput` for the even-cycle
  target and prove the corresponding deletion-critical invariant.
- `EvenCycleExample.SeriesReduction.contract` is a concrete
  `CT3.TargetCompressionContract` for the textbook parity-series reduction.
  It executes CT3 over four response coordinates, proves compression and
  known-row terminals and typed traces, and has exact check limit `28` with a
  degree-zero polynomial bound.

These examples verify transfer of the graph and CT APIs. They do not supply
the missing Erdős manuscript data.

## Validation

The current declarations and framework catalog pass:

```text
make lint
  OK: CT1--CT17 expose only automation-first canonical APIs

make erdos-example-build
  Build completed successfully (1312 jobs).

make even-cycle-example-build
  Build completed successfully (1342 jobs).

python3 tools/validate_repository.py --root .
  OK: 17 automation-first Lean tactics, 124 nodes, 108 typed edges,
      36 residual kinds, 4 generated routes, 0 manual node obligations
```

The Erdős modules and the shared `MinimumDegreeCycle` profile contain no
`sorry`, `admit`, or added axioms.
