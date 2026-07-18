# Red-team audit: nodes [154]--[157] germ consumers

## Baseline and verdict

- Repair sketch: `nodes_154_157_germ_consumer_contracts.md`.
- Read-only specification hash:
  `30b6bbcea15c7ed42ba43e92780de6188bb3dc5b`.
- Failed full-node claim: every surviving selected cold incidence produces a
  bounded germ and every G2 defect is already a sparse/exit-(4) closure.
- Verdict: **PASS for the dependency-ready consumer contract; FAIL for green
  status of the complete nodes [153]--[157]**.  The implementation makes the
  first claim no stronger than a function from a supplied typed germ and keeps
  the second claim as a typed open handoff.

## Provenance and quantifier attack

| Used fact | Producer | Earlier and independent? | Verdict |
|---|---|---:|---|
| actual target cycle | `ColdDyadicHit` supplied by the local producer | yes, once supplied | CT1 consumer sound |
| one distinguishing outside context | `ColdContextDistinction` | yes, once supplied | G2 handoff sound |
| universal context equivalence | `ColdSilentExchange.targetComplete` | yes, once supplied | CT3 consumer sound |
| internal baseline/target freedom/decrease | remaining `ColdSilentExchange` fields | yes, once supplied | CT3 consumer sound |
| every graph germ is represented | no producer | no | deliberately not claimed |
| G2 has exit-(4) receiver/load/support/update | no producer | no | deliberately not claimed |

The central scan has the literal form

```text
for every outside context, there exists one local code representing both
piece responses in that same outside context.
```

It is not exchanged with simultaneous realization of arbitrary Boolean rows.
The code table is not presented as a surjection onto pieces or contexts.  A
single differing code yields one exact decoded outside witness; absence of a
differing code is transported to all contexts only through the supplied
coverage theorem.

Small countermodels rejected by the interface:

- thirteen equal offset bits with a context outside that signature that
  distinguishes the pieces cannot inhabit `ColdBoundedGerm.contextCoverage`;
- a target-defective pair without a receiver or charge update inhabits the G2
  handoff but cannot inhabit any claimed exit-(4) payload, because no such
  payload is defined here;
- a repeated coarse prefix state without packed reconstruction cannot inhabit
  `ColdSilentExchange.atom` and therefore cannot call CT3.

## CT and leaf audit

| Leaf | Exact trigger | Result | Verdict |
|---|---|---|---|
| G1 | actual `CycleWithLength` in `ctx.G` | C1 through existing CT1 | pass |
| G2 | exact two pieces and distinguishing context | typed target-defect residual | pass as handoff, not terminal |
| G3 | target-complete internally valid smaller replacement | C2 through existing CT3/minimality | pass |

CT7 is not re-run because the exact local Boolean scan plus symbolic coverage
already supplies its distinction/neutral dichotomy.  CT8 remains upstream: a
repeat can select two prefixes, but cannot manufacture packed reconstruction
or universal target equivalence.

`VerifiedRowRouting table row` is indexed by the exact CT10 row and stores an
equality to `routeRow table row`; hence the selected row is not lost in an
existential.  The dependent classifier ensures its distinction comes from the
decoded germ of that same row.

## Practicality, ownership, and trust

- Largest enumerated universe: the supplied germ-local context-code table and
  supplied CT10 row table.
- Ambient-size universe: none.
- Work: one finite response scan; CT1/CT3 each use their established one-check
  consumer; CT10 retains its established quadratic row-table bound.
- New code is an Erdős-specific thin composition of existing graph, route,
  CT1, CT3, and CT10 contracts; no framework API was changed.
- No `sorry`, `admit`, `axiom`, or new `Classical.choose` occurs in the new
  module.
- `original_erdos_64_proof.tex` was not edited.

## Checks

- `lake build Erdos64EG.P13ColdGermTableConsumers Erdos64EG.Tests`: pass after
  the concurrent `FiniteBoundedOverlap` edit settled.
- targeted `git diff --check`: pass.

## Exact remaining leaves

1. The F1--F5 producer must construct `ColdBoundedGerm` from the identical
   graph-owned selected incidence and prove graph-to-table coverage.
2. A G2-to-exit-(4) or G2-to-existing-ledger route must construct the receiver,
   routed load, quotient support, and charge update.  Until then G2 remains the
   admitted typed handoff and the aggregate cold branch is not closed.
