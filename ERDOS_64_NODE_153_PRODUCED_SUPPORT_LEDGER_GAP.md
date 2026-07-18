# Node [153] produced-support ledger coverage

Authority: the existing F4 edge inside node `[153]` in
`proofs/erdos_64_eg/erdos_64_proof.tex`, together with the ordinary Type-B,
decorated Type-B, and route-8 producers already named by that edge.

## Implemented dependency-ready aggregation

`P13ProducedPriorSupportLedgerCoverage.lean` now proves the following without
adding a diagram case or deduplicating occurrences.

- An ordinary node-`[64] -> [65]` occurrence schedule maps to an exact ledger;
  every occurrence remains present even when two occurrences have equal
  supports.
- Every grouped decorated support in a supplied exact node-[84]
  `Realization` is converted to `RecordedDecoratedHandoff` with the identical
  source, center, first-neighbour family, arms, and semantic predicates.
- Every support marked `extracted` by that same realization is converted to
  the exact stored `RouteEightExtraction`. The route-8 ledger is the filtered
  realization support schedule, not a caller-supplied event list.
- `CompleteState` computes one persistent tagged occurrence ledger from the
  three schedules and proves membership for every source occurrence. Absence
  from this ledger implies absence from every literal source occurrence. No
  equality between the generic sum enumeration order and list concatenation
  is assumed.
- `completePriorD6State` passes the identical combined ledger to the existing
  D6 scan, and
  `exists_localCorridorSurvivor_of_completeProducedLedger` enters the existing
  `LocalCorridorSurvivor` constructor under the original subcubic and F4
  exclusions.

All scans are over supplied producer schedules. No ambient vertex subset,
path family, context universe, or graph family is enumerated.

The storage and recognition mechanism is now framework-owned:
`Core.FiniteResidualLedger` provides the persistent occurrence universe and
dependent attachments, while `Graph.FiniteResidualSupportLedger` provides
exact support recognition. The Erdős module contains only the event/support
specialization and thin producer adapters. The list-valued D6 ledger is a
compatibility materialization of the same persistent base, not separately
authored state.

## Exact remaining producer

### 2026-07-17 append-produced ordinary schedule audit

The finite scheduling layer is now framework-owned and executable.  Core
defines an occurrence-preserving producer schedule, its exact ledger, a
singleton emitter, and schedule append.  The append occurrence type is a
tagged sum, so two different node-[64] executions remain distinct even when
they emit equal residuals or equal declared supports.  The Erdős ordinary
schedule is a thin specialization to `VerifiedNode64Residual`; it exposes the
exact singleton created by one `[64] -> [65]` execution and append composition
for an upstream branch-produced sequence.  A non-Erdős example proves that
two equal emitted entries retain distinct occurrence identities.

This closes the finite-data and support-identity part of the producer.  It
does not construct the upstream sequence of executions.

The repository still does not construct the inputs needed to make the
connector unconditional:

1. There is no graph-owned branch runner that appends every actual ordinary
   node-`[64] -> [65]` residual.  Each individual output can now be emitted
   and schedules can be composed without loss, but no predecessor currently
   supplies the complete execution sequence.
2. `Node84GlobalFanMass.Realization` contains complete ordinary/grouped and
   extracted-support schedules, but no theorem currently constructs such a
   realization from all actual node-[65] ordinary and node-[108] decorated
   entries. Its own comment and the implementation log identify this as the
   open global Type-B support-family producer.

Consequently XI-153-08 is strengthened but remains partial. Once the existing
node-[84] global-family producer supplies the realization and the ordinary
branch runner folds its literal outputs through the new singleton/append
operations, the connector makes F4 ledger coverage branch-total
definitionally. Until then, a negative D6 scan cannot be promoted to absence
from every earlier produced support.

The filtered canonical node-[84] component family cannot fill this gap: it is
defined using later negativity, no-higher-center, and unsaturated predicates.
Using it as the earlier `[64] -> [65]` production sequence would erase entries
that leave through those later alternatives and would reverse the manuscript's
dependency order.

### Earliest upstream source-list blocker

A repository-wide predecessor trace finds exactly one executable ordinary
route: `TypeANode63Support.routeCanonicalNode61Node62`.  It consumes one
`CanonicalQuarterLedger`, localizes one node-[61] component, and returns one
tagged node-[62] result.  Its Type-B constructor contains one exact node-[64]
residual.  It neither iterates a branch family nor returns a list, and the
Type-A constructor contains no ordinary event to append.

Moreover, `CanonicalQuarterLedger.pressure` is the strict-quarter node-[24]
handoff.  The node-[153] F4 ledger is itself part of the cold producer still
needed by the current node-[24] proof.  Therefore this one local route cannot
be iterated to construct the earlier F4 branch state without circularly
assuming node [24].  The repository contains no earlier finite domain of
ordinary executions, no list-valued node-[62] traversal, and no completeness
theorem relating such a traversal to all actual ordinary outputs.

Consequently the graph-owned runner cannot presently be implemented.  Its
first missing input is the original-branch finite source schedule produced
before the cold F4 consumer, with one exact node-[61]/[62]/[64] result per
execution.  Inventing this domain from all components, all supports, or the
later node-[84] family would either enumerate possibilities rather than actual
outputs or change the manuscript dependency order.

## 2026-07-17 independent pre-node-[24] population audit

The earliest possible population point was re-audited against the immutable
diagram, the exact Lean constructor types, and the Part-XI use of F4. No
graph-owned producer of **actual existing-edge occurrences** can run before
node `[24]` without reversing a manuscript dependency.

The causal chain is exact:

```text
[24] -> [48] -> ... -> [56] -> [57] -> [58] -> [59] -> [61] -> [62]
                                                        |        |
                                                        |        +-> [64] -> [65]
                                                        +-> [63] -> ... -> [108] -> [66] -> [65]
                                                                       |
                                                                       +-> [84]
```

This is not inferred merely from node numbering. The Lean types retain the
same dependency:

- `TypeANodes57To63Provenance.node57` consumes
  `VerifiedP13WindowDensityOutput`, the exact node-`[24]` result;
- `canonicalLedger` obtains its strict negative total only from
  `p13ClosureRobustPartIV node24`;
- `P13NegativeSupportLocalization.canonicalNode61` requires that
  `CanonicalQuarterLedger.pressure` in order to prove that the canonical
  component sum is negative and select the actual first negative component;
- `TypeBEntryRouting.node64` consumes that selected node-`[61]` occurrence and
  the exact yes result of its node-`[62]` scan;
- `TypeANodes107To108Handoff.VerifiedNode107Residual.node108` consumes one
  already produced node-`[107]` survivor and does not enumerate survivors.

The graph-owned canonical remainder-component order is available without the
strict-quarter proof, and it is local and linear. That fact does not solve the
population problem. Before the negative-total handoff it is only a list of
component **candidates**. Filtering it for locally negative components or
high centers would not be the execution trace of the original node `[61]`
choice followed by node `[62]`; it could contain components that the directed
run never selected. Recording those candidates as F4 events would replace
“support emitted by an existing `[64] -> [65]` edge occurrence” with “support
that could have emitted such an occurrence.” The negative F4 result would
then be an over-approximation with no manuscript provenance, while a positive
result would not be a valid existing handoff.

The later canonical node-`[84]` family cannot be reused for the same reason and
for an additional one: its `Eligible` predicate includes node-`[84]` branch
conditions (`NoHigherCenter` and `CenterDeletedUnsaturated`) evaluated after
the node-`[65]` continuation. It is a fan-mass accounting family, not the
earlier `[64] -> [65]` production trace. The decorated half is even later:
the repository has only the one-value map

```text
one supplied VerifiedNode107Residual -> one exact node-[108] handoff,
```

and no graph-owned finite schedule of the supplied node-`[107]` survivors.

Part XI says that F4 transfers to “already named” Type-B or route-8 handoffs,
but the diagram contains no incoming edge from `[64]`, `[84]`, or `[108]` to
node `[153]`. Node `[153]` is part of the hot/cold expansion behind nodes
`[22]--[24]`; using the later Part-V--VIII occurrences to prove that expansion
would therefore be circular. “Already named” cannot be strengthened to
“already produced on this execution” without a new backward edge, which is
forbidden by the specification.

Accordingly no thin Lean producer or focused producer test was added by this
audit. The existing `Ordinary.singleton` and append operations remain the
correct population API **after** an actual node-`[64]` value exists. The
earliest missing datum is still a predecessor-owned occurrence schedule on a
directed path into the Part-XI F4 consumer. Such a path is absent from the
original diagram; scanning ambient supports, paths, or possible branch states
would neither create it nor satisfy the local-computation rule.
