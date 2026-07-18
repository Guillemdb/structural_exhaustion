# Missing target-aware cold-corridor congestion lemma on `[152] -> [153]`

## Claim tested

The original cold-germ extraction deletes the selected branch-excess
half-edges whose cyclic-successor corridors meet a high vertex and treats the
deleted family as `o(n)` because
`sigma(G) = sum_v (degree(v) - 3) = o(n)`.  For this deduction one needs a
uniform degree- or stub-weighted congestion estimate of the form

```text
number of selected successor corridors meeting high vertices
  <= C * sum_v (degree(v) - 3)
```

with `C` independent of the graph.  The current graph-owned construction in
`InducedPathRestrictedComponentBoundarySchedule` orders the actual boundary
stubs, takes their cyclic `List.next`, and chooses the declared-order BFS-tree
shortest path between each pair.  Its API provides no family-overlap theorem.

## Counterexample to the degree-only path-system claim

Fix an arbitrary even number `W` of ambient-cubic cold windows.  Construct one
outside component `K` as follows.

- Take two long cycles `L` and `R` sharing exactly one vertex `h`.
- On each cycle, the two edges incident with `h` are distinct, so `h` has
  degree four in `K`; every other cycle vertex initially has degree two.
- The `15W` external stubs of the `W` cold windows have distinct outside
  endpoints on `L - {h}` and `R - {h}`.  Give each such endpoint one stub, so
  it has ambient degree three.
- Choose the declared token/vertex order so these boundary stubs alternate
  between `L` and `R`.  Since `15W` is even, the cyclic wrap also alternates.
  Within every window the first two entries are its transit stubs and the
  remaining thirteen are its selected branch-excess stubs, exactly as at node
  `[152]`.

Every cyclic-successor pair has one endpoint in `L - {h}` and the other in
`R - {h}`.  Removing `h` separates these sets.  Therefore **every** path
between the pair contains `h`; in particular the graph-owned lexicographic
BFS shortest path contains `h`, independently of all tie-breaking.

Consequently all `13W` selected branch-excess corridors meet the single high
vertex `h`, whereas its surplus weight is

```text
degree(h) - 3 = 1.
```

All other outside endpoints are cubic.  Thus the ratio between high-hit
selected corridors and the available high-center surplus is at least `13W`,
which is unbounded.  The construction can be made bridgeless: each side is a
cycle through `h`, and every cold window has fifteen distinct attachments to
the same connected outside component, so deleting one attachment does not
disconnect it.

This is a counterexample to a **degree-only** congestion lemma for the exact
cyclic-successor/BFS path system.  It is not certified target-avoiding and is
not a counterexample to the surviving Erdős--Gyárfás branch.  It therefore
does not refute a stronger theorem that also assumes the exact F1--F3
negatives.

## F1 red-team

The elementary obstruction is not automatically removed by F1.  Replace each
side of the shared center by a cubic branching network whose boundary
endpoints are leaves at a common distance `R = 2^k` from `h`.  Put the window
stubs only at those leaves, two stubs from distinct windows per leaf, and keep
the declared order alternating between the two sides.  Every cross-side BFS
path still contains `h`, while no internal path vertex is adjacent to an
anchor window.  The only possible same-window F1 completion is at the final
successor leaf.  Its length is

```text
2R + 2 + d,    0 <= d <= 12,
```

where `d` is the distance between the two window offsets.  For `k >= 4`, this
lies strictly between `2^(k+1)` and `2^(k+2)`, so it is not a power of two.
The positive-stage guard also excludes the zero-length start.  Thus the local
F1 arithmetic by itself supplies no congestion bound.

This uniform-depth construction is again only a path-system/F1 test.  It has
not been proved to satisfy every global target-avoidance, minimality, F2, and
F3 hypothesis of the surviving counterexample.  In particular it must not be
cited as a counterexample to a theorem assuming all those hypotheses.

## Exact formalization blocker

The center-level bridge is valid: an actual high result produces the literal
surplus slot `(h, 0 : Fin (degree(h) - 3))`.  What fails is occurrence-level
payment.  Many different node-[152] sources can map to that same slot.

The only paper-faithful remaining F4 route would be a branch-level coverage
theorem saying that every first high corridor endpoint belongs to an actually
produced ordinary Type-B, decorated Type-B, or route-8 support.  The current
canonical ordinary family does not prove this:

- it contains only remainder components satisfying negative charge,
  `NoHigherCenter`, and `CenterDeletedUnsaturated`;
- a restricted cold corridor may pass through a hot packed window, so its high
  center is not even known to lie in the packing remainder; and
- the produced-prior ordinary ledger stores node-[64]
  `VerifiedNode64Residual` values, while the canonical node-[84] family exposes
  `OrdinarySupportSource` values, with no coverage/recording connector between
  them.

The stable canonical APIs make the missing hypotheses exact.
`CanonicalOrdinary.exists_occurrence_of_eligible_component` constructs the
desired occurrence only after receiving both a canonical remainder-component
index containing the vertex and the complete `Eligible` proof for that
component (negative charge, `NoHigherCenter`, and
`CenterDeletedUnsaturated`).
`CanonicalOrdinary.occurrence_has_exact_source` then identifies the node-[84]
source.  A high result on a restricted corridor supplies neither premise, and
there is still no theorem recording that node-[84] source as one of the
node-[64] ordinary events accepted by `P13ProducedPriorSupportLedger`.

Therefore the original `[152] -> [153]` edge currently lacks both available
justifications for deleting all high-hit corridor occurrences.  Degree-only
congestion is false for the selected path system, and F1 exclusion alone does
not repair it.  The paper-faithful possible rescue is the following missing
existing-edge theorem:

> For the literal node-[152] schedule, after the stage-major F1 scan and under
> the exact F2 and F3 negative semantics, the selected corridors whose first
> high vertex is not already contained in a produced Type-B/decorated-Type-B/
> route-8 support have total cardinality bounded by a fixed constant times the
> inherited degree-surplus ledger.

No current Graph or Erdős declaration proves this implication.  Proving it
would be an internal support lemma for the existing F4/F5 extraction, not a
new case or edge.  Until it is proved, the exhaustive F4 support producer is
also absent, so node [153] remains conditional.

## Red-team checklist

- Repair sketch: derive the high-hit deletion from the existing F1--F4
  sequence, without a new branch.
- Failed node and claim: `[152] -> [153]`, the `o(n)` deletion of selected
  corridors meeting high vertices.
- Incoming facts retained: literal node-[152] sources, cyclic successor,
  graph-owned BFS path, target avoidance, stage-major F1--F4 priority, and the
  inherited surplus and produced-support ledgers.
- Quantifier attack: the required map is from **corridor occurrences** to
  paid/recorded incidences.  The available surplus map is only from a high
  center to one slot and is not injective on corridor occurrences.
- Small countermodel result: the shared-center construction refutes the
  degree-only statement.  Its uniform-depth form also avoids every local F1
  completion in the selected paths.  Neither model is certified against the
  full target-avoidance/F2/F3 hypotheses.
- Cross-branch leakage: canonical node-[84] ordinary coverage cannot be used
  without first proving remainder membership and `Eligible`; those are not
  fields of a corridor-high result.
- Positive-side account: still missing—the target-aware congestion theorem
  displayed above.
- Negative-side consumer: existing F4 produced-support ledger, but exhaustive
  producer coverage is missing.
- Computation: all inspected schedules are the actual finite stub and prefix
  schedules; no ambient graph or context universe is enumerated.
- Topology: no new case, edge, outcome, or residual is proposed.
- Trust: the center-level Lean bridge is kernel-checked with only `propext`,
  `Classical.choice`, and `Quot.sound`; the target-aware bound has no Lean
  declaration.
- Verdict: **FAIL**.  The first exact obligation returned to the repair loop is
  the target-aware F1--F3-negative congestion/coverage theorem above.  The
  degree-only refutation is not promoted to a refutation of the surviving
  manuscript branch.
