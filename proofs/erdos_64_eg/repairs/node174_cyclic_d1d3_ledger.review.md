# Expansion review: node [174] cyclic component D1--D3 ledger

## Verdict

**PASS for the node-[174] Lean implementation.**  The repaired thin adapter
now consumes a typed node-`[173]` residual together with equality to the actual
node-`[173]` run, and the collision ledger uses that retained residual as its
anchor row.  The reusable graph implementation remains branch-total, local,
polynomial, and free of extra trust.

TeX--Lean--web synchronization is deliberately pending and was outside this
re-review's write scope.  Node `[175]` remains open.

This review makes no integration, TeX, web, README, or log edits.

## Artifact audit

Reviewed completely:

- `StructuralExhaustion.Core.FiniteCodeCollision`
- `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger`
- `StructuralExhaustion.Examples.InducedPathComponentD1D3Ledger`
- `Erdos64EG.P13SameWindowComponentD1D3Ledger`
- exact predecessors
  `Erdos64EG.P13SameWindowComponentBoundarySchedule` (node `[170]`) and
  `Erdos64EG.P13SameWindowComponentD1D3Observation` (node `[173]`)
- the corresponding node-`[170]` and node-`[173]` manuscript statements and
  scope remarks.

## Checks that pass

### Exact node-[170] structural input

`d1d3LedgerInput.base` is definitionally `transition.graphInput`.  The
adapter's `notBridge` field is derived from the same selected graph's
all-darts nonbridge theorem.  The graph layer filters the already declared
boundary-stub token order by equality with the anchor's one computed outside
component.  It does not replace this schedule with a cold-family schedule.

For each attached schedule entry, `connectorInput` changes only the anchor and
uses the supplied nonbridge proof.  `connector_schedule_eq` proves that every
row retains the original complete node-`[170]` incident schedule.

### True cyclic successor

`connector_successor_eq` identifies each row's successor with

```text
List.next (incidentStubs transition.graphInput) stub stub.member
```

on the original duplicate-free schedule.  Mathlib's `List.next_eq_getElem`
gives index `(idxOf stub + 1) % length`, so the final entry wraps to the first.
This is the true cyclic successor, not a tail-only or default successor.

### Genuine D1--D3 rows

The repaired graph runner accepts an explicit `anchorState`.  Its `rowState`
definition selects that retained value exactly at the original anchor and
computes the node-`[173]` graph operation only for re-anchored non-anchor rows.
The theorem `rowState_anchor` proves this projection definitionally.

The P13 source contains both
`node173 : P13SameWindowComponentD1D3Residual transition` and
`node173Exact : node173 = runP13SameWindowComponentD1D3Observation transition`.
`runD1D3Ledger` requires this source and passes `source.node173.value` to the
graph runner.  Thus the stored anchor row is the exact predecessor value, not
a post-hoc agreement theorem around a node-`[170]`-only execution.  Every
non-anchor row still stores its exact stub beside a genuine `State (Fin 0)`.
Each repeated row can recover its declared-order BFS connector and typed
`MissingD4D7Reconstruction` residual.

### Collision and branch totality

`FiniteCodeCollision.decideWithDecEq` recursively scans only pairs of codes
actually present in the supplied row list.  It returns either:

- an ordered collision with two distinct stored rows and equal coarse states;
  or
- a proof that the observed code list is duplicate-free.

The unique-code branch uses the finite state cardinal only as a proof bound,
yielding schedule length at most
`4^2 * 13^2 * 2^13`.  It never materializes or scans the complete state
universe.  The P13 output exhaustively preserves the repeated branch or the
corresponding `Qbase` length bound.  No CT8 removal, D4--D7 reconstruction,
target closure, or Boolean realization is claimed.

### Local computation and work

The implementation scans only:

- the supplied incident-stub list;
- the existing finite boundary-token list used to construct that schedule;
- one declared-order BFS computation per actual schedule row; and
- equality of the observed 17 coarse coordinates for actual row pairs.

It does not enumerate graphs, vertex subsets, paths, support families, or the
finite state universe.  `visibleChecks` conservatively charges every row and
`17 * rows.length^2` state-coordinate comparisons.  The formal theorem proves

```text
visibleChecks <= 100 * localScale^4.
```

The bound is an upper ledger, not a claim that the first-collision runner
always performs every possible comparison.

### Trust and builds

The following builds pass:

```text
lake build StructuralExhaustion.Core.FiniteCodeCollision \
  StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger \
  StructuralExhaustion.Examples.InducedPathComponentD1D3Ledger

lake build Erdos64EG.P13SameWindowComponentD1D3Ledger
```

`#print axioms` on the collision decision, cyclic-successor theorem, graph
runner, polynomial bound, P13 runner, source constructor, retained-anchor
projection, and actual-node-`[173]` equality reports only `propext`,
`Classical.choice`, and `Quot.sound`.  No application axiom or unproved
external mathematical theorem enters node `[174]`.

## Resolved failure: node-[173] predecessor provenance

The previous review found that the runner accepted only the node-`[170]`
transition.  The repair introduces the dependent source
`P13SameWindowComponentD1D3LedgerSource transition` with the exact typed
fields:

```text
node173      : P13SameWindowComponentD1D3Residual transition
node173Exact : node173 = runP13SameWindowComponentD1D3Observation transition
```

The public runner's checked type now has both `transition` and `source`
arguments and returns an output indexed by that source.  It passes the retained
`source.node173.value` into the generic ledger.  The generic `rowState` uses
that value at `anchorStub`; only other rows invoke re-anchored observations.
Theorems prove both anchor projection and equality of the retained value with
the actual node-`[173]` execution.  Deleting or changing the node-`[173]`
payload now changes the runner's required input and anchor code, so the
authored dependency `[170] -> [173] -> [174]` is enforced.

## Pending synchronization, not a Lean-review failure

The current manuscript says, in all relevant synchronized locations:

- diagram node `[174]`: “open”;
- dependency table row 16q: “open; dependency-ready but not implemented”;
- Part-XI caption: node `[174]` is white;
- node-`[173]` scope remark: node `[174]` is a future split.

The Lean implementation is now PASS-ready, but integration must update these
locations to state the exact two-way result: a repeated observed coarse state
on two distinct cyclic schedule rows, or the certified `Qbase`
schedule-length bound.  D4--D7 reconstruction and every use of the coarse
repetition must remain at open node `[175]`.

## Nonblocking observations

- The P13 bounded constructor intentionally drops the observed-code `Nodup`
  proof and retains only the `Qbase` length bound.  This is acceptable if node
  `[175]` consumes only the bounded schedule; the generic result still owns
  the stronger proof.
- The transfer example is theorem-independent and exercises exhaustive result,
  state cardinality, anchor agreement, and the polynomial work theorem.  It is
  a structural transfer rather than a concrete finite graph fixture, but no
  Erdős declaration leaks into it.
- `visibleChecks` is correctly described as a visible upper ledger.  Future
  synchronization should not call it the exact number of comparisons made by
  an early-stopping collision run.

## Final integration gate

The independent Lean review is complete.  Green synchronization may proceed
provided integration:

1. preserves the typed source and retained-anchor implementation reviewed
   here;
2. updates TeX, diagram status, theorem index, web export, tests, README/log,
   and node count without marking node `[175]` green.
