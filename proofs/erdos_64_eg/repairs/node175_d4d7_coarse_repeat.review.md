# Independent expansion review: node `[175]`

## Verdict

**NOT PASS / keep node `[175]` open.**

The candidate Lean implementation has sound predecessor provenance, honest
branch separation, a correct observed-row first-missing classifier, local
work, and no CT8 overclaim.  It nevertheless fails two mandatory clauses of
`node175_d4d7_coarse_repeat.prereview.md`:

1. the coarse-repeat and first-missing leaves do not name or execute a typed
   CT10/Routes (or equivalent typed downstream) consumer; and
2. the non-Erdős transfer executes only an abstract source and restates the
   three-way exhaustive result.  It supplies no fixture reaching either the
   repeated coarse-refinement leaf or the bounded first-missing leaf.

Node `[174]` remains the last unconditional green endpoint.  This review makes
no TeX, web, umbrella, README, test, or implementation-log integration.

## Reviewed artifacts

- `StructuralExhaustion.Core.FiniteObservedReconstruction`
- `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger`
- `StructuralExhaustion.Graph.InducedPathComponentD4D7OrCoarseRepeat`
- `StructuralExhaustion.Examples.InducedPathComponentD4D7OrCoarseRepeat`
- `Erdos64EG.P13SameWindowComponentD1D3Ledger`
- `Erdos64EG.P13SameWindowComponentD4D7OrCoarseRepeat`
- the node-`[174]` review and node-`[175]` prereview contract
- the current manuscript diagram, dependency row 16r, and detailed
  node-`[170]`--`[175]` dependency prose.

## Checks that pass

### Exact generic and specialized node-[174] provenance

`P13SameWindowComponentD4D7OrCoarseRepeatSource` retains:

- `graphSource.node174`, with equality to the exact generic
  `InducedPathComponentD1D3Ledger.run`; and
- `node174Exact`, proving that literal specialization of the same retained
  generic result equals `transition.runD1D3Ledger source174`.

The retained `source174` itself contains node `[173]` and equality to the
actual node-`[173]` execution.  Its graph input is definitionally the exact
node-`[170]` schedule.  Thus node `[175]` cannot be called from an arbitrary
ledger result or rebuilt node-`[170]` look-alike.

The repaired bounded constructor preserves both:

```text
codesNodup : (actualRows.map coarseState).Nodup
lengthLe   : actualIncidentSchedule.length <= stateCard
```

The P13 specialization additionally transports the same bound to `Qbase`.
No repeat is manufactured on this branch.

### Repeated branch is honest

`CoarseRepeatResidual` retains the exact node-`[174]` collision without
reselection.  The inherited repetition retains both stored rows, their exact
stubs, distinctness, equal `State (Fin 0)` values, re-anchored inputs, true
cyclic successors, declared-order BFS connector paths, and both
`MissingD4D7Reconstruction` markers.  The two anchor-membership questions are
decided locally.

The implementation does not claim:

- complete D4--D7 response equality;
- a CT8 removal or smaller object;
- a distinguishing compatible context;
- target closure, periodicity, termination, density, or Boolean realization.

Calling this constructor a *coarse observed repeat* is sound.

### Bounded branch scans actual rows and preserves first missing

`FiniteObservedReconstruction.classify` is a genuine ordered,
early-stopping recursion over its supplied list.  It returns either a
dependent reconstruction for every supplied row or an exact decomposition

```text
rows = priorRows ++ firstMissingRow :: suffix
```

with reconstructions for the prefix and failure at that exact row.

The graph application supplies only
`InducedPathComponentD1D3Ledger.stubs input`, the attached version of the
actual node-`[174]` incident schedule.  It does not enumerate the state
alphabet.  `FirstMissingReconstruction` retains the selected stub and the
corresponding computed connector's `MissingD4D7Reconstruction` marker.

`D4D7ClausesDerived` is explicitly a derivation-status proposition with no
constructor.  Its negative result must therefore be read only as “the current
graph layer has not supplied these clauses,” not as mathematical
nonexistence.  The source comments and result types respect that boundary;
there is no vacuous `DeclaredLocalSemantics`, `Fin 0` response map, or constant
Boolean semantic conclusion.

### Exhaustive leaves

The generic and P13 results expose exactly:

- repeated coarse-refinement residual;
- bounded reconstructed observed family; or
- bounded first-missing reconstruction residual.

Both exhaustive theorems follow by matching the actual runners.  The bounded
payload retains `codesNodup` and the original length bound in both bounded
constructors.

### Local computation and work

Node `[175]` scans only the actual attached stub schedule.  No executable term
enumerates all states, graphs, subgraphs, vertex subsets, paths, path
families, Boolean functions, or D4--D7 alphabets.  `Qbase` remains proof-only.

The visible ledger is the actual schedule length:

```text
visibleChecks = stubs.length <= D1D3Ledger.localScale.
```

This is a conservative visit bound.  With the current unavailable-clauses
decider, the bounded scan stops at its first actual row.  Connector/BFS data
are inherited from the node-`[174]` row machinery rather than obtained by a
new path-family search.

### Trust and focused builds

These checks pass:

```text
lake build StructuralExhaustion.Core.FiniteObservedReconstruction \
  StructuralExhaustion.Graph.InducedPathComponentD4D7OrCoarseRepeat \
  StructuralExhaustion.Examples.InducedPathComponentD4D7OrCoarseRepeat

lake build Erdos64EG.P13SameWindowComponentD4D7OrCoarseRepeat
```

The reviewed dependency cone contains no `sorry`, `admit`, unsafe proof
shortcut, or declared axiom.  `#print axioms` on the Core classifier, Graph
runner/exhaustiveness/work theorem, P13 runner/exhaustiveness theorem, and both
node-`[174]` provenance theorems reports only `propext`, `Classical.choice`,
and `Quot.sound`.  No HSS or new application axiom enters this local node.

## Blocking gap 1: no typed downstream consumer

The prereview contract requires every terminal to name its next typed
consumer and assigns finite missing-label/refinement routing to CT10/Routes.
The current implementation stops at:

- `Graph.InducedPathComponentD4D7OrCoarseRepeat.CoarseRepeatResidual`; and
- `Graph.InducedPathComponentD4D7OrCoarseRepeat.FirstMissingReconstruction`.

Neither residual contains a route trigger, route provenance, consumer kind,
CT10 input/run, or an equivalent typed continuation.  No file in the reviewed
dependency cone defines a route from either residual.  The module comments
call the repeated output a “CT10/refinement residual,” but that phrase is not
backed by a typed CT10 or Routes declaration.

This is not a semantic-unsoundness bug—the outputs are honest stopping
residuals—but it is insufficient progress for node `[175]`'s green contract.
The repair should couple the exact retained collision or exact first-missing
row to a real typed refinement trigger.  Any CT10 execution must use those
actual residual data; a fixed singleton/canned classification would remain
ceremonial and fail review.

## Blocking gap 2: transfer does not exercise material branches

`StructuralExhaustion.Examples.ComponentD4D7OrCoarseRepeat` is independent of
Erdős declarations and invokes the public graph runner.  However, its source
is abstract and definitionally fixed to the preceding generic ledger run.  It
proves only:

- the runner's generic exhaustive disjunction; and
- the definition of the visible work ledger.

It does not provide a repeated fixture, a bounded fixture, a theorem that the
first missing row is the first actual row, or a branch-specific check that the
retained residual exposes both connectors/markers.  Therefore it does not
meet the prereview requirement that a theorem-independent example execute all
materially different generic branches.

A green repair needs, at minimum:

- a Core fixture for both complete and first-missing ordered scans;
- a graph-level repeated fixture or theorem consuming an explicit exact
  repeated predecessor result and checking pair provenance; and
- a bounded graph fixture/theorem checking preservation of `codesNodup`,
  `lengthLe`, and the exact first missing actual row.

## Synchronization status

The manuscript and diagram still describe node `[175]` as open/white and node
`[174]` as the implemented split.  That is consistent with this negative
review.  Because integration was explicitly excluded, no compiled yellow-set
or crosswalk mutation was attempted.

## Required repair before PASS

1. Add a typed, data-coupled refinement route for both stopping residuals.
2. Retain route execution/provenance and any validity/trace theorem supplied
   by the selected consumer; do not claim CT8 response equality.
3. Add theorem-independent branch fixtures for repeated and bounded
   first-missing behavior, plus Core complete/first-missing coverage.
4. Re-run focused builds, placeholder/locality scans, and `#print axioms`.

Until those repairs exist, node `[175]` must remain open and must not be added
to `formalizedNodeIds`.
