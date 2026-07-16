# Independent review: node [182] D4--D7 clause schedule

## Verdict

**PASS after one review-local repair.**

Node [182] is only a dependent obligation scheduler.  It consumes the exact
node-[180] branch, preserves every `MissingD4D7Reconstruction` marker, and
attaches the fixed duplicate-free order

```text
D4, D5, D6, D7.
```

It does not prove any clause or manufacture a response map, compatible
context family, removal operation, smaller object, or CT8 terminal.  Those
semantic obligations remain white node [185].

## Provenance and marker dependency

The Erdős source stores both
`node180 : D4D7SemanticReadinessOutput` and
`node180Exact`, identifying it with the actual
`runD4D7SemanticReadiness` result on the same transition and exact node-175
chain.  The runner eliminates only that dependent value:

- a coarse block yields two ledgers indexed by exactly
  `blocked.firstMissing` and `blocked.secondMissing`;
- a bounded block yields one ledger indexed by exactly `blocked.missing`.

Each `Ledger` retains `marker : Nonempty Marker` with
`markerExact : marker = source`.  The dependent marker is therefore not
erased to `Unit`, even though the current graph marker structure itself has
only its default `Unit` field.  Each ledger also retains `slotsExact`,
`slotsNodup`, and length four.

## Locality and work

The graph runner pattern matches one already computed node-[180] constructor
and creates four constant slots per actual marker occurrence.  Thus the
coarse branch emits eight slots and the bounded branch emits four.  No local
predicate is evaluated and no path, response, context, state, subgraph,
graph, coloring, or ambient universe is enumerated.

The original Erdős work theorem was a tautology: it defined the budget as
eight and proved `8 ≤ 8`, without mentioning the computed output.  The review
replaced it by:

```text
D4D7ClauseScheduleOutput.emittedSlots
runD4D7ClauseSchedule_emittedSlots_le_eight
```

The repaired theorem measures the actual returned ledgers and proves their
combined list length is at most eight.

## Ownership, transfer, and trust

The reusable slot type, marker-preserving ledger, dependent runner, and work
bound live in `Graph.InducedPathComponentD4D7ClauseSchedule`.  The Erdős file
only instantiates the exact transition payload.  The theorem-independent
`Examples.ComponentD4D7ClauseSchedule` consumes the same graph runner from
the exact non-Erdős semantic-readiness computation, checks totality, marker
identity, exact order, duplicate-freeness, and the eight-slot bound.

Focused framework, transfer, and Erdős builds pass.  `#print axioms` reports
no axioms for `ledger`, and only `propext`, `Classical.choice`, and
`Quot.sound` for the graph runner, totality theorem, Erdős runner, repaired
work theorem, and verified prefix.  There is no HSS dependency, `sorry`,
`admit`, unsafe declaration, or new axiom in this node.

## Validation

```text
cd lean
lake build StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseSchedule \
  StructuralExhaustion.Examples.InducedPathComponentD4D7ClauseSchedule

cd examples/erdos_64_eg
lake build Erdos64EG.P13SameWindowComponentD4D7ClauseSchedule
lake env lean /tmp/ReviewNode182Axioms.lean
```

Shared integration files were not edited.
