# Independent cross-review: node [191] D4 evaluator residual

## Verdict

**PASS.** No code repair was required. Node [191] consumes the exact
node-[188] request output and records only the two missing inputs required
before a graph-owned D4 evaluator could exist. It neither defines nor accepts
an evaluator or truth value.

## Exact node-[188] provenance

`D4EvaluatorResidualSource` stores the dependent node-[188] output and an
equality with `runD4LocalClauseRequest` on the identical transition and full
node-174/175/180/182/185/188 source chain. The node-[191] runner eliminates
that stored value itself. `d4EvaluatorResidual_exact_node188` exports the
source equality, and the computed source is definitionally the actual
node-[188] runner.

No canonical output can be built from an unrelated request family.

## Request, marker, and tail preservation

| node-[188] branch | retained dependent data | node-[191] residuals |
|---|---|---|
| coarse | block, first/second ledgers, first/second cursors, first/second requests | one residual indexed by each exact request |
| bounded | block, ledger, cursor, request | one residual indexed by that exact request |

Each `Residual pending` proves:

- `marker = pending.marker`;
- `slots = pending.slots`;
- `tail = pending.tail`; and
- `needs = [graphLocalPredicate, predicateProvenance]`, with no duplicates.

Through node [188], `pending.marker` is the cursor marker and dependent ledger
marker, `pending.slots = [D4]`, and `pending.tail = [D5,D6,D7]`. Thus neither
marker occurrences nor the unprocessed tail can be exchanged or erased.

## Precise missing requirements

The first tag, `graphLocalPredicate`, requires the future consumer to supply a
predicate derived from the actual graph-local request. The second,
`predicateProvenance`, requires a proof that this predicate has that graph
origin. At node [191] these are deliberately only ordered obligation tags.

There is no function field, `Bool` term, proposition purporting to evaluate D4,
caller-supplied value, compatible context, response map, response equality,
removal operation, smaller object, or CT8 certificate. The tags therefore
cannot be mistaken for satisfying their own requirements.

## Multiplicity and local bound

Each actual request receives exactly two tags. The concrete returned output
therefore contains four tags in the coarse two-request branch and two tags in
the bounded one-request branch. `requiredInputs` reads the actual residual
lists, and the Erdős theorem proves the uniform bound at most four.

The runner performs one constructor inspection and copies fixed lists. It
enumerates no vertices, paths, contexts, states, functions, response tables,
colorings, graphs, finite types, or ambient universes. The four bound is an
obligation-list size, not evaluation work.

## Framework ownership and transfer

The reusable residual, dependent runner, totality theorem, and local bound
live in `Graph.InducedPathComponentD4EvaluatorResidual`. The Erdős file is a
thin exact-source wrapper.

`Examples.ComponentD4EvaluatorResidual` executes the graph runner on the
independent component fixture and checks totality, exact D4 slot, D5--D7 tail,
the ordered requirement pair, and the same local bound.

## Validation and trust

Focused builds pass:

```text
lake build StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorResidual \
  StructuralExhaustion.Examples.InducedPathComponentD4EvaluatorResidual
lake build Erdos64EG.P13SameWindowComponentD4EvaluatorResidual
```

The scoped scan finds no `sorry`, `admit`, `unsafe`, new axiom, executable
`Bool`, `Fintype`, `Finset.univ`, or `Set.univ`. Evaluator/Boolean mentions are
negative scope comments only. Diff checks are clean.

`#print axioms` reports no axioms for `residual`. Graph and Erdős runners,
totality/bound theorems, and the verified-prefix theorem use only `propext`,
`Classical.choice`, and `Quot.sound`. There is no HSS dependency.

Shared integration, WebExport, topology, TeX, README, and implementation-log
files were not edited.
