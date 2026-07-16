# Independent cross-review: node [185] D4--D7 clause cursor

## Verdict

**PASS.** No repair was required. Node [185] is an exact, total structural
consumer of node [182]. It focuses the literal head of each fixed ledger and
does not assign a truth value or response meaning to any clause.

## Exact node-[182] provenance

`D4D7ClauseCursorSource` stores
`node182 : D4D7ClauseScheduleOutput source174` and the equality

```text
node182 = runD4D7ClauseSchedule source174 source175 source180 source182.
```

The right-hand side uses the identical transition and the full node-174,
node-175, node-180, and node-182 source chain. `runD4D7ClauseCursor` eliminates
that stored `node182` value itself. The theorem
`d4d7ClauseCursor_exact_node182` exports the source equality unchanged, so the
adapter cannot accept an unrelated author-supplied schedule as the official
predecessor.

## Dependent marker and ledger audit

| node-[182] branch | retained dependent data | node-[185] output |
|---|---|---|
| coarse | `blocked`, `Ledger blocked.firstMissing`, `Ledger blocked.secondMissing` | the same blocked value and both same ledgers, each with its own cursor |
| bounded | `blocked`, `Ledger blocked.missing` | the same blocked value and same ledger with its cursor |

For every cursor, `markerExact` proves that the retained marker is exactly the
ledger marker. The ledger's own `markerExact` in turn identifies that marker
with its dependent source (`firstMissing`, `secondMissing`, or `missing`). No
marker is converted to `Unit`, a proposition chosen later, or a Boolean.

## D4 head and exact D5--D7 tail

The reusable cursor proves all of the following, rather than relying on list
simplification at a later consumer:

- `ledger.slots = current :: remaining`;
- `current = d4`;
- `remaining = [d5, d6, d7]`; and
- the remaining list is noduplicated.

Together with node [182]'s `slotsExact`, this is precisely the decomposition
`[D4,D5,D6,D7] = D4 :: [D5,D6,D7]`. The output says that D4 is first; it says
nothing about whether D4 or any tail clause holds.

## Output size and local computation

The concrete Erdős theorem computes the size from the actual returned cursors,
not from an ambient upper-bound parameter. It is six remaining slots in the
two-ledger coarse output and three in the one-ledger bounded output, hence at
most six. The runner only inspects the already computed node-[182] constructor
and constructs one or two fixed cursors. It enumerates no vertices, paths,
contexts, colorings, graphs, finite types, response tables, or universes.

This bound is an output-tail size bound. It is not presented as evidence that
any clause predicate was evaluated.

## Framework ownership and transfer

`Graph.InducedPathComponentD4D7ClauseCursor` owns the reusable cursor,
dependent schedule consumer, totality theorem, and six-slot bound. The Erdős
file adds only its concrete transition-preserving output wrapper. The separate
`Examples.ComponentD4D7ClauseCursor` executes the graph runner on the existing
non-Erdős component source and verifies totality, the D4 head, exact D5--D7
tail, ledger decomposition, and the same local bound.

No truth semantics, compatible-response equivalence, smaller-object witness,
or CT8 removal/repetition certificate appears. Those remain downstream work.

## Validation and trust

The following focused builds pass:

```text
lake build StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseCursor \
  StructuralExhaustion.Examples.InducedPathComponentD4D7ClauseCursor
lake build Erdos64EG.P13SameWindowComponentD4D7ClauseCursor
```

The scoped forbidden-pattern audit finds no `sorry`, `admit`, `unsafe`, new
`axiom`, `Fintype`, `Finset.univ`, or `Set.univ`. Diff checks are clean.

`#print axioms` gives:

- `cursor`: `propext` only;
- graph runner, totality, and six-slot theorem: `propext`,
  `Classical.choice`, `Quot.sound`;
- Erdős runner, six-slot theorem, and verified-prefix theorem: the same three
  standard axioms.

There is no HSS dependency in node [185]. Shared integration files were not
edited.
