# Pre-review: node [185] D4--D7 first-obligation cursor

## Verdict

**READY FOR INDEPENDENT REVIEW.**

Node [185] consumes the exact node-[182] output and performs only a
structural refinement of each fixed obligation ledger.  It focuses D4 as the
next obligation and retains D5--D7 as the exact unevaluated tail.  It does not
interpret the predecessor marker as clause truth and does not claim response
equivalence, compatible-context transport, removal, or CT8 repetition.

## Exact provenance and branch coverage

`D4D7ClauseCursorSource` stores the actual node-[182] output together with an
equality to `runD4D7ClauseSchedule` on the same transition and node-180/182
source chain.  Its runner eliminates exactly that value:

- the coarse constructor preserves both dependent ledgers and creates one
  cursor for each exact `firstMissing` and `secondMissing` occurrence;
- the bounded constructor preserves its dependent ledger and creates one
  cursor for the exact `missing` occurrence.

The exhaustive theorem accounts for both constructors.  No branch is erased
or merged.

## Honest semantic boundary

The reusable `Cursor ledger` proves only the literal list decomposition

```text
[D4, D5, D6, D7] = D4 :: [D5, D6, D7].
```

The field `current = D4` means that D4 is the first scheduled obligation; it
does not give D4 a Boolean value.  The dependent marker remains the exact
marker stored in its ledger.  Actual finite local-response semantics and
pair-compatible context transport remain reserved for successor node [188].

## Framework ownership and transfer

The reusable cursor, dependent schedule consumer, totality theorem, and work
bound live in
`Graph.InducedPathComponentD4D7ClauseCursor`.  The Erdős module is a thin
instantiation carrying the concrete transition payload.  The independent
`Examples.ComponentD4D7ClauseCursor` executes the same graph runner from the
existing non-Erdős schedule and checks the focused slot, exact tail,
decomposition, totality, and local work bound.

## Local computation and work

The runner pattern matches one already computed node-[182] constructor and
constructs constant-size cursors.  It evaluates no clause predicate and
enumerates no vertices, paths, contexts, colorings, graphs, finite types, or
ambient universes.  The concrete Erdős work theorem measures the returned
cursor tails: six slots in the two-ledger coarse branch and three in the
one-ledger bounded branch.

## Trust and validation

Focused Graph, transfer, and Erdős builds pass.  A forbidden-pattern scan
finds no `sorry`, `admit`, new axiom, `Fintype`, `Finset.univ`, or `Set.univ`.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`
for the exported runners, totality/work theorems, and verified-prefix theorem;
the cursor constructor itself uses only `propext`.  There is no HSS
dependency.

```text
cd lean
lake build StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseCursor \
  StructuralExhaustion.Examples.InducedPathComponentD4D7ClauseCursor

cd examples/erdos_64_eg
lake build Erdos64EG.P13SameWindowComponentD4D7ClauseCursor
lake env lean /tmp/ReviewNode185Axioms.lean
```

Shared integration files were not edited.
