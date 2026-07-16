# Pre-review: node [191] graph-owned D4 evaluator residual

## Verdict

**READY FOR INDEPENDENT REVIEW.** Node [191] consumes the exact node-[188]
requests.  Since those requests contain no predicate, it exposes the earliest
honest residual rather than inventing truth: every actual D4 request requires
a graph-local predicate and a proof of that predicate's provenance.  Node
[194] is the sole white semantic successor.

## Exact flow and scope

The Erdős source stores node [188]'s dependent output and equality with the
actual runner on the identical node-174/175/180/182/185/188 chain.  The coarse
branch preserves both blocks, ledgers, cursors, and requests and attaches two
residuals; the bounded branch preserves its corresponding exact data and
attaches one residual.  Exhaustiveness covers both constructors.

Each reusable residual retains the exact marker, singleton D4 slots, and
D5--D7 tail from its request.  Its duplicate-free requirement list is exactly

```text
[graphLocalPredicate, predicateProvenance].
```

There is no `Bool`, evaluator function, response map, compatible-context
family, response equality, removal, smaller object, or CT8 certificate.  The
requirements are obligations, not caller-supplied semantic inputs.

## Ownership, transfer, and locality

The residual contract, dependent runner, and work bound live in
`Graph.InducedPathComponentD4EvaluatorResidual`; the Erdős file is a thin
exact-source wrapper.  `Examples.ComponentD4EvaluatorResidual` executes the
same runner independently and checks the exact D4 slot, D5--D7 tail, two
requirements, totality, and bound.

No predicate can be evaluated at this node.  The runner inspects only the
already-computed node-[188] constructor and its actual singleton request
lists.  The concrete output contains four missing-input tags in the coarse
branch and two in the bounded branch.  It enumerates no vertices, paths,
contexts, responses, states, graphs, functions, colorings, or universes.

## Validation and trust

Focused Graph, transfer, and Erdős builds pass.  The forbidden scan finds no
`sorry`, `admit`, new axiom, `Fintype`, `Finset.univ`, or `Set.univ`.
`#print axioms` reports only the standard `propext`, `Classical.choice`, and
`Quot.sound` dependencies for runners and the verified prefix.  No HSS
dependency is introduced.

Shared umbrella imports, WebExport, topology, TeX, README, and implementation
log were not edited.
