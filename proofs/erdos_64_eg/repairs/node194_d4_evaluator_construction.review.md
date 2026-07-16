# Independent cross-review: node [194] D4 evaluator construction residual

## Verdict

**PASS.** No code repair was required. Node [194] consumes the exact node-[191]
residual output and adds only three ordered graph-owned construction
obligations per residual occurrence. It constructs no evaluator or semantics.

## Exact node-[191] chain

`D4EvaluatorConstructionSource` stores the dependent node-[191] output and an
equality with `runD4EvaluatorResidual` on the identical transition and full
node-174/175/180/182/185/188/191 source chain. The node-[194] runner eliminates
that stored value itself, while `exact_node191` exports the equality. The
computed source is definitionally the actual node-[191] runner.

The coarse output retains its block, two ledgers, two cursors, two requests,
and two node-[191] residuals. The bounded output retains its block, ledger,
cursor, request, and residual. No dependent occurrence is merged or erased.

## Exact predecessor preservation

Every `ConstructionResidual pending` stores
`predecessor : D4EvaluatorResidual.Residual request` together with
`predecessor = pending`. Consequently the exact node-[191] marker, singleton
D4 request, D5--D7 tail, and evaluator requirement pair remain available
transitively. Node [194] neither reconstructs nor substitutes those fields.

## Three graph-owned construction requirements

The additional list is exactly, in order,

```text
[componentLocalData, graphOwnedPredicateDefinition, predicateDerivation].
```

It is proved duplicate-free and has length three. These tags require a future
consumer to provide actual component-local input, define its predicate from
the graph, and prove that derivation. They are obligation names only: the
structure contains no local-data object, predicate function, proof of a
predicate, evaluator, or truth value.

## Multiplicity and local bound

There are two construction residuals in the coarse branch, hence six returned
tags, and one in the bounded branch, hence three. The concrete Erdős
`requiredInputs` reads the actual returned lists and proves a uniform bound of
six.

The runner performs one constructor inspection and copies one or two fixed
three-tag lists. It enumerates no graph, vertex, path, context, state,
function, response table, coloring, finite type, or ambient universe. The
bound measures missing-input tags, not semantic evaluation work.

## Framework ownership and transfer

The reusable construction residual and exact three-tag list live in
`Graph.InducedPathComponentD4EvaluatorConstructionResidual`. The Erdős module
only preserves the concrete dependent branches. The independent example
builds the complete marker → ledger → cursor → request → evaluator residual →
construction residual chain and checks exact predecessor equality and the
three tags.

## Validation and trust

Focused Graph/example and Erdős builds pass. The scoped scan finds no `sorry`,
`admit`, `unsafe`, new axiom, executable `Bool`, `Fintype`, `Finset.univ`, or
`Set.univ`; Boolean/evaluator mentions are negative scope comments or local
example names. Diff checks are clean.

`#print axioms` reports no axioms for the reusable residual or nodup theorem.
The Erdős runner, six-tag bound, and verified-prefix theorem use only
`propext`, `Classical.choice`, and `Quot.sound`. There is no HSS dependency.

Node [196] was not expanded. Shared integration, WebExport, topology, TeX,
README, and implementation-log files were not edited.
