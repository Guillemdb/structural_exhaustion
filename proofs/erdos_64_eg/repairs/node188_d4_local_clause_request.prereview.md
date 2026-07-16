# Pre-review: node [188] local D4 clause request

## Verdict

**READY FOR INDEPENDENT REVIEW.**

Node [188] consumes node [185]'s exact D4 cursor residual and emits one typed
singleton request for each actual marker occurrence.  The request identifies
the focused slot as D4 and preserves the literal D5--D7 tail.  It deliberately
does not manufacture a truth value from the marker, which still carries no
clause predicate.  Genuine graph-derived D4 semantics and any CT8 route remain
the sole white successor [191].

## Exact predecessor and branch ledger

`D4LocalClauseRequestSource` stores a dependent node-[185] output and equality
with `runD4D7ClauseCursor` on the identical transition and full
node-174/175/180/182/185 source chain.  Its runner eliminates that stored
value:

| node-[185] branch | data retained exactly | node-[188] local move |
|---|---|---|
| coarse | block, both dependent ledgers, both exact cursors | one singleton D4 request for each cursor |
| bounded | block, dependent ledger, exact cursor | one singleton D4 request for that cursor |

No branch is merged, and the exhaustive theorem accounts for both outputs.

## Semantic scope

The reusable `Request focused` stores:

- the exact dependent marker from `focused`;
- `slots = [focused.current]` and `focused.current = D4`;
- the unchanged cursor tail; and
- `tail = [D5,D6,D7]`.

Thus node [188] inspects the actual local head slot and no other clause.  A
request is an obligation payload, not a Boolean result.  There is no
caller-supplied truth, response map, compatible context, response equality,
removal operation, smaller object, or CT8 certificate.

## Framework ownership and transfer

The reusable request, dependent cursor consumer, totality theorem, and work
bound live in `Graph.InducedPathComponentD4LocalClauseRequest`.  The Erdős
module is a thin exact-source wrapper.  The theorem-independent
`Examples.ComponentD4LocalClauseRequest` executes the same graph runner from
the existing non-Erdős component chain and checks exact D4 head, D5--D7 tail,
marker preservation, totality, and work.

## Locality and work

The runner pattern matches one already-computed node-[185] constructor and
constructs one or two singleton lists.  The concrete Erdős work theorem
measures the actual returned request lists: two slots in the coarse branch and
one in the bounded branch, hence at most two.  It enumerates no vertices,
paths, contexts, states, graphs, colorings, finite types, functions, response
tables, or universes.

## Trust and validation

Focused Graph, transfer, and Erdős builds pass.  The scoped forbidden scan
finds no `sorry`, `admit`, new axiom, `Fintype`, `Finset.univ`, or `Set.univ`.
`#print axioms` reports no axioms for the request constructor and only
`propext`, `Classical.choice`, and `Quot.sound` for the exported runners,
totality/work theorems, and verified prefix.  There is no HSS dependency.

```text
cd lean
lake build StructuralExhaustion.Graph.InducedPathComponentD4LocalClauseRequest \
  StructuralExhaustion.Examples.InducedPathComponentD4LocalClauseRequest

cd examples/erdos_64_eg
lake build Erdos64EG.P13SameWindowComponentD4LocalClauseRequest
lake env lean /tmp/ReviewNode188Axioms.lean
```

Shared umbrella imports, WebExport, topology, TeX, README, and implementation
log were not edited.
