# Independent cross-review: node [188] local D4 clause request

## Verdict

**PASS.** No theorem-bearing repair was required. Node [188] consumes the
exact node-[185] output, emits exactly one singleton D4 request per actual
cursor occurrence, and preserves the unevaluated D5--D7 tail. A request is not
a clause value or response certificate.

## Exact node-[185] provenance

`D4LocalClauseRequestSource` stores the dependent
`D4D7ClauseCursorOutput source174` and an equality with
`runD4D7ClauseCursor` on the identical transition and full
node-174/175/180/182/185 source chain. `runD4LocalClauseRequest` eliminates the
stored `source188.node185` value itself, and
`d4LocalClauseRequest_exact_node185` exposes that exact source equality.

The official computed source uses the actual node-[185] runner definitionally.
There is no constructor accepting an unrelated cursor output as the canonical
predecessor.

## Multiplicity and dependent-data ledger

| node-[185] branch | exact retained payload | requests |
|---|---|---|
| coarse | blocked value, `Ledger blocked.firstMissing`, `Ledger blocked.secondMissing`, and their two exact cursors | one request indexed by the first cursor and one indexed by the second cursor |
| bounded | blocked value, `Ledger blocked.missing`, and its exact cursor | one request indexed by that cursor |

The output constructors preserve all these values rather than reconstructing
or erasing them. Each `Request focused` stores a marker with
`marker = focused.marker`; the cursor retains equality with its ledger marker,
and the ledger retains equality with its dependent missing-marker source.
Thus the first, second, and bounded marker occurrences cannot be exchanged.

## Literal D4-only focus

For each actual cursor, the request proves:

- `slots = [focused.current]`;
- `focused.current = D4`;
- `tail = focused.remaining`; and
- `tail = [D5,D6,D7]`.

Consequently the requested schedule is the singleton `[D4]`, while the exact
D5--D7 tail is copied but not requested or evaluated. The request structure
has no Boolean field, evaluator, compatible context, response map, response
equality, removal operation, smaller-object witness, or CT8 certificate.

## Local work

The concrete Erdős bound is computed from the request lists in the returned
output. Their total length is two in the coarse branch and one in the bounded
branch, hence at most two. The runner performs one constructor match and
constructs one or two singleton lists. It enumerates no vertices, paths,
contexts, states, colorings, graphs, functions, response tables, finite types,
or ambient universes.

The bound measures literal emitted request slots; it is not evidence that D4
was evaluated.

## Framework ownership and non-Erdős transfer

The reusable request, dependent cursor consumer, totality theorem, and local
two-slot bound live in
`Graph.InducedPathComponentD4LocalClauseRequest`. The Erdős file is a thin
dependent wrapper over the concrete transition.

`Examples.ComponentD4LocalClauseRequest` executes the graph runner on the
existing independent component source. It checks totality, the singleton D4
head, exact D5--D7 tail, dependent marker preservation, and the same local
bound.

## Validation and trust

Focused builds pass:

```text
lake build StructuralExhaustion.Graph.InducedPathComponentD4LocalClauseRequest \
  StructuralExhaustion.Examples.InducedPathComponentD4LocalClauseRequest
lake build Erdos64EG.P13SameWindowComponentD4LocalClauseRequest
```

The scoped scan finds no `sorry`, `admit`, `unsafe`, new `axiom`, `Bool` term,
`Fintype`, `Finset.univ`, or `Set.univ`; the only Boolean/response/CT8 mentions
are explicit negative scope comments. Diff checks are clean.

`#print axioms` reports no axioms for `request`. The graph and Erdős runners,
totality/local-bound theorems, and official prefix use only `propext`,
`Classical.choice`, and `Quot.sound`. There is no HSS dependency.

Shared umbrella imports, WebExport, topology, TeX, README, and implementation
log were not edited.
