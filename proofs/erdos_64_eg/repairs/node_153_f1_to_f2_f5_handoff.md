# Node [153]: exact F1-to-F2--F5 handoff ledger

Status: stage-major continuation contract.  It does not claim the graph-owned
F2, F3, F4, or F5 semantic producer, so node [153] is not green.

## Residual-flow ledger

| Incoming branch path | Exact accumulated residual | Local data inspected | Negated earlier exits retained | Node move | Outgoing branch | Consumer |
|---|---|---|---|---|---|---|
| [152] weighted-cold selected stub -> C153.1a outside endpoint -> C153.1b restricted component -> C153.2 prefix package | identical node-[152] entry and source token; weighted-cold deletion family; anchor boundary stub; cyclic successor; canonical restricted-component BFS path; ordered prefix stages | at the current prefix, the literal `Fin 13` anchor-window offsets, in canonical order; each test uses only prefix length, actual endpoint adjacency, and exact dyadic length | all earlier prefix stages have no F1--F4 event; within the current stage, every offset before the selected offset is non-F1 | run `FiniteFirstFailure` in stage order; at each stage test F1, then F2, F3, F4 | F1: canonical first offset and a literal `CycleWithLength ... PowerOfTwoLength` | target terminal for this local source |
| same path and residual | same package and schedules | graph-owned F2 response distinction at this same stage | all earlier stages clear and F1 false at this stage | same runner | F2 payload | sparse-exit / exit-(4) route |
| same path and residual | same package and schedules | graph-owned F3 exact response equality and proper representative at this same stage | all earlier stages clear; F1 and F2 false at this stage | same runner | F3 payload | CT3/replacement route |
| same path and residual | same package and schedules | exact existing Type-B / route-8 membership key at this same stage | all earlier stages clear; F1--F3 false at this stage | same runner | F4 payload | named existing ledger |
| same path and residual | same package and schedules | terminal successor or repeated exact cut-state exchange | every stage is exhaustively negative for F1--F4 | runner reaches its no-event constructor | F5 germ constructed only from exhaustive negatives | node [154] G1--G3 input producer |

The order is nested, not a global Cartesian prepass.  A later-stage F1 cannot
outrank an earlier-stage F2.  At one stage, `F1Stage` is the existence of a
literal completion among `Fin 13`; `firstOffsetHit` retains the canonical
first offset and its no-earlier-offset proof.  The outer
`FiniteFirstFailure.Profile` then enforces F1 < F2 < F3 < F4 before advancing
to the next stored prefix.  Its F5 constructor is called only from the
exhaustive no-event branch.

## Exact executable boundary

The implemented profile exposes:

```text
outer order   : package.stages.values
inner order   : List.finRange 13
F1Stage       : exists offset, package.F1At (stage, offset)
F1 data       : exact stage, canonical first-offset hit, literal dyadic cycle
later contract: local F2/F3/F4 predicates, deciders, typed payload builders
F5 builder    : consumes exhaustive negative evidence on the full stage list
```

Thus a missing endpoint-to-window attachment edge makes that offset non-F1; it
is not converted into a cycle or discarded.  The older stage-product `f1Scan`
is retained only as an auxiliary audit and is not used by the production
continuation profile.

## Contract required from the next producer

The profile becomes an actual node-[153] execution only after a graph/route-
owned **exact two-boundary semantic producer** constructs
`RequiredF2F5Semantics`, supplying for each stored prefix stage:

1. the literal two-boundary piece and its displayed boundary data;
2. a proof-selected compatible outside context witnessing F2, when one
   exists, together with compatibility and the exact response discrepancy;
3. otherwise, the universal compatible-context response equality and the
   proper smaller representative required to build the CT3/replacement input
   for F3;
4. exact membership keys for the already existing Type-B and route-8 ledgers
   for F4; and
5. after all earlier predicates are false, the terminal/repeated exact
   cut-state exchange and bounded support required for F5.

This producer must inspect stored local pieces and proof-selected contexts. It
must not enumerate an ambient context universe.  `RequiredF2F5Semantics` is an
explicit missing-producer contract; quantifying over it demonstrates that the
generic priority runner is ready, but is not an unconditional Erdős theorem
and does not make node [153] green.

## Local work

At each prefix the F1 scan performs at most thirteen literal offset tests,
followed by one top-level call to each of F2, F3 and F4.  Hence the visible
top-level call bound is `16 * numberOfStages`.  The missing semantic producer
must separately bound the internal cost of its F2--F4 predicates.  No graph,
path, completion, or context family is enumerated.
