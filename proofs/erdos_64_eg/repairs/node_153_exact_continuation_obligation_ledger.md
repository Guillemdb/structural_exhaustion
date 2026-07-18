# Node [153] exact F2--F5 continuation obligation ledger

Authority: `original_erdos_64_proof.tex`, node [153] and
`def:cold-corridor-first-failure`.  This ledger records the delta supplied by
`P13WeightedColdRestrictedExactContinuation.lean`; it adds no diagram node,
edge, or outcome.

| Obligation | Exact input | Lean evidence | Status |
|---|---|---|---|
| At a stored stage, F2 retains a literal earlier prefix with the same complete structural state and one proof-selected distinguishing outside context. | node-[152] prefix package plus `LocalCorridorSurvivor` | `StageF2`, `F2At`, `f2Data` | proved |
| F2 does not enumerate the outside-context universe. | same | `F2Distinction` stores one context selected by `classifyF2`; `F2At` performs no context-list scan | proved |
| F3 is available only with universal exact response and an actual proper representative carrying the replacement obligations. | F2-negative semantic pair | `StageF3`, `ProperRepresentativeProposal`, `F3At` | proved |
| F4 retains the identical event and first-hit key from the already-produced ordinary/decorated/route-8 ledger. | exact `PriorD6Ledger` | `F4At`, `D6F4Hit`, `f4Data` | proved |
| On the locally surviving edge, the completed D6 scan excludes F4 at every literal stage. | `LocalCorridorSurvivor` | `f4_absent` | proved |
| A repeated structural state with a distinguishing context is the F2 event at the exact later occurrence. | actual Core repetition | `repeatedStageF2` | proved |
| A repeated structural state with universal response and a proper representative is the F3 event at the exact later occurrence. | actual Core repetition | `repeatedStageF3` | proved |
| After exhaustive stage-wise F1--F4 negatives, run the actual structural corridor and return only the original F5 terminal or repeated support. | exact literal stage schedule | `exactF5OfClear`, `ExactF5` | proved |
| In the repeated case, F2 distinction contradicts the retained same-stage F2 negative; universal response with a proper representative contradicts the retained same-stage F3 negative. | same | internal branches of `exactF5OfClear` | proved |
| Compose F1, F2, F3, F4, and F5 in the original stage-major order. | `LocalCorridorSurvivor` | `exactLaterSemantics`, `runExactContinuation`, `runExactContinuation_total` | proved locally |
| Account for the visible stage scan without an ambient graph scan. | literal stored stages | `exactContinuation_checks` | proved |

Delta: **11/11 local continuation obligations proved**.  In the global
Part-XI ledger this strengthens XI-153-04 and XI-153-06--11, but node [153]
remains yellow for two predecessor/consumer obligations that this local
composition must not assume:

1. the branch-total produced-support ledger must prove that every earlier
   ordinary Type-B, decorated Type-B, and route-8 event is present before the
   `LocalCorridorSurvivor` enters node [153];
2. terminal or repeated `ExactF5` must be converted by the graph-owned
   producer into the manuscript's full `ColdBoundedGerm` (XI-153-12), including
   its two representatives and finite response-reflection/coverage data.

The build target
`Erdos64EG.P13WeightedColdRestrictedExactContinuationTests` passes.  Its axiom
audit reports only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`.
