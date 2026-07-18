# Node [147] obligation ledger

Specification: `original_erdos_64_proof.tex`, Part XI, node `[147]`, together
with the route-8 private-carrier reduction cited by the Part XI caption and
the cold-branch closure proof in
`proofs/erdos_64_eg/erdos_64_proof.tex`.

Node `[147]` remains yellow. Exactly **4 of 9** obligations are proved from
the current green node-`[146]` yes payload.

| Task ID | Original-paper obligation/property | Exact predecessor | Lean evidence | Status | Missing producer |
|---|---|---|---|---|---|
| XI-147-01 | Consume the literal yes edge `[146] -> [147]` on the same node-[145] ledger. | `P13Node146To147` | `P13Node147ArithmeticPrefix.previous` | proved | -- |
| XI-147-02 | Retain `tau(theta) < 3/13`. | `[146]` yes | `P13Node147ArithmeticPrefix.tau_lt` | proved | -- |
| XI-147-03 | Prove the strict coefficient collision `tau(theta) < 12(1/4-tau(theta))`. | XI-147-02 | `p13Route8CollisionCoefficientGap` | proved | -- |
| XI-147-04 | Record the equivalent positive margin `3-13 tau(theta)>0`. | XI-147-02 | `p13Route8CollisionMargin_pos` | proved | -- |
| XI-147-05 | Consume the existing Type-A route-8 collection carrying the large-budget deficit, with its exact basin count and same-context remainder. | Standing route-8 ledger carried into [145] | -- | missing | The current `P13Node146To147.previous` is only `P13SequentialWeightedLedger`; it contains no route-8 collection or basin data. |
| XI-147-06 | Under no two-carrier entry, select three private essential carriers per indexed basin and prove their cross-entry disjointness and boundary-incidence injection. | XI-147-05 and original carrier-core ledger | -- | missing | Exact nodes [114], [117], and [119] carrier producer. |
| XI-147-07 | Derive `3 N_basin <= def+(R) <= tau(theta)|R|+o(|R|)` on the same remainder. | XI-147-05/06 and boundary-supply ledger | -- | missing | Same-context private-carrier upper-budget producer, including finite/asymptotic error control. |
| XI-147-08 | Derive `3 N_basin >= 12(1/4-tau(theta))|R|-o(|R|)` from the route-8 burden and large-budget deficit. | XI-147-05 | -- | missing | Same-context route-8 burden and deficit lower-budget producer. |
| XI-147-09 | Absorb the two `o(|R|)` errors using the positive margin and conclude that the route-8 branch is impossible. | XI-147-03/04/07/08 | -- | missing | XI-147-07 and XI-147-08, plus their common eventual-error scale. |

The dependency-ready arithmetic performs zero new local scans; its work bound
is `p13Node147ArithmeticCheckCount_polynomial`. No ambient graph, state,
context, or universe family is enumerated.
