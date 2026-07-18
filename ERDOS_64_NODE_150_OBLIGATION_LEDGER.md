# Node [150] obligation ledger

Specification: Part XI node `[150]`, `lem:hot-failure-cold-mass`, and
`def:surviving-cold-branch` in the original manuscript. Node `[150]` remains
yellow. Exactly **8 of 9** obligations are proved.

| Task ID | Original-paper obligation/property | Exact predecessor | Lean evidence | Status | Missing producer |
|---|---|---|---|---|---|
| XI-150-01 | Consume the literal no edge `[148] -> [150]`, retaining the same `[146]` no payload and node-[145] ledger. | `P13Node148To150` | `P13Node150FiniteColdMass.previous`, `previousExact` | proved | -- |
| XI-150-02 | Define `C` as the exact cold count of the node-[145] sequential ledger. | XI-150-01 | `p13Node150ColdCount`, `coldCountExact` | proved | -- |
| XI-150-03 | Retain failed hot comparison, exact hot payment/cold shortfall, and prove `C>0`. | XI-150-01 | predecessor fields, `P13Node150FiniteColdMass.coldNonempty` | proved | -- |
| XI-150-04 | Prove the exact finite normalization of `C >= (theta-theta_win)n-o(n)` with the correction explicit. | XI-150-01/02 | `p13Node150_route8ColdMassCrossMultiplied` | proved | -- |
| XI-150-05 | Prove the correction becomes `o(n)` after dividing by the positive fixed rate and `log n`. | XI-150-04 | `p13ManuscriptDyadicHotNormalizationError_real_upper`, `p13ManuscriptDyadicHotNormalizationRealEnvelope_isLittleO`, `p13ManuscriptDyadicHotNormalization_div_nlog_tendsto_zero`, `normalizationVanishing` | proved | -- |
| XI-150-06 | Evaluate the route-8 threshold coefficient exactly. | XI-150-04 and `theta>=1/78` | `p13ManuscriptRoute8ColdMassNumerator_exact`, `p13Node150_manuscriptRoute8ColdMassCrossMultiplied`, `manuscriptRoute8Lower` | proved | -- |
| XI-150-07 | Evaluate the negative-net threshold coefficient when `theta>=1/73`. | XI-150-04 plus the named threshold condition | `p13ManuscriptNegativeNetColdMassNumerator_exact`, `p13Node150_manuscriptNegativeNetColdMassCrossMultiplied` | proved | -- |
| XI-150-08 | Certify the two printed decimal lower coefficients. | XI-150-06/07 | `p13ExactManuscriptHotRateCertificate` certifies the fixed decimal; `p13ExactManuscriptDyadicRateCertificate` retains its strict dyadic slack; `p13SequentialHot_manuscriptDyadic_normalized_with_error`, `p13ManuscriptRoute8ColdMassCoefficient_printedBracket`, and `p13ManuscriptNegativeNetColdMassCoefficient_printedBracket` prove the two displayed lower endpoints. | proved | -- |
| XI-150-09 | Retain every surviving-cold-branch exclusion and the exact near-cubic spine payload for node [151]. | `[144]`, `[148]` no, standing ledgers | `P13NearCubicSpineBound`, `P13Node144NearCubicHandoff`, and `P13Node151AmbientCubicColdHandoff` now specify and consume the exact spine/cold fields. | partial | The exact `[150] -> [151]` cold/spine connector is proved on the current bounded-spine input, but node `[144]` still lacks the semantic sparse-exit/Type-B/fixed-cap producer and no branch-total exclusion ledger carries all clauses (i)--(v) of `def:surviving-cold-branch`. |

The implemented arithmetic performs zero new local scans and enumerates no
ambient graph, context, state family, or Boolean universe.  Its only finite
certificate is the fixed 42-row repeated-squaring ledger already prescribed
by the manuscript rate calculation.
