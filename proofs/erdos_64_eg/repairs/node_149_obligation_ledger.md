# Original node [149] obligation ledger

Incoming edge: the exact yes payload of node [148], itself indexed by the
particular no payload of node [146].  Node [149] is terminal in the original
diagram and introduces no new case.

| Task | Original-paper obligation | Lean evidence | Status |
|---|---|---|---|
| XI-149-01 | Consume the particular node-[148]-yes payload and retain the complete dependent predecessor chain. | `VerifiedP13Node149DensityCap.previous`, `exactPrevious`; the type is indexed by `node146No` and `node148Yes`. | proved |
| XI-149-02 | Retain the corrected finite density cap selected by node [148]. | `densityCap`, `densityCapExact`, `correctedHandoff`, `correctedHandoffExact`. | proved |
| XI-149-03 | Export the exact cross-multiplied `theta <= theta_win + error` inequality without dropping scale or skeleton error. | `VerifiedP13Node149DensityCap.correctedThetaCap`. | proved |
| XI-149-04 | Verify the printed coefficient `theta_win = 0.01270017798...` and retain the corrected remainder consequence. | `p13Node149ThetaWindow_eq_exact`, `p13WindowThetaExact_decimalBracket`, and `VerifiedP13Node149DensityCap.correctedRemainderCap`. | proved |
| XI-149-05 | Prove uniformly that the complete normalization error is `o(n log n)` and conclude the original asymptotic `theta <= theta_win + o(1)`. | `p13SequentialHotNormalizationError_real_upper`, `p13SequentialHotNormalizationRealEnvelope_isLittleO`, `p13Node149ThetaError_tendsto_zero`, and `VerifiedP13Node149DensityCap.theta_le_thetaWindow_add_oOne`. | proved |
| XI-149-06 | Perform no new search and expose a polynomial local work bound. | `VerifiedP13Node149DensityCap.localCheckCount_polynomial` (zero checks). | proved |

All six obligations are proved.  The terminal node is green: its exact
predecessor-indexed finite cap is divided by the positive finite binary-log
budget, and the resulting graph-order-only additive error tends to zero.
