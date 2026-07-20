# Node [22] repair template

| Field | Value |
|---|---|
| Incoming | [21] -> [22] |
| Outgoing | yes -> [23]; no -> [24] |
| Responsibility | Decide whether P13 packing density exceeds the paper threshold. |
| Retained facts | Exact node21 constants/budget and packing ledger. |
| New output | Exact framework density decision only. |
| CT chain | Framework threshold/finite-count decision. |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N22-PRED | Consume literal Node21Stage | [21] | `runInitialThroughNode21`; `node22P13DensityDecision`; `runInitialThroughNode22` | complete; framework ledger |
| N22-DENSITY | State exact paper inequality | [22] | `node22DensityFamily`; `Node22High`; `Node22Low` | complete |
| N22-DECIDE | Exhaustive yes/no framework decision; neither branch is caller-supplied | [22] | `Core.OrderThresholdSplit.DependentNoContinuationProfileFamily.executeStrictUsingNoContinuation`; `node22DensityDecision_exhaustive`; `Node22Stage` | complete |
| N22-WORK | Retain local symbolic work bound | framework | `DependentNoContinuationProfileFamily.workBudget`; `node22LocalChecks_eq_zero` | complete |

Forbidden: Boolean-realization assumption, custom residual branch, or node23/24 conclusion.

Node [22] has no application-owned input or handoff. Its canonical runner
executes node [21], retrieves the literal `Node21Stage` from the accumulated
framework ledger, and applies the exhaustive framework decision. The root
axiom report inherits node [21]'s documented native finite-audit boundary and
the HSS theorem, but node [22] introduces no additional axiom.
