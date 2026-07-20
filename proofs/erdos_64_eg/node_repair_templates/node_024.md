# Node [24] repair template

| Field | Value |
|---|---|
| Incoming | [22] no -> [24], while node [23]'s sibling yes output is retained |
| Outgoing | [24] -> [25] |
| Responsibility | Record the exact complementary window-density cap and the paper's conditional sharper high-entropy arithmetic implication. |
| Retained facts | Literal node-[22] low proof, node-[17] maximal packing support bound, node-[21] typed payload. |
| New output | `windowDensity`, `packingSupport`, and `highEntropy : joint budget -> sharper cap`. |
| CT chain | Framework no-after-yes continuation preserving both node-[22] successors. |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N24-PRED | Consume only the literal node-[22] no leaf while retaining node [23]'s yes payload | [22]/[23] | `Node24Stage`; `node24P13DensityBounds` | kernel-checked, conditional |
| N24-WINDOW | Retain the exact cross-multiplied complementary window cap | [22] no | `Node24Output.windowDensity := low` | kernel-checked, conditional |
| N24-SUPPORT | Retain the exact support bound for the selected maximal packing | [17]/[24] | `Graph.InducedPathMaximalPacking.packing_vertices_bound`; `Node24Output.packingSupport` | kernel-checked, conditional |
| N24-HIGH | From `Node24HighEntropyJointBudget`, derive exactly `Node24HighEntropyCap` | [24] | `node24HighEntropyCap_of_jointBudget`; `Node24Output.highEntropy` | kernel-checked, conditional |
| N24-LEDGER | Register the residual-wide high-entropy transformer once for later ledger queries. | [24] | `Node24HighEntropyTransformer`; `node24StageEntailsHighEntropyTransformer` | kernel-checked, conditional |
| N24-WORK | Perform only symbolic arithmetic and use the stored packing theorem | framework/[24] | `node24LocalChecks_eq_zero` | kernel-checked, conditional |

Forbidden: asserting the high-entropy premise, closing node [52], adding a new
dichotomy, or assigning remainder construction and asymptotic transport to
node [24]. The focused kernel check passes with no `sorryAx`; node [24]
remains yellow only until the typed node-[21] producer is replaced.
