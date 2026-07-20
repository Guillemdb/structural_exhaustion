# Node [28] repair template

| Field | Value |
|---|---|
| Incoming | [27] -> [28] |
| Outgoing | [28] -> [29] |
| Responsibility | Define the positive deficiency of the retained remainder and attach its exact degree-sum identity. |
| Retained facts | Inherited through the accumulated ledger: the literal node27 stage and unchanged Residual A graph. |
| New output | The paper's positive-deficiency quantity and exact local identity. |
| CT chain | Framework finite-sum/localization successor (CT11 arithmetic layer). |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N28-PRED | Consume literal Node27Stage | [27] | `node28P13PositiveDeficiency` | kernel-checked, conditional |
| N28-DEF | Define `def⁺(R)=sum_v max(0,3-d_R(v))` on the retained carrier | [28] | framework graph profile `p13RemainderDeficiencyProfile` | kernel-checked, conditional |
| N28-IDENTITY | Prove the exact degree-sum/deficiency formula used downstream | [28] | `Node28Output.exactFormula` | kernel-checked, conditional |
| N28-LEDGER | Append the formula once | framework | generic active-cursor map | kernel-checked, conditional |

Forbidden: external-incidence estimates (node29), a copied graph carrier, or a global graph-family scan.

Node [28] is kernel-checked but remains conditional/yellow solely because its
incoming ledger depends on the accumulated node-[21] framework ledger and
`Node23DenseWindowQuietBlockInput`. Its exact deficiency identity is its only
local output; inherited graph data are not copied into that output. The
node-local producer showed no `sorryAx`.
