# Node [19] repair template

| Field | Value |
|---|---|
| Incoming | [18] -> [19] |
| Outgoing | yes -> [20]; no -> [21] |
| Responsibility | Decide whether sigma(G) exceeds C_sp sqrt(n). |
| Retained facts | Packed minimal context and node18 algebra. |
| New output | Exact framework yes/no surplus-scale decision. |
| CT chain | Framework order-threshold split. |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N19-PRED | Consume literal Node18Stage | [18] | `node19SurplusScaleDecision`; `Node18StageContext` | proved; kernel checked |
| N19-VALUES | Retrieve sigma,n,C_sp from the immediate live context/local definition | earlier/[19] | `node19Profile`, `node19SurplusCoefficient` | proved; kernel checked |
| N19-DECIDE | Exhaustive strict-high/at-most threshold decision | [19] | `Node19Stage`, `node19_exhaustive` through `executeStrictUsingStage` | proved; kernel checked |
| N19-WORK | Retain zero/local work | framework | `node19WorkBudget`, `node19_work_zero` | proved; kernel checked |

Forbidden: application route/state machine or branch reconstruction.
