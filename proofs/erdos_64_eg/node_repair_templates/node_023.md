# Node [23] repair template

| Field | Value |
|---|---|
| Incoming | [22] yes -> [23] |
| Outgoing | branch terminal |
| Responsibility | Prove the paper's P13 window entropy overflow on the high-density branch. |
| Retained facts | Literal node22 high branch, label count, and node21 constants. |
| New output | Exact strict window-overflow inequality on node [22]'s literal yes constructor. |
| CT chain | Framework `continueDependentDecisionOnNoYes` branch continuation. |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N23-PRED | Consume the literal node-[22] yes leaf while retaining the node-[20] bypass and node-[22] no leaf | [22] | `Node23Stage`; `node23P13WindowEntropyOverflow` through `State.StageNode.continueDependentDecisionOnNoYes` | kernel-checked, conditional |
| N23-OVERFLOW | Expose the exact cross-multiplied strict inequality `1500000000 * n < 118108581006 * p13` carried by the yes leaf | [22] yes | `node23StrictWindowOverflow` | kernel-checked, conditional |
| N23-OUTPUT | Attach the strict overflow as node [23]'s exact branch payload without assuming that the branch is empty | [22] yes | `Node23Output.strictWindowOverflow`; `node23P13WindowEntropyOverflow` | kernel-checked, conditional only on node [21] |

Forbidden: cold-branch closure or downstream node24 obligations.

Node [23] remains yellow only because node [21] is still a typed predecessor.
Its own focused kernel check passes with no `sorryAx`.  It assumes no
quiet-block closure and does not infer a contradiction from the scalar
inequality alone; node [24]'s complementary edge is retained by Core.
