# Node [20] repair template

| Field | Value |
|---|---|
| Incoming edges | [19] yes -> [20] |
| Outgoing edges | expansion entry [125] only; the remaining edges belong to [125]--[144] |
| Local responsibility | Name the strict constructor of node [19] as the non-near-cubic accounting branch. Node [20] is expanded, rather than proved, by Part X. |
| Retained branch facts | Literal `Node18Stage`, the complete accumulated ledger, and the exact strict inequality produced by `Node19Stage` |
| New output | None: [20] is the existing yes constructor, not a second mathematical producer |
| CT chain | No new CT; framework-owned dependent decision at [19], followed later by its yes-branch continuation to [125] |
| Immediate consumers | [125] |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N20-PRED | Identify [20] with the literal strict constructor of `Node19Stage` | [19] | `Node20SourceStage`, `Node20Entry` | [19] yes -> [20] | proved; kernel checked |
| N20-STRICT | Retain the exact strict squared-surplus inequality without copying it into an application residual | [19] | `node20Entry_iff_node19High` | [20] -> [125] | proved; kernel checked |
| N20-SCOPE | Defer all surplus-pair construction and accounting to the displayed Part-X nodes | paper topology | no CT or accounting declaration occurs in `Node20SurplusPairAccountingBranch.lean` | [20] -> [125] | proved by source scope and kernel-checked endpoint |
| N20-WORK | Add no work beyond node [19]'s symbolic comparison | framework/[20] | `node20LocalChecks_eq_zero` | [20] -> [125] | proved; kernel checked |

Forbidden: `ExactHandoff`, custom route, a duplicate branch payload, executing
nodes [125]--[144] at node [20], or closing/touching node [19]'s low branch.
