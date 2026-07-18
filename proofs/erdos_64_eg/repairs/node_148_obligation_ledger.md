# Original node [148] obligation ledger

Incoming edge: the literal no payload of node [146], carrying the unchanged
node-[145] sequential ledger and the proved inequality
`1/78 <= theta`.  Outgoing edges are exactly `[148] -> [149]` (yes) and
`[148] -> [150]` (no).

| Task | Original-paper obligation | Lean evidence | Status |
|---|---|---|---|
| XI-148-01 | Consume `theta >= 1/78` and the exact final hot aggregate on the same node-[21] context. | `P13Node146To148`; `P13Node148To149.previous`; `P13Node148To150.previous`; both payloads retain `p13SequentialFinalHotAggregate`. | proved |
| XI-148-02a | Express total, hot, cold, and corrected skeleton demands on the exact packing-order ledger. | `p13Node148TotalDemand`, `p13Node148HotDemand`, `p13Node148ColdDemand`, `p13Node148Allowance`. | proved |
| XI-148-02b | Prove the simultaneous recoverable hot product fits the corrected allowance. | `p13Node148_hotDemand_le_allowance`. | proved |
| XI-148-02c | Prove exact hot/cold demand partition and total payment. | `p13Node148_totalDemand_eq_hot_add_cold`, `p13Node148_totalDemand_le_allowance_add_cold`. | proved |
| XI-148-02d | Decide whether the corrected total cap closes. | `runP13Node148`. | proved |
| XI-148-03a | Route yes to node [149] with the corrected finite density handoff. | `P13Node148To149.correctedHandoff`. | proved |
| XI-148-03b | Route no to node [150] with the failed cap, exact hot payment, cold shortfall, and nonempty cold list. | `P13Node148To150`. | proved |
| XI-148-04 | Prove exhaustiveness, one local comparison, and a polynomial work certificate. | `runP13Node148_exhaustive`, `p13Node148LocalCheckCount_polynomial`, `p13Node148WorkBudget`. | proved |

All eight tasks are proved.  Node [148] does not prove node [149]'s
asymptotic density theorem or node [150]'s normalized linear cold-mass bound;
those are responsibilities of the two successor nodes.
