# Original node [89] obligation ledger

Node [89] tests the canonical receiver loads on the exact Type-A support.  Its
only outgoing edges are no to [90] and yes to [93].  The exit-(4) loop returns
to the same test only after node [102] has produced a smaller residual load;
that later iteration is not an extra node-[89] outcome.

| Task | Original-paper obligation | Lean evidence | Status |
|---|---|---|---|
| VIII-89-01 | Consume the exact Type-A support and its canonical receiver traces. | `TypeANode89SaturationDecision.input`, indexed through the supplied `VerifiedNode88Residual`. | proved |
| VIII-89-02 | Define `q(w)=3-d_X(w)` and `L(w)` as the fibre of cubic vertices whose canonical trace terminates at `w`. | `input.degree`; `routing`; `routedReceiver_eq_canonical`; `FiniteReceiverDischarge.Routing.load`. | proved |
| VIII-89-03 | Decide whether some receiver satisfies `L(w)>=4q(w)`. | `run`; the saturated witness exports `threshold_le_load`. | proved |
| VIII-89-04 | On no, prove every receiver satisfies `L(w)<=4q(w)-1` and route that exact residual to [90]. | `ToNode90.unsaturated`, `load_le_capacity`. | proved |
| VIII-89-05 | On yes, retain one actual saturated receiver and route the identical support to [93]. | `ToNode93`, including receiver membership, degree, and threshold proof. | proved |
| VIII-89-06 | Preserve exact predecessor identity and prove the two routes exhaustive. | `exactPrevious` in both payloads; `run_exhaustive`. | proved |
| VIII-89-07 | Inspect only actual support vertices and receiver fibres with polynomial work. | `localCheckCount_polynomial`, `workBudget`. | proved |
| VIII-89-08 | Consume a typed immediate node-[88] residual carrying the raw H0/H1/H2 threshold audit on this identical support. | Every node-[89] definition is indexed by `TypeANodes86To88Thresholds.VerifiedNode88Residual`; both outgoing payloads retain it as `previous` with `exactPrevious`. | proved |

Eight of eight node-[89] obligations are proved.  The cell is fully
implemented; execution of this branch remains upstream-blocked at node [87].
No later exit or route-8 conclusion is assumed here.
