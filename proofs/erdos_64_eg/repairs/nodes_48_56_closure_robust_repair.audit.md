# Red-team audit: closure-robust Part IV repair

## Baseline

- Repair sketch: `nodes_48_56_closure_robust_repair.tex`
- Original manuscript baseline: SHA-256 `6cea87715450176e2b3e611a347c7147764730866c7174122e5be0445235c671`
- Failed block: nodes 48--54, specifically full target-relative rank being used as simultaneous Boolean realization and then as additive entropy.
- Methodology consulted: branch states and residuals; C1--C5; admission; bookkeeping-vs-theorem; both-sides test; invariant ordering and granularity; budgets; selection policy; typed handoffs; level-2/level-3 repair; defect register and taxonomy; EG CT3/CT15 rows.
- Current verdict: **FAIL**. The sketch is mathematically honest and the downstream composition compiles, but the genuine fixed cold-skeleton/F2--F5 producer of node 24 is not proved. A FAIL verdict blocks source merger and green status.

## Provenance matrix

| Used fact | Producer | Earlier on path? | Independent of nodes 48--54? | Verdict |
|---|---|---:|---:|---|
| Minimal packed counterexample and target avoidance | nodes 4--16 | yes | yes | pass |
| Selected maximum induced-P13 packing | node 17 / `VerifiedP13PackingPrefix` | yes | yes | pass |
| Same-context node-21 multi-scale prefix | node 21 / `VerifiedP13MultiScaleCurvaturePrefix` | yes | yes | pass |
| Exact remainder partition and remainder floor | nodes 25--26 / `VerifiedP13RemainderResidual` | downstream of the node-24 coverage value | yes | pass conditional on typed node-24 output |
| Net-deficiency incidence upper bound | nodes 29 and 47 provenance / `p13NetDeficiencyNumerator_le_coverageBudget` | yes once coverage exists | yes | pass |
| Quotient/full-rank ledger | node 47 / `P13DensityConnectedGlobalRankPrefix` | yes | yes | pass; magnitude unused |
| Exact quarter window budget | `P13WindowDensityStructuralTheorem` | **not produced** | yes by specification | **blocking** |
| Scaled strict inequality transfer | Core `FiniteBudgetTransfer` | framework | yes | pass |

No fact from the high-entropy sibling branch is used.

## Quantifier attack

| Claim | Literal form | Smallest countermodel attempted | Result |
|---|---|---|---|
| Response-preserving quotient injectivity realizes a Boolean cube | `(forall code, responsePreserving code -> Injective code) -> forall assignment, exists state, value state = assignment` | two coordinates and the three states `00`, `01`, `10` | false; all-true is absent |
| Separate two-value realization implies simultaneous realization | `(forall i b, exists s, value s i = b) -> forall epsilon, exists s, forall i, value s i = epsilon i` | same three-state system | false |
| Node-24 coverage may be selected after node 47 | `exists U, p13 <= U` used without the required strict budget | identity ceiling `U=p13` | insufficient; it need not prove the quarter inequality |
| Typed node-24 output implies node 56 | `forall ctx node21, VerifiedP13WindowDensityOutput ctx node21 -> strictQuarter ctx` | checked against compiled Lean composition | true |

Injection is not confused with surjection; pairwise/separate witnesses are not exchanged with one simultaneous witness; rank is not called a Boolean cube; no quotient representatives or context-generator completeness are used in the repaired route.

## Branch and invariant audit

- Positive-side payment: the genuine node-24 output pays the exact finite `P13QuarterNetBudget` into node 55.
- Negative side: absence of that output is the unresolved producer obligation, not a legal proof leaf. It prevents PASS.
- Measurability: after production, the payload consists only of the same-context finite ceiling and natural-number inequalities.
- Ladder legality: node 21 -> structural node 24 -> exact remainder/incidence bookkeeping -> retained node 47 provenance -> node 55 -> node 56.
- Cross-branch leakage: none found.
- Theorem weakened or assumption added: the production theorem is not weakened, but the sketch is conditional and therefore not mergeable. The condition is visibly isolated rather than installed as a standing manuscript hypothesis.

## CT and route obligations

| Instance | Trigger | Unfilled schema | Payload/consumer mismatch | Verdict |
|---|---|---|---|---|
| Fixed cold-skeleton/F2--F5 node-24 producer | same node-21 context and selected packing | proof of packing ceiling plus exact strict-quarter finite inequality | none specified once produced | **blocking: producer absent** |
| Node-47 provenance wrapper | verified node-24 output | none | none | pass |
| Node-55 finite budget | verified node-24 output | none | exact `P13QuarterNetBudget` matches node 56 | pass |
| Node-56 transfer | node-55 budget, incidence upper bound, remainder floor | none | none | pass |

The repair introduces no interface-changing CT and no loop. The structural boundary has one consumer, node 55, through the compiled same-context wrappers.

## Reused closed routes

| Handoff | Exact trigger | State transported | Dependency cone | Independent? | Cycle | Verdict |
|---|---|---|---|---:|---|---|
| node 24 -> node 47 wrapper | `VerifiedP13WindowDensityOutput ctx node21` | identical `ctx`, `node21`, packing, coverage | rank closure through node 47 | yes, nodes 48--54 absent | none | pass |
| node 47/node 24 -> node 55 | `P13QuarterNetBudget` from node 24 | identical coverage | finite budget only | yes | none | pass |
| node 55 -> node 56 | upper bound, strict budget, remainder floor | identical remainder | Core arithmetic and remainder ledger | yes | none | pass |

## Leaf totality

| Leaf | Certificate or consumer | Exact proof | Practical checker | Verdict |
|---|---|---|---|---|
| Nodes 48--54 | removed, not a leaf | fixed Lean countermodel rejects implication | constant fixed universe | pass |
| Node-24 output exists | node 55 then node 56 | compiled conditional composition | constant arithmetic after certificate | pass conditional on producer |
| Node-24 output absent | no C1--C5 certificate and no typed closing consumer | none | n/a | **blocking** |

The last row is why the repair is not ready for merger.

## Practicality and termination

- Largest universe enumerated by the repaired production route: none.
- Fixed countermodel universe used only in the negative audit: two coordinates, three states.
- Ambient-size complexity after node 24: constant number of natural-number operations.
- Certificate checker: projections plus natural-number inequality checking; the future node-24 certificate must be locally checkable from fixed cold-skeleton/F2--F5 data.
- Cycles: none.
- Hidden global computation: none found in the production route.

## TeX--Lean--framework correspondence

- Exact statement match: the sketch uses natural-number truncated subtraction and the exact Lean `P13QuarterNetBudget`, not an asymptotic quotient.
- Generic ownership: scaled transitivity is in Core and has a non-Erdos example.
- Problem layer: concrete context, packing, coverage, surplus, deficiency, and thin wrappers only.
- Transfer example: `StructuralExhaustion.Examples.FiniteBudgetTransfer`.
- `sorry`/`admit`/`axiom`/`unsafe`: none in the production closure-robust file or this sketch.
- Trust base: Lean kernel and the already registered proof inputs; no new external theorem.
- Source manuscript: not edited by this repair task; baseline hash remains the audit reference.

## Findings

### Blocking

1. `P13WindowDensityStructuralTheorem ctx node21` has no production inhabitant. The genuine fixed cold-skeleton/F2--F5 proof must produce the same-context ceiling and strict finite quarter budget. Until then node 24 and nodes 48--56 remain unclosed.

### Required cleanup

None beyond resolving the blocking producer and rerunning this complete audit.

### Advisory

When the producer is proved, replace the Part-IV source diagram rather than leaving nodes 48--54 visually on the main path. Optional curvature-entropy observations must be labelled non-load-bearing and separately conditional.

## FAIL disposition

- Exact obligation returned to the repair loop: construct `P13WindowDensityStructuralTheorem ctx node21` from the genuine fixed cold-skeleton/F2--F5 branch on the identical selected packing.
- Negated residual: every candidate ceiling supplied by the attempted local producer fails either `p13 <= U` or `4 * ((15*U + sigmaW) dotminus sigmaR) < n dotminus 13*U`; its first failed local F2--F5 ledger clause must be extracted and routed, not assumed away.
- Methodology re-entered: level-2 invariant selection and both-sides test, followed by level-3 interface review only if the fixed local payload is inexpressible.
- New invariant/finer split: fixed cold-skeleton/F2--F5 first-failure data, with the exact failed ledger clause as the residual selector.
- Discharged in this iteration: the false rank-to-cube implication and all node-47-to-node-56 arithmetic/interface obligations.
- Complete audit rerun after producer proof: **no; required before PASS**.

## Verdict

**FAIL -- merger blocked.** The proposed route is the correct non-enumerative conditional spine and its downstream Lean composition is verified, but leaf totality fails exactly at the missing genuine node-24 producer. No source-manuscript edit and no green status are authorized.

## Checks recorded for this audit

- `lake build Erdos64EG.P13ClosureRobustPartIV Erdos64EG.WebExport`: passed.
- `make example-export`: framework and all example packages passed.
- `python3 tools/render_example_catalog.py --raw-root build/example-exports --root . --source-root . --catalog generated/lean-machines.json`: passed.
- `npm run test -- --run src/erdos-proof-flow.test.ts`: six tests passed.
- `git diff --check` on the repair artifacts: passed.
- Source manuscript SHA-256 after drafting: `6cea87715450176e2b3e611a347c7147764730866c7174122e5be0445235c671`, unchanged from the recorded baseline.
