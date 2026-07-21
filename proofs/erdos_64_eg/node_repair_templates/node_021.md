# Node [21] repair template

| Field | Value |
|---|---|
| Incoming | [19] no -> [21] |
| Outgoing | [21] -> [22] and existing cross-panel continuations |
| Responsibility | Perform the finite enumeration producing c_Omega and c_13. |
| Retained facts | Exact near-cubic branch and node18 label algebra. |
| New output | Certified finite constants and near-cubic budget facts. |
| CT chain | CT10 finite enumeration/classification successor. |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N21-PRED | Consume the literal node-[19] no-stage and no other branch | [19] | `Node21Stage`, `node21MultiScaleCurvature`, `runInitialThroughNode21` via framework `continueDependentDecisionNo` | complete |
| N21-PAIRS | Classify the 196 ordered length pairs and retain exactly the 91 pairs with positive lengths and sum at most 14 | [21] | `p13Barrier_candidate_count`, `p13Barrier_class_count`; the latter uses `Core.FiniteTriangle` | source complete; focused kernel recheck pending the serialized build |
| N21-SEMANTICS | Identify every one of the fifteen 399-row packed relations with the manuscript's local `P13CodeCompatibleSparse` relation | [18], [21] | `Erdos64EG.Node21.Certificates`, shallow `p13AscendingCodes`, thirteen certified feature columns, `p13CodeCompatibleSparse_iff_forbiddenMask`, chunked `p13MultiScaleRows_codeAudit`, `p13MultiScaleCompatibilityRow_semantic` | dedicated certificate index added; leaf audits remain cached native certificates pending pointwise kernel migration |
| N21-SAFE | Prove every stored safe count is the reusable barrier profile's safe count on the accepted 91-pair schedule | [21] | `p13MultiScaleSafeCounts_audit`, `p13BarrierSafeCount_audit` | partial: exact statements exist, but their cached proofs still use `native_decide` |
| N21-FLAT | Prove every stored composition-flat count is the reusable barrier profile's flat count on the accepted 91-pair schedule | [21] | `p13MultiScaleFlatCounts_audit`, `p13BarrierFlatCount_audit` | partial: exact statements exist, but their cached proofs still use `native_decide` |
| N21-ONEONE | Certify the scale-(1,1) values 543958, 432672, and 111286 | [21] | `Node21Output.oneOneCounts`, shallow `safeCountsRows`/`flatCountsRows` | source upgraded to kernel `decide`; focused endpoint recheck pending the serialized build |
| N21-RATE | Prove the exact integer product inequality `2^118 * product(flat) < product(safe)` | [21] | `Node21Output.rateFloor`, `p13MultiScaleBarrier_more_than_118_bits` | source upgraded to kernel `decide`; the identical 91-factor proposition passes an isolated default-limit kernel check, endpoint recheck pending |
| N21-BUDGET | Attach the inherited near-cubic square budget | [19], [21] | `Node21Output.nearCubicBudget`, obtained directly from the literal `Node19Low` proof | complete |
| N21-CT10 | Retain CT10 stage, terminal, trace, and the single certified-table interface | CT10 | `Node21Output.stage`, `.certificate`, `.terminal`, `.trace` | partial until N21-SEMANTICS, N21-SAFE, and N21-FLAT are sole-HSS clean |
| N21-WORK | Prove the local polynomial work bound without unfolding the filtered class table | [21] | `Node21Output.polynomial`, `p13MultiScaleCheckCount_quadratic` | source complete via symbolic pair count and a shallow arithmetic `calc`; focused kernel recheck pending |

Forbidden: application SurplusScaleRoute or manual branch handoff.

Implementation note: the compliant node path uses only the framework-owned
`DependentDecisionNoContinuation`.  The older `SurplusScaleCurvatureRoute`
declarations remain temporarily for non-node consumers and are not evidence
for node `[21]`; they must be removed when those consumers migrate.

Interface note: `Node21MultiScaleCurvatureAPI.lean` owns only the exact fixed
barrier data, `Node21Context`, `Node21Output`, and `Node21Stage` types.
`CT10P13MultiScaleCurvature.lean` imports that API and remains the sole owner
of the finite audits and producer.  Node `[22]` imports only the API, so a
typed provisional node-[21] output can drive downstream source refactors
without replaying the unfinished node-[21] computation; this does not change
node `[21]`'s partial status.

Dashboard rule: node `[21]` remains partial while any of N21-SEMANTICS,
N21-SAFE, or N21-FLAT depends on a native finite-audit axiom. The old output
may be consumed provisionally by downstream refactors, but it is not green
kernel evidence.
