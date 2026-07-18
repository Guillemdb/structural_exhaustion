# Type B nodes [65]--[74]: exact missing producers

This note records the first unsatisfied implications found by the sequential
Lean audit. It does not add a diagram node, edge, branch, or assumption.
`original_erdos_64_proof.tex` remains the immutable flow specification.

## 1. The ordinary [64] -> [65] handoff does not produce the assigned scope

### Node [65] obligation ledger

This ledger expands node [65] into its individual responsibilities.  A row is
`proved` only when the displayed evidence consumes the exact incoming value;
conditional structures whose missing fields are supplied by a caller are not
evidence for the row.

| Task | Original-paper obligation | Incoming producer | Current Lean evidence | Status | Missing producer |
|---|---|---|---|---|---|
| 65.1 | Retain the connected negative ordinary support on the `[64] -> [65]` edge. | `TypeBEntryRouting.VerifiedNode64Residual` | `VerifiedNode65Residual.ordinary`, `VerifiedNode65Residual.source_ordinary`, `VerifiedNode65Residual.negative` | proved | --- |
| 65.2 | Retain the decorated exit-(7) support and all of its handoff semantics on the `[66] -> [65]` edge. | `TypeBEntryRouting.Node66Residual` | `VerifiedNode65Residual.decorated`, `VerifiedNode65Residual.source_decorated`, `node66_data` | proved for a produced node-[66] value | The unconditional node-[108] producer remains a predecessor obligation. |
| 65.3 | Take the counted remainder core `Y_X` to be the exact localized support, with remainder and component provenance unchanged. | node [64] ordinary residual | `VerifiedNode64Residual.support`, `core_subset_remainder`, `remainder_neighbor_closed` | proved | --- |
| 65.4 | Assign to `X` exactly all high-degree centers of `Y_X`, and retain the selected high-surplus center as a member. | node [64] ordinary residual | `NegativeSupportHandoff.chargeProfile`, `node64_center_mem_assignedCenters` | proved | --- |
| 65.5 | Define the ordinary and center charges, augmented ledger, exact B-ledger identity, and the nonnegative-ledger implication. | exact core and assigned-center family from 65.3--65.4 | `AssignedSupportCharge.Profile.coreQuarterChargeAt`, `centerQuarterChargeAt`, `augmentedQuarterCharge`, `netQuarterCharge_eq_augmented_add_centers`, `netQuarterCharge_nonnegative_of_augmented` | proved | --- |
| 65.6 | Produce the actual external assigned fan-incidence carrier set, without treating an unassigned incidence as assigned. | node [64] ordinary residual plus the canonical support assignment | `TypeBFanIncidenceSupportClassification.route` identifies the actual incidence geometry; `TypeBFanHybridReadiness.classify` returns `WindowAssignmentRequest` or `InternalAssignmentRequest` when an assignment proof is needed. | missing | A theorem on the existing `[64] -> [65]` edge deciding the `FanClosedPort.Assigned` judgment for each requested actual carrier. |
| 65.7 | Produce the ordinary deficiency/window-incidence reserve and prove that every assigned Type B carrier is disjoint from it exactly when the paper's unit is unused. | canonical support and stub assignment inherited at [65] | `Graph.RefinedFanLedger.Reserve` is only the target data type; no constructor from `VerifiedNode64Residual` exists. | missing | A semantic reserve producer tied to the same canonical component and packed-window incidence assignment. |
| 65.8 | Produce, for every assigned high center, either its complete marked-fan certificate map or the genuine absence result used by the certificate branch. | exact assigned high-center family from 65.4 | `TypeBFanCertificateRequirement.route` reaches only the first legal-label request.  `MarkedFan` requires an attachment on every actual port, legality at every port, and pairwise compatibility. | missing | A local certificate producer from the actual packed-window attachments; it must not enumerate a label universe or default every center to `none`. |
| 65.9 | Preserve the no-double-counting convention: an assigned center is not reused as a non-center carrier, and a grouped decorated support follows the transfer identity. | ordinary [64] and decorated [66] inputs | The ordinary assigned-center membership is proved, and the decorated handoff is retained, but no complete carrier assignment exists with which to state the required disjointness/transfer theorem. | partial | Completion of 65.6--65.8 on the exact joined support. |
| 65.10 | Expose a finite local schedule and practical bound for constructing the node-[65] payload. | actual core, actual high centers, actual port/shoulder schedules | High centers and incidence coordinates are finite local scans; `TypeBFanHybridReadiness.visibleChecks_linear` proves the shoulder readiness scan is linear. | partial | The work of the missing assignment/reserve/certificate producers cannot be bounded until those producers are defined. |

Therefore node [65] is not one missing Boolean.  Its core, center family, and
charge algebra are already kernel-checked, while tasks 65.6--65.8 are three
specific semantic producer obligations.  Filling `assignedCarriers` with the
empty set, using an empty reserve, or mapping every center to `none` would make
the structure inhabited but would not prove the paper's assigned-support
claim.

The original crosswalk places the marked-fan definition at [70], the
certificate-presence/cap step at [71], and the B1/B2 carrier ledger at
[72]--[74].  Thus tasks 65.6--65.8 are outgoing payload obligations needed by
those existing consumers, not additional cases at [65].  A web projection may
attach them to the exact downstream node tasks, but it must not manufacture a
new edge or treat a default-filled `TypeBSupportScope` as the producer.

`TypeBEntryRouting.VerifiedNode64Residual` contains:

- the exact connected negative vertex support selected at [61];
- one actual high-center witness from [62]; and
- the typed ordinary high-surplus tag.

The later `TypeBSupportScope` additionally requires:

- the finite external assigned-carrier set;
- the pre-existing vertex/incidence reserve; and
- the optional certificate marking at every actual high center.

No theorem currently constructs these three fields from the node-[64]
residual. In particular, the ordinary tag in
`Routes.NegativeSupportHandoff.OrdinaryResidual` contains only the high-center
witness. It does not prove that the external carrier set or reserve is empty.
Consequently, instantiating both fields by the empty set would be a fresh
assignment convention, not a consequence of the incoming original edge.

The required existing-edge producer is a theorem constructing the precise
assigned-support data asserted at [65] from the ordinary [64] residual, with
the decorated data supplied only by the separate existing [66] input.

## 2. Certificate presence does not yet imply a complete [72] local entry

For a supplied `TypeBSupportScope`, Lean already performs the exact certificate
presence split. If a certificate is present, however, `CT12TypeBResolution`
still permits `UnresolvedCenter`: a marked center may have neither a
`CertificateClosedMarkedFan` nor a `PositiveDeficitMarkedFan` value.

The certificate-closed value is constructible when the computed inequality

```text
4 * closedCount + degree <= 11
```

holds. In the complementary positive-deficit case, the current
`PositiveDeficitMarkedFan` constructor requires two distinct fan-compatible,
fan-closed ports and their four actual assigned incidences. Pairwise
compatibility of the certificate labels does not prove the graph predicate
`HighCenterPort.FanCompatible`: the latter also requires endpoint/shoulder
exclusion and disjoint shoulder lists.

The graph library closes a shared-shoulder failure by a 4-cycle, and closes an
endpoint-in-shoulders failure when one port is triangular. It deliberately
retains the open--open endpoint failures. No current predecessor theorem routes
those remaining failures to one of the original outcomes before [72]. Thus the
present `DegreeFourB2Route.unresolved` constructor is not yet justified as an
original [72] -> [73] outcome, and it must not be used to mark [72] or [73]
green.

The missing original-flow lemma must show, from the exact assigned marked fan
and the already tested predecessor exits, either:

1. the nonpositive-deficit certificate-closed entry; or
2. the positive B1 entry with two actual compatible closed ports; or
3. one of the already existing earlier closing outcomes.

It may not introduce a new residual constructor.

## 3. Full B2 does not currently prove the [74] conclusion

The original node [74] promises nonnegative net charge outside route 8. The
strongest unconditional implemented theorem for a full disjoint choice is
`unresolved_or_overlap_or_net_nonnegative_or_saturated_or_bounded_boundaryOverload`.
On its full-choice branch it still permits:

- a saturated receiver in the literal remaining Type A core; or
- strict boundary-transfer overload, with only a quantitative deficit bound.

Neither outcome is `No(X) >= 0`, and the original Part VI diagram has no new
branch leaving [74] for either condition. Closing [74] therefore requires the
existing manuscript strategy to discharge the saturated remaining core and to
prove the boundary transfer (or derive an already existing route-8 outcome)
from the exact B2 payload. The current coefficient bound does not supply that
implication.

## Status consequence

Until these producers exist, nodes [65]--[74] cannot form an unconditional
derive-from-[1] chain. Conditional CT9/CT12/CT14 executions on caller-supplied
marked fans and scopes remain valid reusable lemmas, but they are not whole-node
implementations of the original flow.
