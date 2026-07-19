# Node [8] repair template

## Paper identity

| Field | Value |
|---|---|
| Node ID | [8] |
| Incoming edges | [6] no -> [8] |
| Outgoing edges | [8] -> [9] |
| Local responsibility | Prove that the selected minimal counterexample has no proper subgraph of minimum degree three in the target-avoiding regime. |
| Retained branch facts | Minimality, target algebra, and exact CT1 avoidance. |
| New output | No-proper-core certificate. |
| CT chain | Framework CT1-avoidance to CT2 local-deletion/minimality successor. |
| Immediate consumers | [9] |

## Obligations

| Task ID | Paper assertion | Producer | Lean evidence | Edge | Status |
|---|---|---|---|---|---|
| N8-PRED | Consume literal node-[6] no-stage | [6] | `Node8Stage`; `node8NoProperCore` via `CT1.ResidualRefinement.continueCertificateAvoidingUsingStage` | no->[8] | proved |
| N8-QUERY | Retrieve minimality and avoidance from the ledger | [4],[6] | literal `Node6Stage` predecessor retained by `CertificateAvoidingContinuation` | no->[8] | proved |
| N8-CORE | Prove no proper minimum-degree-three subgraph | [8] | `Node8Output`; `node8_noProperCore`; `SelectedNoProperCore.certificate` | [8]->[9] | proved |
| N8-CERT | Preserve CT execution, semantics, totality, and work | CT2 | `node8_ct2_certificate`; `EdgeRootedNoProperCorePrefix.properCoreTotal`; `.properCorePolynomial` | [8]->[9] | proved |

## Framework and validation record

- Uses the framework-owned literal CT1 avoiding continuation and the reusable
  packed-minimality/CT2 executor `StaticInput.selectNoProperCore`.
- No reconstruction from root inputs is permitted.
- Focused kernel command: `cd examples/erdos_64_eg && lake build
  Erdos64EG.Node8NoProperCore` (passed).
- Trust audit: `runInitialThroughNode8`, `node8_noProperCore`, and
  `node8_ct2_certificate` use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Dashboard/TeX synchronization: pending.
