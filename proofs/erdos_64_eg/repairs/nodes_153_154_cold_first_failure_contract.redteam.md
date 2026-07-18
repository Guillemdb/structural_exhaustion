# Red-team audit: nodes [153]–[154] cold first-failure contract

## Baseline

* Repair sketch: `nodes_153_154_cold_first_failure_contract.md`.
* Read-only specification hash:
  `215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10`
  for `original_erdos_64_proof.tex`.
* Failed node and claim: [153] total F1–F5 routing from every selected
  branch-excess incidence, followed by [154] extraction with
  `D_cold = M_cold * B_cold + 1`.
* Methodology: both-sides test, finite first failure, typed handoffs, level-2
  repair protocol, level-3 interface audit and local-computation rules.
* **Verdict: FAIL for marking nodes [153]–[154] green.**  The generic finite
  subcontracts, corrected C153.1a/C153.1b restricted cold-component producer,
  and C153.2 prefix geometry pass.  C153.3–C153.6 and C154.1–C154.4 remain open.

## Provenance matrix

| Used fact | Producer | Earlier? | Independent? | Verdict |
|---|---|---:|---:|---|
| exact weighted-cold cubic list | `p13WeightedColdCubicWindows` | yes, [151] | yes | pass |
| thirteen selected tail stubs | `p13WeightedColdBranchExcessSchedule` | yes, [152] | yes | pass |
| same-window provenance | `P13WeightedColdBranchExcessStub.sameWindow` | yes | yes | pass |
| deleted-edge return | `P13WeightedColdBranchExcessStub.corridor` | yes | yes | insufficient for paper component corridor |
| broad component schedule/successor/path | `InducedPathBranchExcessComponentEntry.route` | existing graph producer | yes | auxiliary only: deletes hot ambient-cubic windows too |
| exact cold-only endpoint split | `P13WeightedColdRestrictedEntries` | C153.1a | yes | pass |
| exact restricted successor/path | `P13WeightedColdRestrictedComponentSchedule` | C153.1b | yes | pass |
| exact prefix stages | `P13WeightedColdRestrictedPrefixStages` | C153.2 | yes | pass |
| five-way aggregate partition | new `FiniteFirstFailureLedger.partition` | generic | yes | pass |
| `M*B+1` extraction | new `LocalMultiplicityProfile.extracted_div_bound` | generic | yes | pass |

No near-cubic, hot-entropy, G1–G3, or node-[24] conclusion is imported into
this branch.

## Quantifier attack

| Claim | Literal form | Countermodel/attack | Result |
|---|---|---|---|
| exact cut-state equality gives target equivalence | `code p = code q -> forall compatible c, response p c = response q c` | two prefixes may share all displayed bits while one omitted context distinguishes them | rejected; this is exactly F2 |
| no F2 gives F3 | `not (exists c, compatible c /\ differs c)` gives universal equivalence, but not a smaller valid representative | equal responses do not construct baseline, boundary profile, properness or strict decrease | rejected; F3 must carry all fields separately |
| every old corridor is the paper component corridor | equality of deleted-edge return with delete-all-windows successor path | paths have different deleted graphs and endpoints | rejected; C153.1 routes the same stub without asserting this equality, and C153.2 uses only the component constructor |
| all-ambient-cubic deletion equals cold-cubic deletion | every ambient-cubic selected window is weighted-cold | a hot ambient-cubic window | rejected; exact cold-family deletion introduced |
| point multiplicity gives overlap | each support has at most `M` vertices and each vertex lies in at most `B` candidates | tested for self-overlap and duplicate items | proved, including self, by `overlap_card_le_mul` |
| aggregate five-way accounting | every executed source has one run result | possible duplicate sources | partition holds regardless; separate `run_sources_nodup` requires and preserves source `Nodup` |

Injection is never presented as state realization.  Pairwise context witnesses
are not combined into one context.  No rank statement is used.  Representative
existence is an explicit F3/F5 payload obligation.  Context coverage remains a
reflection theorem, not a finite-table cardinality assertion.

## Branch and invariant audit

* Positive payments: F1 target cycle; F2 exact distinction; F3 exact proper
  target-complete exchange; F4 exact named ledger key.
* Negative residual: exhaustive absence of F1–F4 constructs F5 only after a
  terminal/repeated exact state and with a bounded support.
* Measurability: first hit is over one stored finite prefix list.  A
  distinguishing context is proof-selected; the ambient context type is not
  enumerated.
* Cross-branch leakage: none in the generic implementation.  The existing
  older corridor runner's `False`/`Empty` F2/F3 fields may not be reused as
  proofs that these branches are impossible.
* No theorem is weakened and no semantic conclusion is added as a standing
  hypothesis.

## CT and route obligations

| Instance | Trigger | Unfilled schema | Verdict |
|---|---|---|---|
| cold-only endpoint dichotomy | exact weighted node-[152] source stub and list membership | none; restricted route retains both outcomes | pass |
| restricted component schedule | cold-only surviving boundary | none; family is retained through successor and both BFS objects | pass |
| finite first failure | exact component-prefix stages | graph-owned stage construction and F1–F4 deciders/data | blocking |
| F2 to target defect | one literal compatible-context distinction | exact sparse/exit-(4) trigger and state transport | blocking |
| F3 to CT3/replacement | complete proper exchange | construction of atom/replacement and strict decrease | blocking |
| F4 handoff | first declared envelope/carrier hit | ledger recognition from inherited branch state | blocking |
| finite bounded overlap | finite F5 subtype, support bound, point multiplicity | none at Core level | pass |
| graph multiplicity | subcubic bounded F5 support | radius containment, subcubic ball bound, fifteen-source accounting | blocking |
| G handoff | selected disjoint F5 output | complete `ColdBoundedGerm`, especially context reflection | blocking |

## Leaf totality

| Leaf | Consumer | Certificate | Verdict |
|---|---|---|---|
| cold-deleted endpoint | future cold cross-window ledger | exact same-source restricted residual | producer pass; downstream ledger consumer remains separate |
| F1 | G1/CT1 | literal dyadic cycle | producer open |
| F2 | target-defect route | context and differing responses | route open |
| F3 | CT3/replacement | same-interface proper exchange | producer/route open |
| F4 | Type B or route 8 | exact ledger key | recognizer open |
| F5 | node [154], then G1–G3 | bounded repeated/terminal germ | producer and reflection open |

Accordingly the full branch is not total yet.  The new generic ledger is
total for any fully defined `FiniteFirstFailure.Profile`, but that theorem is
not being misreported as the Erdős producer.

## Practicality and termination

* Largest enumerated universe in the new code: the explicitly supplied local
  source/stage/item types.
* Ambient complexity: one list map plus the sum of stored stage lengths; the
  overlap theorem uses the already finite F5 item subtype.
* No ambient graph, path, context, support or completion universe is
  generated.
* Recursion is structural on finite lists.  Maximum disjoint packing is
  proof-level finite choice; its checker consumes only support disjointness.
* The non-Erdős transfer fixtures compile for both new contracts.

## TeX–Lean–framework correspondence

* The live and original manuscripts were not edited by this workstream.
* Generic ownership passes: aggregate first-failure bookkeeping and
  size/multiplicity extraction live in `StructuralExhaustion.Core`.
* The Erdős-specific graph adapter has deliberately not been faked by a
  caller contract.
* Transfer examples:
  `Examples.FiniteFirstFailureLedger` and the local-multiplicity additions to
  `Examples.FiniteColdGermLedger`.
* Search of changed proof files finds no `sorry`, `admit`, or `axiom`.

## Findings

### Blocking

1. **C153.3–C153.6:** exact response pair comparison, F1 completion, F2/F3
   routes and F4 ledger recognizer are not
   constructed from that source.
2. **C154.1–C154.2:** `B_cold` still lacks its graph proof (radius containment,
   subcubic ball size and source multiplicity).
3. **C154.4:** F5 has not constructed the full reflected same-interface germ
   required by G1–G3.

### Required cleanup

None in the two compiled generic contracts.

### Advisory

Retire both the older F1/F4/F5 schedule and the broad
`P13WeightedColdComponentEntries` schedule as evidence for node [153].  Keep
them only as auxiliary classifiers.

## FAIL disposition

The original C153.1 repair iteration fails paper fidelity because it deletes
all ambient-cubic windows.  The refined C153.1a iteration passes:
`P13WeightedColdRestrictedEntries` constructs its deletion family from the
literal weighted-cold cubic list, retains source membership, executes the
restricted endpoint split, proves the two-way partition, and has one visible
check per source.

Focused verification:

```text
lake build StructuralExhaustion.Graph.InducedPathRestrictedColdSkeleton
lake build StructuralExhaustion.Examples.InducedPathRestrictedColdSkeleton
lake build Erdos64EG.P13WeightedColdRestrictedEntriesTests
```

These pass.  There is no new axiom or author contract.

C153.1b now passes.  `InducedPathRestrictedComponentBoundarySchedule` retains
one explicit `CubicWindowFamily` through the outside BFS, exit scan, family
slot scan, boundary-token filter, cyclic successor, component object and
declared-order BFS shortest path.  `P13WeightedColdRestrictedComponentSchedule`
constructs its input from the exact C153.1a component constructor and the
same source token; no path is supplied by a caller.

Focused verification passes:

```text
lake build StructuralExhaustion.Graph.InducedPathRestrictedComponentBoundarySchedule
lake build StructuralExhaustion.Examples.InducedPathRestrictedComponentBoundarySchedule
lake build Erdos64EG.P13WeightedColdRestrictedComponentScheduleTests
```

C153.2 now passes.  `WalkPrefixFiltration` derives the finite stage order and
nested prefix supports from one supplied proof-carrying path, and the Erdős
package fixes that path to C153.1b's stored restricted component path.  It adds
no F1--F4 semantics.  Focused verification passes:

```text
lake build StructuralExhaustion.Examples.WalkPrefixFiltration
lake build Erdos64EG.P13WeightedColdRestrictedPrefixStagesTests
```

C153.3 literal soundness now passes.  The graph module maps a positive stored
prefix to the original graph, derives disjointness from the exact restricted
deletion, consumes two actual attachment adjacencies, and delegates only the
cycle construction to the already verified connector-cycle theorem.  The
Erdős module's production profile is stage-major: stored prefix order outside,
canonical `List.finRange 13` inside F1, then F2--F4 at the same prefix.  Every
F1 payload is a literal dyadic cycle and carries first-offset/no-earlier-offset
provenance.  The old global stage-product scan is auxiliary only and is not
used by the continuation runner.

Focused verification passes:

```text
lake build StructuralExhaustion.Graph.InducedPathRestrictedPrefixCompletion
lake build StructuralExhaustion.Examples.InducedPathRestrictedPrefixCompletion
lake env lean Erdos64EG/P13WeightedColdRestrictedF1Completion.lean
lake env lean Erdos64EG/P13WeightedColdRestrictedF1Handoff.lean
```

The audit rejects the stronger arithmetic-only reading of the paper's smear
sentence.  From one self-return with fixed attachment positions, acceptance
of one of the numbers `ell,...,ell+12` does not construct the return edge at
the corresponding offset.  The exact missing premise is

```text
G.Adj prefixEndpoint (selectedWindow anchorWindow offset).
```

The implemented F1 predicate tests precisely this local premise.  When it is
absent, the candidate remains non-F1; no target-response bit is converted into
an edge, no caller supplies a cycle, and no old deleted-edge F1 theorem is
used.  Thus C153.3's literal predicate/soundness passes, while the manuscript's
claim that every short self-return realizes the whole thirteen-length interval
remains a blocking structural lemma for any later argument that needs that
stronger conclusion.  The generic continuation constructs F5 only after an
exhaustive all-stage negative proof, but `RequiredF2F5Semantics` is explicitly
a missing-producer contract.  The first concrete blocker is the graph-owned
two-boundary prefix producer needed to build the literal F2 distinction or F3
universal-equality/replacement payload.  Therefore node [153] remains open.
