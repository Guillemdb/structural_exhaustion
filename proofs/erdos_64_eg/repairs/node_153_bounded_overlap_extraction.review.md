# Node [153] bounded-overlap extraction audit

Date: 2026-07-17

Audited obligation: `XI-153-15`, the existing node-[153] output in
`lem:cold-germ-extraction`.  The immutable source is
`original_erdos_64_proof.tex`; the synchronized statement is in
`proofs/erdos_64_eg/erdos_64_proof.tex`.  This audit adds no diagram node,
edge, case, or premise.

## Paper contract

The paper's extraction has four dependency-ordered inputs.

1. After the named routed losses, every remaining selected branch-excess
   half-edge produces one canonical `ColdBoundedGerm` incidence, so the
   candidate count is at least `b - loss`.
2. Every candidate support has at most `M_cold` vertices and every graph
   vertex belongs to at most `B_cold` candidate supports.
3. Greedy bounded-overlap extraction returns pairwise vertex-disjoint germs
   with denominator
   `D_cold = M_cold * B_cold + 1`.
4. The named losses are `o(n)`, and the exact predecessor inequalities
   substitute `b >= 13 C - o(n)` and
   `C >= (theta - theta_win) n - o(n)`.

## Reusable extraction already proved

The purely finite third step is complete in
`StructuralExhaustion.Core.FiniteBoundedOverlap`.

- `LocalMultiplicityProfile.overlap_card_le_mul` derives the intersection
  bound from literal support-cardinality and point-fibre bounds.
- `LocalMultiplicityProfile.toProfile` uses exactly the manuscript
  denominator `M * B + 1`.
- `Profile.supply_sub_loss_div_le_selected` and
  `Profile.supply_le_selected_mul_add_loss` retain an explicit routed loss.
- `Profile.selected_pairwise` proves that the selected supports are pairwise
  vertex-disjoint.

The non-Erdős fixture `FiniteColdGermLedger` exercises both the local
multiplicity API and the routed-loss API.  Thus no new Core extraction theorem
is needed, and duplicating this arithmetic in an Erdős module would violate
framework ownership.

## Exact graph data currently available

The existing node-[151]/[152] prefix supplies the following unconditional
inputs without an ambient scan.

- `p13WeightedColdBranchExcessSchedule_length` proves exactly thirteen
  selected branch-excess sources per retained ambient-cubic cold window.
- `p13WeightedColdCubicWindows_nodup`,
  `p13WeightedColdBranchExcessStubs_nodup`, and
  `p13WeightedColdBranchExcessSchedule_nodup` now prove that the filtered
  windows, the thirteen local incidences, and the complete dependent schedule
  contain no duplicates.
- `P13WeightedColdBranchExcessStub.sameWindow` retains the literal source
  window of every entry.
- `thirteen_mul_weightedCold_le_branchExcess_add_surplus` and
  `verifiedP13WeightedColdNearCubicPayment` retain the exact non-cubic loss and
  its square-root bound.
- `p13WeightedColdRestrictedEntries_length` preserves every source through
  the cold-only entry decision.
- The F5 frontier proves the repeated-span support bound
  `QCold + 1` and retains the exact terminal or repeated structural support.

These declarations stop before a graph-produced `ColdBoundedGerm`.  The
current frontier deliberately retains only structural F5 data.

## First blocking producer

`XI-153-15` is not dependency-ready.  Its first missing producer is the
existing F5-to-germ responsibility already recorded as `XI-153-12` and
`XI-153-13`: node [153] must construct one actual `ColdBoundedGerm` from every
surviving terminal or repeated F5 result and retain the unique originating
node-[152] half-edge.  The present payload does not contain the required
second same-interface representative, proper atom, full boundary-degree
profile equality, finite response/reflection table, or symbolic context
coverage.  Introducing any of those as a caller argument would assume the
missing paper conclusion and is therefore forbidden.

Consequently there is currently no application-level finite candidate type,
support function, or proof that `b - loss` is bounded by its cardinality.
The generic bounded-overlap profile cannot be instantiated without inventing
that missing graph producer.

## Remaining subobligations in dependency order

1. **F5 germ construction (`XI-153-12`).** Construct the complete
   graph-owned `ColdBoundedGerm` on the exact terminal or repeated support,
   including both same-interface representatives and all replacement/response
   data.
2. **Canonical incidence and loss partition (`XI-153-13`).** The exact
   node-[152] source schedule is now duplicate-free.  It remains to map every
   surviving source to exactly one graph-produced germ, retain that source in
   the germ payload, and partition all other sources into only the named
   surplus, non-ambient-cubic, Type-B, and route-8 losses.
3. **Support bound (`XI-153-14`).** Upgrade the exact F5 support bounds to the
   paper's complete `M_cold` support, including the two windows and boundary
   stubs.
4. **Graph point multiplicity (`XI-153-14`).** Prove that a candidate
   containing a fixed vertex originates from one of at most
   `1 + 3(2^(M_cold+2)-1)` nearby subcubic vertices and one of at most fifteen
   source stubs.  This requires the graph-owned localization from a candidate
   support to its retained source; the numerical ball estimate alone is not
   an application proof.
5. **Finite extraction (`XI-153-15`).** Instantiate
   `FiniteBoundedOverlap.LocalMultiplicityProfile` with those actual germs and
   invoke the already proved routed-loss and pairwise-disjoint theorems.
6. **Asymptotic loss payment (`XI-153-15`).** Prove the combined named loss is
   `o(n)`.  The non-cubic square-root loss is available, but branch-total
   Type-B/route-8 handoff losses and the candidate-incidence partition are not.
7. **Final substitutions (`XI-153-15`).** Compose the extracted bound with the
   exact node-[152] branch-excess payment and the node-[150] cold-mass bound to
   obtain the two printed inequalities through `13 C` and
   `theta - theta_win`.

## Verdict

`XI-153-15` remains **missing**.  The reusable greedy mathematics is proved;
the obstruction is the earlier graph-semantic producer and its actual
bounded-multiplicity/loss ledger.  No WebExport or dashboard status is
promoted by this audit.

Focused verification:

- `lake build StructuralExhaustion.Examples.FiniteColdGermLedger`: pass
  (2,975 jobs).
- `lake build Erdos64EG.P13WeightedColdRestrictedColdGermFrontierTests`: pass
  (8,958 jobs).
- `lake build Erdos64EG.P13WeightedColdBranchExcess`: pass (8,804 jobs).
- `lake build Erdos64EG.P13WeightedColdBranchExcessNodupTests`: pass (8,805
  jobs); the axiom audit contains only `propext`, `Classical.choice`, and
  `Quot.sound`.
