import Erdos64EG.Node2
import HypostructureErdos64EG.Node2
import HypostructureParity.Erdos64EG.Node1

namespace HypostructureParity.Erdos64EG.Node2

open Hypostructure

universe u

/-!
# Diagram node 2 parity

The immutable proof diagram assigns node `[2]` the exhaustive
counterexample decision.  This module compares the paper-visible branch
predicates: the positive branch is the minimum-degree baseline together with
target avoidance; the negative branch is target realization.

The legacy root residual contains an additional large-tail proof used later
in the old implementation.  It is not part of node `[2]` in the original
paper, so parity here is normalized to the graph, baseline, target, and
branch propositions.
-/

/-- The two target predicates are equivalent on the normalized root graph. -/
theorem target_iff (object : Hypostructure.Graph.FiniteObject.{u}) :
    _root_.Erdos64EG.Internal.Target (Node1.legacyView object) ↔
      HypostructureErdos64EG.Target object := by
  exact
    (_root_.Erdos64EG.Internal.target_iff_official_conclusion
      (Node1.legacyView object)).trans
      (HypostructureErdos64EG.target_iff_official_conclusion object).symm

/-- Both node-2 positive branch predicates mean baseline plus target
avoidance for the same graph. -/
theorem counterexample_iff
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    _root_.Erdos64EG.Internal.IsCounterexample
        (Node1.legacyView root.object) ↔
      HypostructureErdos64EG.IsCounterexample
        (HypostructureErdos64EG.node1 root) := by
  change
    (_root_.Erdos64EG.Internal.Baseline
        (Node1.legacyView root.object) ∧
      ¬ _root_.Erdos64EG.Internal.Target
        (Node1.legacyView root.object)) ↔
      (HypostructureErdos64EG.problem.Baseline root.object ∧
        ¬ HypostructureErdos64EG.Target root.object)
  exact and_congr (Node1.baseline_iff root.object) (not_congr (target_iff root.object))

/-- Both node-2 negative branch predicates mean target realization for the
same graph. -/
theorem notCounterexampleTarget_iff
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    _root_.Erdos64EG.Internal.Target (Node1.legacyView root.object) ↔
      HypostructureErdos64EG.IsNotCounterexample
        (HypostructureErdos64EG.node1 root) := by
  change
    _root_.Erdos64EG.Internal.Target (Node1.legacyView root.object) ↔
      HypostructureErdos64EG.Target root.object
  exact target_iff root.object

/-- The Hypostructure node-2 executor exposes the same normalized branch
proposition as the legacy counterexample setup. -/
theorem node2_exhaustive_normalized
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    match
      (HypostructureErdos64EG.node2
        (HypostructureErdos64EG.node1 root)).added
    with
    | .yesBranch _proof =>
        _root_.Erdos64EG.Internal.IsCounterexample
          (Node1.legacyView root.object)
    | .noBranch _proof =>
        _root_.Erdos64EG.Internal.Target
          (Node1.legacyView root.object) := by
  cases branch :
      (HypostructureErdos64EG.node2
        (HypostructureErdos64EG.node1 root)).added with
  | yesBranch proof =>
      exact (counterexample_iff root).mpr proof
  | noBranch proof =>
      exact (notCounterexampleTarget_iff root).mpr proof

/-- A legacy-visible target certificate forces the Hypostructure node-2
negative branch. -/
theorem node2_no_branch_of_legacy_target
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (target :
      _root_.Erdos64EG.Internal.Target (Node1.legacyView root.object)) :
    ∃ proof :
      HypostructureErdos64EG.IsNotCounterexample
        (HypostructureErdos64EG.node1 root),
      (HypostructureErdos64EG.node2
        (HypostructureErdos64EG.node1 root)).added =
        Core.Residual.Decision.Binary.noBranch proof :=
  HypostructureErdos64EG.node2_no_branch_of_target
    (HypostructureErdos64EG.node1 root)
    ((notCounterexampleTarget_iff root).mp target)

#print axioms target_iff
#print axioms counterexample_iff
#print axioms notCounterexampleTarget_iff
#print axioms node2_exhaustive_normalized
#print axioms node2_no_branch_of_legacy_target

end HypostructureParity.Erdos64EG.Node2
