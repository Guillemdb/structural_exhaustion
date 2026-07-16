import StructuralExhaustion.Graph.SurplusPatternGermAudit
import StructuralExhaustion.Graph.SurplusPatternCoarseRouting

namespace StructuralExhaustion.Examples.SurplusPatternGermAudit

open StructuralExhaustion

universe u

/-! Framework transfer fixture for the exact homogeneous-pattern germ scan. -/

variable {input : Graph.PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : Graph.SurplusPortActivation.Setup input ctx}

theorem exact_scan_is_total
    (activation : Graph.SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    (windowSize remainderSize primitiveSize : Nat)
    (routed : Graph.SurplusClasswiseOverload.RoutedOverload activation
      windowSize remainderSize primitiveSize) :
    Nonempty (Graph.SurplusPatternGermAudit.VerifiedStage activation routed) :=
  ⟨Graph.SurplusPatternGermAudit.verifiedStage activation routed⟩

theorem retained_pair_has_exhaustive_geometry
    (activation : Graph.SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    {token : Graph.SurplusCapacityTokenRouting.Token (ctx := ctx) (setup := setup)}
    {pair : Graph.SurplusPairResponse.ScheduledPair (setup := setup)}
    (audit : Graph.SurplusPatternGermAudit.PairAudit activation token pair) :
    Graph.SurplusPatternGermAudit.PairAudit.kind activation audit = .parallel ∨
      Graph.SurplusPatternGermAudit.PairAudit.kind activation audit = .divergeAtRoot ∨
      Graph.SurplusPatternGermAudit.PairAudit.kind activation audit = .divergeAfterEdge :=
  Graph.SurplusPatternGermAudit.PairAudit.kind_cases activation audit

theorem fixed_coarse_collision_is_total
    (activation : Graph.SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Graph.SurplusPatternCoarseRouting.Routed activation
      windowSize remainderSize primitiveSize}
    (homogeneous : Graph.SurplusPatternCoarseRouting.HomogeneousAudit activation
      windowSize remainderSize primitiveSize routed)
    (large : 48 < (Graph.SurplusPatternCoarseRouting.patternPairs
      activation homogeneous).length) :
    ∃ collision : Graph.SurplusPatternCoarseRouting.VerifiedCollision
        activation homogeneous,
      Nonempty (Graph.SurplusPatternCoarseRouting.CanonicalGermResidual
        activation collision) := by
  let collision := Graph.SurplusPatternCoarseRouting.verifiedCollision
    activation homogeneous large
  exact ⟨collision, ⟨Graph.SurplusPatternCoarseRouting.canonicalGermResidual
    activation collision⟩⟩

/-! A concrete theorem-independent execution of the same 49-versus-48
collision kernel.  This fixture contains no graph or Erdős data. -/

def fixtureItems : List (Fin 49) :=
  (inferInstance : FinEnum (Fin 49)).orderedValues

def fixtureCode (item : Fin 49) : Fin 48 :=
  ⟨item.val % 48, Nat.mod_lt _ (by decide)⟩

def fixtureDecision :=
  Core.FiniteCodeCollision.decide
    (inferInstance : FinEnum (Fin 48)) fixtureCode fixtureItems

theorem fixtureDecision_is_collision :
    ∃ collision, fixtureDecision = .collision collision := by
  unfold fixtureDecision
  generalize decisionEq : Core.FiniteCodeCollision.decide
    (inferInstance : FinEnum (Fin 48)) fixtureCode fixtureItems = decision
  cases decision with
  | collision collision => exact ⟨collision, rfl⟩
  | unique codesNodup =>
      have bounded := Core.Enumeration.length_le_elems_of_nodup
        (inferInstance : FinEnum (Fin 48)) codesNodup
      rw [List.length_map, FinEnum.orderedValues_length] at bounded
      norm_num [fixtureItems] at bounded

end StructuralExhaustion.Examples.SurplusPatternGermAudit
