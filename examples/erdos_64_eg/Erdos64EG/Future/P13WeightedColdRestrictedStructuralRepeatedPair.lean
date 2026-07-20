import Erdos64EG.Future.P13WeightedColdRestrictedStructuralCutState

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

theorem repeated_stage_val_lt
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    repetition.first.val < repetition.second.val :=
  Core.FiniteExactStateCorridor.Profile.Repeated.relation_of_stages_pairwise
    (profile := package.coldStructuralCorridorProfile survivor)
    (R := fun earlier later : package.Stage => earlier.val < later.val)
    repetition package.positiveStages_pairwise_val_lt

/-- The Core repetition directly determines the paper's earlier/current
two-boundary pieces.  No coarse-code match and no degenerate outcome is used. -/
noncomputable def repeatedPriorPiecePair
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    package.PriorPiecePair repetition.second repetition.first := by
  apply package.priorPiecePair repetition.second repetition.first
  apply List.mem_filter.mpr
  constructor
  · change repetition.first ∈
      package.profile.stages.values.take repetition.second.val
    rw [package.profile.stages_values_eq_finRange]
    apply (List.mem_take_iff_idxOf_lt
      (List.mem_finRange repetition.first)).mpr
    simpa using package.repeated_stage_val_lt survivor repetition
  · exact decide_eq_true (package.repeated_first_positive survivor repetition)

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
