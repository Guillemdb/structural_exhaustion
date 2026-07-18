import StructuralExhaustion.Core.FiniteSearch
import StructuralExhaustion.Core.Enumeration
import Mathlib.Tactic

namespace StructuralExhaustion.Core.FiniteExactStateCorridor

universe uStage uCode

/-!
# Terminal-or-repeated exact-state corridors

This module performs the finite pigeonhole step used by bounded corridor
arguments.  It scans only the supplied ordered stages.  In the long case it
inspects the first `Q + 1` stages, where the producer supplies an injection of
its symbolic code into `Fin Q`, and returns two actual occurrences with equal
codes.  The code type itself is never enumerated.

The runner makes no response-reflection claim.  In applications such as the
cold-corridor argument, equal structural codes are followed by the separately
proved F2 outside-context comparison; only its neutral outcome may feed F3.
-/

structure Profile (Stage : Type uStage) (Code : Type uCode) where
  stages : OrderedCollection Stage
  stateBound : Nat
  encode : Code → Fin stateBound
  encode_injective : Function.Injective encode
  code : Stage → Code

namespace Profile

variable {Stage : Type uStage} {Code : Type uCode}
variable (profile : Profile Stage Code)

noncomputable def inspectedStages : List Stage :=
  profile.stages.values.take (profile.stateBound + 1)

theorem inspectedStages_sublist :
    profile.inspectedStages <+: profile.stages.values :=
  List.take_prefix _ _

theorem inspectedStages_length :
    profile.inspectedStages.length =
      min (profile.stateBound + 1) profile.stages.values.length := by
  simp [inspectedStages]

/-- Two distinct occurrences in the inspected prefix, in strict stage order.
The fields are positions, not merely values, so an equal stage value at two
different occurrences is retained faithfully. -/
structure Repeated where
  firstIndex : Nat
  secondIndex : Nat
  firstInBounds : firstIndex < profile.inspectedStages.length
  secondInBounds : secondIndex < profile.inspectedStages.length
  first : Stage
  second : Stage
  firstExact : first = profile.inspectedStages[firstIndex]'firstInBounds
  secondExact : second = profile.inspectedStages[secondIndex]'secondInBounds
  firstMem : first ∈ profile.stages.values
  secondMem : second ∈ profile.stages.values
  ordered : firstIndex < secondIndex
  equalCode : profile.code first = profile.code second

namespace Repeated

variable {profile}

theorem first_mem (repetition : profile.Repeated) :
    repetition.first ∈ profile.stages.values :=
  repetition.firstMem

theorem second_mem (repetition : profile.Repeated) :
    repetition.second ∈ profile.stages.values :=
  repetition.secondMem

theorem secondIndex_le_bound (repetition : profile.Repeated) :
    repetition.secondIndex ≤ profile.stateBound := by
  have lengthLe : profile.inspectedStages.length ≤ profile.stateBound + 1 := by
    rw [profile.inspectedStages_length]
    exact min_le_left _ _
  have indexLt := repetition.secondInBounds
  omega

theorem span_le_bound (repetition : profile.Repeated) :
    repetition.secondIndex - repetition.firstIndex ≤ profile.stateBound := by
  have := repetition.secondIndex_le_bound
  omega

/-- A repeated pair inherits any strict scheduling relation proved pairwise on
the supplied stage list.  This is independent of the code and does not unfold
or enumerate its symbolic alphabet. -/
theorem relation_of_stages_pairwise {R : Stage → Stage → Prop}
    (repetition : profile.Repeated)
    (orderedStages : profile.stages.values.Pairwise R) :
    R repetition.first repetition.second := by
  rw [List.pairwise_iff_getElem] at orderedStages
  have firstBound : repetition.firstIndex < profile.stages.values.length :=
    repetition.firstInBounds.trans_le
      (profile.inspectedStages_sublist.length_le)
  have secondBound : repetition.secondIndex < profile.stages.values.length :=
    repetition.secondInBounds.trans_le
      (profile.inspectedStages_sublist.length_le)
  rw [repetition.firstExact, repetition.secondExact]
  simpa [inspectedStages] using
    orderedStages repetition.firstIndex repetition.secondIndex
      firstBound secondBound repetition.ordered

end Repeated

/-- Exact result of the local corridor stopping rule.  The terminal branch
means the complete supplied corridor fits within `Q` stages.  The repeated
branch contains the first bounded prefix in which pigeonhole forces equal
exact states; consumers may choose their own deterministic first-pair policy
inside this bounded prefix. -/
inductive Outcome where
  | terminal
      (length_le : profile.stages.values.length ≤ profile.stateBound)
  | repeated (repetition : profile.Repeated)

private theorem exists_repeated_of_card_lt_length
    (long : profile.stateBound < profile.inspectedStages.length) :
    Nonempty profile.Repeated := by
  classical
  by_contra absent
  have unequal : ∀ (i j : Nat)
      (hi : i < profile.inspectedStages.length)
      (hj : j < profile.inspectedStages.length), i < j →
      profile.code profile.inspectedStages[i] ≠
        profile.code profile.inspectedStages[j] := by
    intro i j hi hj ordered equal
    apply absent
    exact ⟨⟨i, j, hi, hj, profile.inspectedStages[i],
      profile.inspectedStages[j], rfl, rfl,
      profile.inspectedStages_sublist.subset (List.getElem_mem _),
      profile.inspectedStages_sublist.subset (List.getElem_mem _),
      ordered, equal⟩⟩
  have encodedNodup :
      (profile.inspectedStages.map (profile.encode ∘ profile.code)).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
    intro i j hi hj ordered
    intro encodedEqual
    apply unequal i j (by simpa using hi) (by simpa using hj) ordered
    apply profile.encode_injective
    simpa using encodedEqual
  have lengthLe := encodedNodup.length_le_card
  have long' : Fintype.card (Fin profile.stateBound) <
      (profile.inspectedStages.map (profile.encode ∘ profile.code)).length := by
    simpa using long
  exact (Nat.not_lt_of_ge lengthLe long').elim

/-- Execute the terminal-or-repeat split.  No ambient state or context
universe is generated: the only inspected list is `stages.take (Q + 1)`. -/
noncomputable def run : profile.Outcome := by
  by_cases short : profile.stages.values.length ≤ profile.stateBound
  · exact .terminal short
  · have fullPrefix : profile.inspectedStages.length = profile.stateBound + 1 := by
      rw [profile.inspectedStages_length, min_eq_left]
      omega
    have long : profile.stateBound < profile.inspectedStages.length := by
      rw [fullPrefix]
      omega
    exact .repeated (Classical.choice (profile.exists_repeated_of_card_lt_length long))

theorem run_total :
    (∃ short, profile.run = .terminal short) ∨
      (∃ repetition, profile.run = .repeated repetition) := by
  cases equation : profile.run with
  | terminal short => exact .inl ⟨short, rfl⟩
  | repeated repetition => exact .inr ⟨repetition, rfl⟩

noncomputable def inspectedChecks : Nat := profile.inspectedStages.length

theorem inspectedChecks_le_bound_add_one :
    profile.inspectedChecks ≤ profile.stateBound + 1 := by
  rw [inspectedChecks, inspectedStages_length]
  exact min_le_left _ _

end Profile

end StructuralExhaustion.Core.FiniteExactStateCorridor
