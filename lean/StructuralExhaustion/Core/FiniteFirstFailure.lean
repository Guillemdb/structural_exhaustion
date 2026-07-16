import StructuralExhaustion.Core.FiniteSearch
import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Core.FiniteFirstFailure

open StructuralExhaustion

universe uCorridor uStage uF1 uF2 uF3 uF4 uGerm

/-!
# Ordered local first-failure classification

The runner below scans only the explicit stage list attached to one supplied
corridor.  F1--F4 are checked at each stage in fixed priority order.  If the
whole stage list is clear, the profile constructs the bounded F5 datum from
the exhaustive negative proof.  Thus callers cannot inject a preselected
quiet/F5 outcome.
-/

structure Profile (Corridor : Type uCorridor) (Stage : Type uStage) where
  corridors : FinEnum Corridor
  stages : Corridor → Core.OrderedCollection Stage
  F1 : Corridor → Stage → Prop
  F2 : Corridor → Stage → Prop
  F3 : Corridor → Stage → Prop
  F4 : Corridor → Stage → Prop
  f1Decidable : ∀ corridor stage, Decidable (F1 corridor stage)
  f2Decidable : ∀ corridor stage, Decidable (F2 corridor stage)
  f3Decidable : ∀ corridor stage, Decidable (F3 corridor stage)
  f4Decidable : ∀ corridor stage, Decidable (F4 corridor stage)
  F1Data : Type uF1
  F2Data : Type uF2
  F3Data : Type uF3
  F4Data : Type uF4
  f1Data : ∀ corridor stage, F1 corridor stage → F1Data
  f2Data : ∀ corridor stage, F2 corridor stage → F2Data
  f3Data : ∀ corridor stage, F3 corridor stage → F3Data
  f4Data : ∀ corridor stage, F4 corridor stage → F4Data
  Germ : Corridor → Type uGerm
  germOfClear : ∀ corridor,
    (∀ stage, stage ∈ (stages corridor).values →
      ¬F1 corridor stage ∧ ¬F2 corridor stage ∧
        ¬F3 corridor stage ∧ ¬F4 corridor stage) → Germ corridor

namespace Profile

variable {Corridor : Type uCorridor} {Stage : Type uStage}
variable (profile : Profile Corridor Stage)

def Event (corridor : Corridor) (stage : Stage) : Prop :=
  profile.F1 corridor stage ∨ profile.F2 corridor stage ∨
    profile.F3 corridor stage ∨ profile.F4 corridor stage

def eventDecidable (corridor : Corridor) (stage : Stage) :
    Decidable (profile.Event corridor stage) := by
  exact @instDecidableOr _ _ (profile.f1Decidable corridor stage)
    (@instDecidableOr _ _ (profile.f2Decidable corridor stage)
      (@instDecidableOr _ _ (profile.f3Decidable corridor stage)
        (profile.f4Decidable corridor stage)))

/-- Typed payload of the event at the canonical first failing stage.  The
constructor priority is F1, F2, F3, F4. -/
inductive EventData (corridor : Corridor) (stage : Stage) where
  | f1 (proof : profile.F1 corridor stage) (data : profile.F1Data)
  | f2 (notF1 : ¬profile.F1 corridor stage)
      (proof : profile.F2 corridor stage) (data : profile.F2Data)
  | f3 (notF1 : ¬profile.F1 corridor stage)
      (notF2 : ¬profile.F2 corridor stage)
      (proof : profile.F3 corridor stage) (data : profile.F3Data)
  | f4 (notF1 : ¬profile.F1 corridor stage)
      (notF2 : ¬profile.F2 corridor stage)
      (notF3 : ¬profile.F3 corridor stage)
      (proof : profile.F4 corridor stage) (data : profile.F4Data)

def eventData (corridor : Corridor) (stage : Stage)
    (event : profile.Event corridor stage) : profile.EventData corridor stage := by
  letI : Decidable (profile.F1 corridor stage) :=
    profile.f1Decidable corridor stage
  letI : Decidable (profile.F2 corridor stage) :=
    profile.f2Decidable corridor stage
  letI : Decidable (profile.F3 corridor stage) :=
    profile.f3Decidable corridor stage
  by_cases f1 : profile.F1 corridor stage
  · exact .f1 f1 (profile.f1Data corridor stage f1)
  · by_cases f2 : profile.F2 corridor stage
    · exact .f2 f1 f2 (profile.f2Data corridor stage f2)
    · by_cases f3 : profile.F3 corridor stage
      · exact .f3 f1 f2 f3 (profile.f3Data corridor stage f3)
      · have f4 : profile.F4 corridor stage := by
          rcases event with f1' | f2' | f3' | f4
          · exact (f1 f1').elim
          · exact (f2 f2').elim
          · exact (f3 f3').elim
          · exact f4
        exact .f4 f1 f2 f3 f4 (profile.f4Data corridor stage f4)

inductive Result (corridor : Corridor) where
  | first
      (hit : Core.FiniteSearch.FirstHit
        (profile.stages corridor).values (profile.Event corridor))
      (data : profile.EventData corridor hit.value)
  | germ
      (noEvent : ∀ stage, stage ∈ (profile.stages corridor).values →
        ¬profile.Event corridor stage)
      (data : profile.Germ corridor)

/-- Canonical first failure, or the F5 germ constructed by the runner after
an exhaustive clear scan. -/
def run (corridor : Corridor) : profile.Result corridor :=
  match Core.FiniteSearch.firstOnList (profile.stages corridor).values
      (profile.Event corridor) (profile.eventDecidable corridor) with
  | .found hit => .first hit
      (profile.eventData corridor hit.value hit.holds)
  | .absent absent =>
      let clear : ∀ stage, stage ∈ (profile.stages corridor).values →
          ¬profile.F1 corridor stage ∧ ¬profile.F2 corridor stage ∧
            ¬profile.F3 corridor stage ∧ ¬profile.F4 corridor stage :=
        fun stage member => by
          have noEvent := absent stage member
          exact ⟨fun f1 => noEvent (Or.inl f1),
            fun f2 => noEvent (Or.inr (Or.inl f2)),
            fun f3 => noEvent (Or.inr (Or.inr (Or.inl f3))),
            fun f4 => noEvent (Or.inr (Or.inr (Or.inr f4)))⟩
      .germ absent (profile.germOfClear corridor clear)

theorem run_total (corridor : Corridor) :
    (∃ hit data, profile.run corridor = .first hit data) ∨
      (∃ noEvent data, profile.run corridor = .germ noEvent data) := by
  cases equation : profile.run corridor with
  | first hit data => exact Or.inl ⟨hit, data, rfl⟩
  | germ noEvent data => exact Or.inr ⟨noEvent, data, rfl⟩

/-- The first-event branch retains the exact clean prefix. -/
theorem first_prefix_clear (corridor : Corridor)
    (hit : Core.FiniteSearch.FirstHit
      (profile.stages corridor).values (profile.Event corridor)) :
    ∀ stage, stage ∈ hit.before → ¬profile.Event corridor stage :=
  hit.beforeAbsent

/-- The runner checks one local event predicate per declared stage. -/
def checks (corridor : Corridor) : Nat :=
  (profile.stages corridor).values.length

end Profile

end StructuralExhaustion.Core.FiniteFirstFailure
