import StructuralExhaustion.Graph.ResidualSupportRefinement

namespace StructuralExhaustion.Examples.ResidualSupportRefinement

open StructuralExhaustion

structure Event where
  label : Nat
  labelPositive : 0 < label
  support : Finset Nat
  supportNonempty : support.Nonempty

def Produced (event : Event) : Prop :=
  0 < event.label

def HasSupport (event : Event) : Prop :=
  event.support.Nonempty

noncomputable def first : Event :=
  ⟨1, by omega, {2, 3}, by simp⟩

noncomputable def second : Event :=
  ⟨2, by omega, {3, 4}, by simp⟩

noncomputable def schedule : Core.FiniteResidualLedger.Ledger Event :=
  (Core.FiniteResidualLedger.Ledger.singleton first).append
    (Core.FiniteResidualLedger.Ledger.singleton second)

noncomputable def producer :
    Core.ResidualRefinement.Ledger.Producer Event Produced where
  emit := id
  prove := fun event => event.labelPositive

noncomputable def produced :=
  Core.ResidualRefinement.Ledger.produce schedule producer

noncomputable def supportNode :
    Core.ResidualRefinement.State.Node
      (facts := [Produced]) HasSupport where
  prove := fun state => state.residual.supportNonempty

noncomputable def refined := produced.refine supportNode

noncomputable def profile :
    Graph.ResidualSupportRefinement.Profile (Event := Event) Nat where
  vertexDecEq := inferInstance
  support := Event.support

noncomputable def bareView := profile.viewSchedule schedule

noncomputable def emitted : Bool → Event
  | false => first
  | true => second

noncomputable def mappedSchedule :=
  Core.FiniteResidualLedger.Ledger.ofMappedEnumeration
    Core.Enumeration.bool emitted

example : mappedSchedule.entries = [false, true] := by
  change Core.Enumeration.bool.orderedValues = [false, true]
  rfl

theorem mapped_emission_is_exact (input : Bool) :
    mappedSchedule.event input = emitted input ∧
      input ∈ mappedSchedule.entries :=
  ⟨rfl, mappedSchedule.occurrence_mem input⟩

theorem bare_schedule_occurrence_is_retained
    (occurrence : schedule.Occurrence) :
    occurrence ∈ schedule.entries :=
  schedule.occurrence_mem occurrence

example (occurrence : schedule.Occurrence) :
    bareView.support occurrence = (schedule.event occurrence).support :=
  rfl

/-- A graph hit automatically retains both earlier mathematical facts; the
application does not re-prove producer provenance after support recognition. -/
theorem hit_retains_all_facts {vertex : Nat}
    (hit : Graph.ResidualSupportRefinement.Profile.FirstHit
      profile refined vertex) :
    HasSupport hit.state.residual ∧ Produced hit.state.residual ∧
      vertex ∈ hit.state.residual.support := by
  exact ⟨hit.require, hit.require, hit.contains⟩

theorem occurrence_retains_producer_fact
    (occurrence : refined.residuals.Occurrence) :
    Produced (refined.residuals.event occurrence) :=
  refined.require occurrence

#print axioms hit_retains_all_facts
#print axioms occurrence_retains_producer_fact
#print axioms bare_schedule_occurrence_is_retained
#print axioms mapped_emission_is_exact

end StructuralExhaustion.Examples.ResidualSupportRefinement
