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

/-- A graph hit automatically retains both earlier mathematical facts; the
application does not re-prove producer provenance after support recognition. -/
theorem hit_retains_all_facts {vertex : Nat}
    (hit : Graph.ResidualSupportRefinement.Profile.FirstHit
      profile refined vertex) :
    HasSupport hit.state.residual ∧ Produced hit.state.residual ∧
      vertex ∈ hit.state.residual.support := by
  exact ⟨hit.get .here, hit.get (.there .here), hit.contains⟩

theorem compatibility_entry_retains_producer_fact
    {event : Event} (member : event ∈ (profile.materialize refined).entries) :
    Produced event := by
  exact refined.fact_of_mem_events (.there .here) member

#print axioms hit_retains_all_facts
#print axioms compatibility_entry_retains_producer_fact

end StructuralExhaustion.Examples.ResidualSupportRefinement
