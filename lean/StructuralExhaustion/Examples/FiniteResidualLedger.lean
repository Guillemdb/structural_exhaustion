import StructuralExhaustion.Graph.FiniteResidualSupportLedger

namespace StructuralExhaustion.Examples.FiniteResidualLedger

open StructuralExhaustion

inductive Event
  | residual
  deriving DecidableEq

noncomputable def first :=
  Core.FiniteResidualLedger.Ledger.singleton Event.residual

noncomputable def second :=
  Core.FiniteResidualLedger.Ledger.singleton Event.residual

noncomputable def combined := first.append second

theorem equal_events_keep_distinct_occurrences
    (left : first.Occurrence) (right : second.Occurrence) :
    (Sum.inl left : combined.Occurrence) ≠ Sum.inr right := by
  simp

theorem combined_event_left (occurrence : first.Occurrence) :
    combined.event (.inl occurrence) = Event.residual :=
  rfl

theorem combined_event_right (occurrence : second.Occurrence) :
    combined.event (.inr occurrence) = Event.residual :=
  rfl

noncomputable def firstPayload :
    Core.FiniteResidualLedger.Ledger.View first where
  Payload := fun _ => Nat
  value := fun _ => 11

noncomputable def secondPayload :
    Core.FiniteResidualLedger.Ledger.View second where
  Payload := fun _ => Nat
  value := fun _ => 29

noncomputable def combinedPayload := firstPayload.append secondPayload

theorem dependent_view_left_exact (occurrence : first.Occurrence) :
    combinedPayload.value (.inl occurrence) =
      firstPayload.value occurrence :=
  rfl

theorem dependent_view_right_exact (occurrence : second.Occurrence) :
    combinedPayload.value (.inr occurrence) =
      secondPayload.value occurrence :=
  rfl

def keepLeft : combined.Occurrence → Prop
  | .inl _ => True
  | .inr _ => False

noncomputable def keepLeftDecidable :
    ∀ occurrence, Decidable (keepLeft occurrence) := fun occurrence => by
  cases occurrence with
  | inl _ => exact isTrue trivial
  | inr _ => exact isFalse (fun impossible => impossible)

noncomputable def restricted :=
  combined.restrict keepLeft keepLeftDecidable

theorem restricted_event_exact (occurrence : restricted.Occurrence) :
    restricted.event occurrence = combined.event occurrence.1 :=
  rfl

noncomputable def firstSupport :
    Graph.FiniteResidualSupportLedger.View first (Fin 4) where
  vertexDecEq := inferInstance
  support := fun _ => {0}

noncomputable def secondSupport :
    Graph.FiniteResidualSupportLedger.View second (Fin 4) where
  vertexDecEq := inferInstance
  support := fun _ => {1}

noncomputable def combinedSupport := firstSupport.append secondSupport

theorem left_support_exact (occurrence : first.Occurrence) :
    combinedSupport.support (.inl occurrence) = {0} :=
  rfl

theorem right_support_exact (occurrence : second.Occurrence) :
    combinedSupport.support (.inr occurrence) = {1} :=
  rfl

theorem exact_two_checks : combinedSupport.checks = 2 := by
  change (firstSupport.append secondSupport).checks = 2
  rw [Graph.FiniteResidualSupportLedger.View.append_checks]
  change (1 : Nat) + 1 = 2
  rfl

theorem recognition_retains_occurrence_and_event (vertex : Fin 4) :
    match combinedSupport.recognize vertex with
    | .found hit =>
        hit.event = (first.append second).event hit.occurrence ∧
        hit.occurrence ∈ (first.append second).entries ∧
        vertex ∈ combinedSupport.support hit.occurrence ∧
        ∀ earlier ∈ hit.before,
          vertex ∉ combinedSupport.support earlier
    | .absent _ =>
        ∀ occurrence : (first.append second).Occurrence,
          vertex ∉ combinedSupport.support occurrence :=
  by
    cases result : combinedSupport.recognize vertex with
    | found hit =>
        exact ⟨hit.eventExact, hit.occurrence_mem combinedSupport vertex,
          hit.vertexMember, hit.beforeAbsent⟩
    | absent absentProof => exact absentProof

#print axioms equal_events_keep_distinct_occurrences
#print axioms exact_two_checks
#print axioms recognition_retains_occurrence_and_event
#print axioms Core.FiniteResidualLedger.Ledger.append_checks
#print axioms Graph.FiniteResidualSupportLedger.View.recognize_exact

end StructuralExhaustion.Examples.FiniteResidualLedger
