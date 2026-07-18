import StructuralExhaustion.Graph.CertifiedResidualSupportLedger

namespace StructuralExhaustion.Examples.CertifiedResidualLedger

open StructuralExhaustion

inductive Input
  | first
  | second
  deriving DecidableEq

inductive Event
  | shared
  deriving DecidableEq

def Valid : Event → Prop
  | .shared => True

noncomputable def firstInput : Core.FiniteResidualLedger.Ledger Input :=
  .singleton .first

noncomputable def secondInput : Core.FiniteResidualLedger.Ledger Input :=
  .singleton .second

noncomputable def inputs : Core.FiniteResidualLedger.Ledger Input :=
  firstInput.append secondInput

noncomputable def producer :
    Core.CertifiedResidualLedger.Ledger.Producer
      (Event := Event) (Valid := Valid) Input where
  emit := fun _ => .shared
  certified := fun _ => trivial

noncomputable def produced :=
  Core.CertifiedResidualLedger.Ledger.produce inputs producer

theorem equal_events_keep_distinct_producer_occurrences :
    produced.residuals.Occurrence = Sum PUnit PUnit :=
  rfl

theorem both_occurrences_certified
    (occurrence : produced.residuals.Occurrence) :
    Valid (produced.residuals.event occurrence) :=
  produced.certified occurrence

noncomputable def adapter :
    Core.CertifiedResidualLedger.Ledger.SemanticAdapter
      (Event := Event) (Valid := Valid) where
  Seed := fun _ => Unit
  adapt := fun _ _ => ()

theorem routed_seed_exact (occurrence : produced.residuals.Occurrence) :
    (produced.routeSeeds adapter).value occurrence = () :=
  rfl

noncomputable def supportProfile :
    Graph.CertifiedResidualSupportLedger.Profile
      (Event := Event) (Fin 2) where
  vertexDecEq := inferInstance
  support := fun _ => {0}

#print axioms equal_events_keep_distinct_producer_occurrences
#print axioms both_occurrences_certified
#print axioms routed_seed_exact
#print axioms Graph.CertifiedResidualSupportLedger.Profile.recognize_exact

end StructuralExhaustion.Examples.CertifiedResidualLedger
