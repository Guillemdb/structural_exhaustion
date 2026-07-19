import StructuralExhaustion.Core.ExactHandoff

namespace StructuralExhaustion.Examples.ExactHandoff

open StructuralExhaustion

def incoming : Nat := 7

def retained : Core.ExactHandoff incoming := Core.ExactHandoff.refl incoming

example : retained.previous = incoming := retained.previous_eq

example : retained.previous + 1 = 8 :=
  retained.property (fun value => value + 1 = 8) (by decide)

def boundedProperty : Core.ExactPropertyHandoff incoming (fun value => value < 10) :=
  Core.ExactPropertyHandoff.refl incoming (by decide)

example : incoming < 10 :=
  boundedProperty.certificateAtExpected

def dependentStage (value : Nat) := Fin (value + 1)

def staged : Core.ExactStageHandoff incoming dependentStage :=
  Core.ExactStageHandoff.refl incoming ⟨0, by decide⟩

example : (staged.stageAtExpected : Fin (incoming + 1)).1 = 0 := rfl

def dependentProducer (value : Nat) : dependentStage value :=
  ⟨value, Nat.lt_succ_self value⟩

theorem transported_dependent_producer_is_exact :
    Core.ExactStageHandoff.transportProducer
      (previous := incoming) (expected := incoming) rfl dependentProducer =
        dependentProducer incoming := by
  simp

def mappedDependent : Core.ExactHandoff (dependentProducer incoming) :=
  retained.mapDependent dependentProducer

theorem mapped_dependent_output_is_exact :
    mappedDependent.output = dependentProducer incoming := by
  simp [mappedDependent]

def renamedMappedDependent :
    Core.ExactHandoff (dependentProducer incoming) :=
  mappedDependent.castExpected rfl

theorem renamed_mapped_dependent_output_is_exact :
    renamedMappedDependent.output = dependentProducer incoming := by
  simp [renamedMappedDependent]

def Guard (value : Nat) : Prop := value ≤ 10
def Previous (value : Nat) : Prop := value = incoming
def Next (value : Nat) : Prop := value + 1 = 8

example : ∃ value, Guard value ∧ Next value :=
  Core.ExactHandoff.exists_and_map
    (guard := Guard) (previous := Previous)
    (next := Next) ⟨incoming, by simp [Guard, incoming], rfl⟩
    (fun value equal => by
      simpa [Previous, Next, incoming] using equal)

#print axioms transported_dependent_producer_is_exact
#print axioms mapped_dependent_output_is_exact
#print axioms renamed_mapped_dependent_output_is_exact

end StructuralExhaustion.Examples.ExactHandoff
