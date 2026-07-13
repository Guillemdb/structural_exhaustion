import StructuralExhaustion.CT1.State

namespace StructuralExhaustion.CT1

/-- Proof-carrying result of CT1's generic dependent finite search. -/
inductive RealizationDecision {P : Core.Problem} (S : Spec P)
    (input : Input P) (equivalence : EquivalenceState S input) where
  | hit (certificate : C1Certificate S input equivalence)
  | avoiding (state : AvoidingState S input equivalence)

/-- Execute the reference nested search over tests and their dependent witness
fibres.  Both branches are complete because the enumerators carry coverage
proofs. -/
def findRealization {P : Core.Problem} (S : Spec P)
    (capability : Capability S)
    (input : Input P) (equivalence : EquivalenceState S input) :
    RealizationDecision S input equivalence :=
  match Core.FiniteSearch.dependentSearch
      {
        indices := capability.tests
        fibres := capability.witnesses input.context.G
      }
      (S.Realizes input.context.G)
      (capability.realizesDecidable input.context.G) with
  | .found index witness realizes =>
      .hit {
        index := index
        witness := witness
        realizes := realizes
      }
  | .absent noRealization =>
      .avoiding (AvoidingState.ofNoRealization equivalence noRealization)

/-- The canonical target is decidable whenever CT1's executable operations
are available. -/
def targetDecidable {P : Core.Problem} (S : Spec P)
    (capability : Capability S)
    (G : P.Ambient) : Decidable (Target S G) :=
  match Core.FiniteSearch.dependentSearch
      {
        indices := capability.tests
        fibres := capability.witnesses G
      }
      (S.Realizes G)
      (capability.realizesDecidable G) with
  | .found index witness realizes =>
      .isTrue ⟨index, witness, realizes⟩
  | .absent noRealization =>
      .isFalse (by
        intro target
        rcases target with ⟨index, witness, realizes⟩
        exact noRealization index witness realizes)

end StructuralExhaustion.CT1
