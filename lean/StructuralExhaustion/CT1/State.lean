import StructuralExhaustion.CT1.Capability
import StructuralExhaustion.Core.Context

namespace StructuralExhaustion.CT1

/-- CT1 receives only the shared branch context. -/
structure Input (P : Core.Problem) where
  context : Core.BranchContext P

/-- Framework-produced certification of the definitional target semantics. -/
structure EquivalenceState {P : Core.Problem} (S : Spec P)
    (input : Input P) : Prop where
  targetIff :
    Target S input.context.G ↔
      ∃ index, ∃ witness,
        S.Realizes input.context.G index witness

def certifyEquivalence {P : Core.Problem} (S : Spec P)
    (input : Input P) : EquivalenceState S input where
  targetIff := Iff.rfl

/-- Provenance-indexed C1 evidence. -/
structure C1Certificate {P : Core.Problem} (S : Spec P)
    (input : Input P) (equivalence : EquivalenceState S input) where
  index : S.TestIndex
  witness : S.Witness input.context.G index
  realizes : S.Realizes input.context.G index witness

namespace C1Certificate

theorem target {P : Core.Problem} {S : Spec P} {input : Input P}
    {equivalence : EquivalenceState S input}
    (certificate : C1Certificate S input equivalence) :
    Target S input.context.G :=
  ⟨certificate.index, certificate.witness, certificate.realizes⟩

end C1Certificate

/-- Exact negative realization state.  The inherited branch context remains a
dependent index and is therefore not duplicated in this residual. -/
structure AvoidingState {P : Core.Problem} (S : Spec P)
    (input : Input P) (equivalence : EquivalenceState S input) where
  noRealization :
    ∀ index witness,
      ¬ S.Realizes input.context.G index witness

namespace AvoidingState

def ofNoRealization {P : Core.Problem} {S : Spec P} {input : Input P}
    (equivalence : EquivalenceState S input)
    (noRealization :
      ∀ index witness,
        ¬ S.Realizes input.context.G index witness) :
    AvoidingState S input equivalence where
  noRealization := noRealization

theorem targetAvoiding {P : Core.Problem} {S : Spec P} {input : Input P}
    {equivalence : EquivalenceState S input}
    (state : AvoidingState S input equivalence) :
    ¬ Target S input.context.G := by
  intro target
  rcases target with ⟨index, witness, realizes⟩
  exact state.noRealization index witness realizes

/-- Recover the shared target-avoiding context definitionally from the input
index and the framework-derived absence proof. -/
def toAvoidingContext {P : Core.Problem} {S : Spec P} {input : Input P}
    {equivalence : EquivalenceState S input}
    (state : AvoidingState S input equivalence) :
    Core.AvoidingContext P (Target S) :=
  Core.AvoidingContext.ofBranch input.context state.targetAvoiding

end AvoidingState

end StructuralExhaustion.CT1
