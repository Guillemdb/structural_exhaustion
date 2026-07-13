import StructuralExhaustion.Core.Problem

namespace StructuralExhaustion.CT1

universe uI uW

/-- Mathematical target-test vocabulary.  It contains no search procedure,
downstream tactic, or completed node decision. -/
structure Spec (P : Core.Problem) where
  TestIndex : Type uI
  Witness : P.Ambient → TestIndex → Type uW
  Realizes :
    (G : P.Ambient) →
    (index : TestIndex) →
    Witness G index → Prop

/-- The canonical CT1 target.  Defining the target from its realization
semantics makes target-test equivalence a framework theorem by reflexivity. -/
def Target {P : Core.Problem} (S : Spec P) (G : P.Ambient) : Prop :=
  ∃ index, ∃ witness, S.Realizes G index witness

theorem target_iff_realization {P : Core.Problem} (S : Spec P)
    (G : P.Ambient) :
    Target S G ↔ ∃ index, ∃ witness, S.Realizes G index witness :=
  Iff.rfl

/-- Optional, reusable bridge from a public mathematical target to CT1's
canonical realization target.  It is instance-level semantic data rather than
an invocation-specific node result or routing witness. -/
structure TargetBridge {P : Core.Problem} (S : Spec P)
    (PublicTarget : P.Ambient → Prop) : Prop where
  equivalent : ∀ G, PublicTarget G ↔ Target S G

end StructuralExhaustion.CT1
