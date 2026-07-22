import Hypostructure.Core.Residual.Decision

namespace Hypostructure.Core.Degradation

universe uSource uClosed uResidual

/-! Generic guarded degradation.  A predecessor-owned guard either closes the
branch through the supplied closure proof or retains the exact failed guard
as a residual.  No successor payload or transport data is accepted here. -/

inductive Outcome (Source : Type uSource) (Closed : Source -> Type uClosed)
    (Residual : Source -> Type uResidual)
    (guard : (source : Source) -> Prop) where
  | closed (source : Source) (proof : guard source)
      (value : Closed source) : Outcome Source Closed Residual guard
  | residual (source : Source) (proof : ¬ guard source)
      (value : Residual source) : Outcome Source Closed Residual guard

def execute {Source : Type uSource} {Closed : Source -> Type uClosed}
    {Residual : Source -> Type uResidual} {guard : (source : Source) -> Prop}
    (decideGuard : ∀ source, Decidable (guard source))
    (close : ∀ source, guard source -> Closed source)
    (retain : ∀ source, ¬ guard source -> Residual source) (source : Source) :
    Outcome Source Closed Residual guard :=
  match decideGuard source with
  | .isTrue proof => .closed source proof (close source proof)
  | .isFalse proof => .residual source proof (retain source proof)

theorem exhaustive {Source : Type uSource} {Closed : Source -> Type uClosed}
    {Residual : Source -> Type uResidual} {guard : (source : Source) -> Prop}
    (outcome : Outcome Source Closed Residual guard) :
    (∃ source proof value, outcome = .closed source proof value) ∨
      (∃ source proof value, outcome = .residual source proof value) := by
  cases outcome with
  | closed source proof value => exact Or.inl ⟨source, proof, value, rfl⟩
  | residual source proof value => exact Or.inr ⟨source, proof, value, rfl⟩

end Hypostructure.Core.Degradation
