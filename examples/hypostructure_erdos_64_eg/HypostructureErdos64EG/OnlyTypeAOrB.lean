import HypostructureErdos64EG.Node63
import HypostructureErdos64EG.Node164

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-! The paper's Type-A/Type-B checkpoint is the public destructor for the
framework-owned Node 62 decision.  It introduces no new routing or problem
data: the literal predecessor and its branch proof are already carried by the
Core ledger extension. -/

theorem only_type_A_or_B
    {Previous : Type u} (contract : Node62Contract Previous)
    (stage : Node62Stage contract) :
    (∃ (previous : Previous),
      ∃ (high : Node62HighSurplus contract previous),
        stage = Core.Residual.Ledger.extend previous
          (Core.Residual.Decision.Binary.yesBranch high)) ∨
    (∃ (previous : Previous),
      ∃ (noHigh : Node62NoHighSurplus contract previous),
        stage = Core.Residual.Ledger.extend previous
          (Core.Residual.Decision.Binary.noBranch noHigh)) := by
  cases stage with
  | _ previous added =>
      cases added with
      | yesBranch high =>
          exact Or.inl ⟨previous, high, rfl⟩
      | noBranch noHigh =>
          exact Or.inr ⟨previous, noHigh, rfl⟩

end HypostructureErdos64EG
