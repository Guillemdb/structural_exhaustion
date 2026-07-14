import StructuralExhaustion.Graph.SurplusPortActivity

namespace StructuralExhaustion.Graph.SurplusResidualBudget

universe u

/-!
# Residual-center surplus budgets

Residual high-center families are charged to the literal `degree - 3` slot
universe already used by CT6. Restricting that universe by a semantic center
predicate is proof-level: this module never scans or materializes a table.
-/

/-- Exact surplus slots whose center satisfies a declared residual predicate. -/
abbrev RestrictedSlot {V : Type u} (object : FiniteObject V)
    (Residual : V → Prop) :=
  {slot : SurplusPortActivity.ExcessPortSlot object // Residual slot.1}

/-- Restricted surplus slots inject into the complete CT6 slot universe. -/
theorem restrictedSlot_card_le {V : Type u} (object : FiniteObject V)
    (Residual : V → Prop) [DecidablePred Residual] :
    letI : FinEnum V := object.input.vertices
    Fintype.card (RestrictedSlot object Residual) ≤
      Fintype.card (SurplusPortActivity.ExcessPortSlot object) := by
  letI : FinEnum V := object.input.vertices
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

/-- Multiplying by a fixed local envelope constant preserves the literal
surplus-slot domination. -/
theorem weighted_restrictedSlot_card_le {V : Type u}
    (object : FiniteObject V) (Residual : V → Prop)
    [DecidablePred Residual] (weight : Nat) :
    letI : FinEnum V := object.input.vertices
    weight * Fintype.card (RestrictedSlot object Residual) ≤
      weight * Fintype.card (SurplusPortActivity.ExcessPortSlot object) := by
  letI : FinEnum V := object.input.vertices
  exact Nat.mul_le_mul_left weight (restrictedSlot_card_le object Residual)

end StructuralExhaustion.Graph.SurplusResidualBudget
