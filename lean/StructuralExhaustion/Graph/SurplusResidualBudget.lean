import StructuralExhaustion.Graph.SurplusPortActivity

namespace StructuralExhaustion.Graph.SurplusResidualBudget

universe u

/-!
# Residual-center surplus budgets

Residual high-center families are charged to the literal `degree - 3` slot
universe already used by CT6. Restricting that universe by a semantic center
predicate is proof-level: this module never scans or materializes a table.
-/

/-- The first literal surplus slot at a supplied high center.  This is a
semantic bridge from an already found local high occurrence; it performs no
vertex or graph search. -/
def canonicalSlotOfHigh {V : Type u} (object : FiniteObject V)
    (center : V) (high : 4 ≤ object.degree center) :
    SurplusPortActivity.ExcessPortSlot object :=
  ⟨center, ⟨0, by omega⟩⟩

@[simp]
theorem canonicalSlotOfHigh_center {V : Type u} (object : FiniteObject V)
    (center : V) (high : 4 ≤ object.degree center) :
    (canonicalSlotOfHigh object center high).1 = center := rfl

/-- Exact surplus slots whose center satisfies a declared residual predicate. -/
abbrev RestrictedSlot {V : Type u} (object : FiniteObject V)
    (Residual : V → Prop) :=
  {slot : SurplusPortActivity.ExcessPortSlot object // Residual slot.1}

/-- A supplied high center satisfying the residual predicate gives a literal
member of the corresponding restricted surplus-slot ledger. -/
def restrictedSlotOfHigh {V : Type u} (object : FiniteObject V)
    (Residual : V → Prop) (center : V) (high : 4 ≤ object.degree center)
    (residual : Residual center) : RestrictedSlot object Residual :=
  ⟨canonicalSlotOfHigh object center high, residual⟩

@[simp]
theorem restrictedSlotOfHigh_center {V : Type u} (object : FiniteObject V)
    (Residual : V → Prop) (center : V) (high : 4 ≤ object.degree center)
    (residual : Residual center) :
    (restrictedSlotOfHigh object Residual center high residual).1.1 = center := rfl

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
