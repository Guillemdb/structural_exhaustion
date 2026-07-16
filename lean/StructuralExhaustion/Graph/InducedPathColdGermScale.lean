import StructuralExhaustion.Graph.InducedPathColdCorridor

namespace StructuralExhaustion.Graph.InducedPathColdGermScale

open StructuralExhaustion
open InducedPathColdCorridor
open InducedPathWindowLedger

universe u

variable {V : Type u} {object : FiniteObject V}

/-!
# Exact short/long promotion boundary for a cold corridor germ

The short branch retains a literal bounded path with its two endpoints as the
same interface.  It deliberately does not claim that a smaller replacement or
target-response theorem has already been found.  The long branch retains the
strict scale inequality and the canonical finite support positions required
by an arithmetic consumer such as CT17.
-/

variable (producer : Producer object) (LengthOK : Nat → Prop)
variable (stub : CubicStub object)
variable (germ : Producer.ColdStructuralGerm producer LengthOK stub)

/-- Exact two-terminal bounded source residual.  The corridor itself is the
source piece; any later CT3 promotion must construct a distinct candidate and
prove response reflection rather than asking the caller for them. -/
structure BoundedSameInterfaceResidual (scale : Nat) where
  retainedGerm : {candidate :
    Producer.ColdStructuralGerm producer LengthOK stub // candidate = germ}
  bounded : (producer.ambientReturn stub).support.length ≤ scale

namespace BoundedSameInterfaceResidual

abbrev left {scale : Nat}
    (_residual : BoundedSameInterfaceResidual producer LengthOK stub germ scale) : V :=
  stub.neighbor

noncomputable abbrev right {scale : Nat}
    (_residual : BoundedSameInterfaceResidual producer LengthOK stub germ scale) : V :=
  selectedWindow object stub.window stub.position

noncomputable abbrev source {scale : Nat}
    (_residual : BoundedSameInterfaceResidual producer LengthOK stub germ scale) :
    object.graph.Walk stub.neighbor
      (selectedWindow object stub.window stub.position) :=
  producer.ambientReturn stub

theorem source_isPath {scale : Nat}
    (_residual : BoundedSameInterfaceResidual producer LengthOK stub germ scale) :
    (producer.ambientReturn stub).IsPath :=
  producer.ambientReturn_isPath stub

theorem source_support_bounded {scale : Nat}
    (residual : BoundedSameInterfaceResidual producer LengthOK stub germ scale) :
    (producer.ambientReturn stub).support.length ≤ scale :=
  residual.bounded

end BoundedSameInterfaceResidual

/-- Exact long-support residual and its canonical finite position universe. -/
structure LongSupportResidual (scale : Nat) where
  retainedGerm : {candidate :
    Producer.ColdStructuralGerm producer LengthOK stub // candidate = germ}
  exceeds : scale < (producer.ambientReturn stub).support.length

namespace LongSupportResidual

abbrev Position {scale : Nat}
    (_residual : LongSupportResidual producer LengthOK stub germ scale) :=
  Fin (producer.ambientReturn stub).support.length

@[implicit_reducible]
noncomputable def positions {scale : Nat}
    (_residual : LongSupportResidual producer LengthOK stub germ scale) :
    FinEnum (Fin (producer.ambientReturn stub).support.length) :=
  inferInstance

@[simp]
theorem positions_card {scale : Nat}
    (residual : LongSupportResidual producer LengthOK stub germ scale) :
    (residual.positions).card =
      (producer.ambientReturn stub).support.length := by
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_fin]

end LongSupportResidual

/-- Typed exhaustive scale result. -/
inductive Routed (scale : Nat) where
  | short (residual :
      BoundedSameInterfaceResidual producer LengthOK stub germ scale)
  | long (residual : LongSupportResidual producer LengthOK stub germ scale)

/-- Execute the graph-owned arithmetic comparison. -/
noncomputable def route (scale : Nat) :
    Routed producer LengthOK stub germ scale :=
  match producer.classifyScale LengthOK stub germ scale with
  | .short bounded => .short ⟨⟨germ, rfl⟩, bounded⟩
  | .long exceeds => .long ⟨⟨germ, rfl⟩, exceeds⟩

theorem route_exhaustive (scale : Nat) :
    (∃ residual, route producer LengthOK stub germ scale = .short residual) ∨
    (∃ residual, route producer LengthOK stub germ scale = .long residual) := by
  cases equation : route producer LengthOK stub germ scale with
  | short residual => exact Or.inl ⟨residual, rfl⟩
  | long residual => exact Or.inr ⟨residual, rfl⟩

end StructuralExhaustion.Graph.InducedPathColdGermScale
