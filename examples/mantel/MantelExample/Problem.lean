import StructuralExhaustion.Graph.Mantel

namespace MantelExample

open StructuralExhaustion

universe u

/-- Public Mantel target for an explicitly finite Mathlib graph. -/
abbrev Target {V : Type u} (object : Graph.FiniteObject V) : Prop :=
  object.edgeCount ≤ object.input.vertices.card ^ 2 / 4

end MantelExample
