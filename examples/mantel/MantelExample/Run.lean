import MantelExample.Problem

namespace MantelExample

open StructuralExhaustion

universe u

/-- Mantel's theorem.  The problem package supplies only triangle-freeness;
all finite summation, localization, and contradiction steps are reusable
framework code. -/
theorem mantel {V : Type u} (object : Graph.FiniteObject V)
    (triangleFree : object.graph.CliqueFree 3) : Target object :=
  Graph.Mantel.edgeCount_le_card_sq_div_four_of_triangleFree object triangleFree

/-- Expose the exact CT11 execution used when the numerical target is
negated.  This is useful for executable fixtures and trace auditing. -/
abbrev ct11Run {V : Type u} (object : Graph.FiniteObject V)
    (violation : object.input.vertices.card ^ 2 < 4 * object.edgeCount) :=
  Graph.Mantel.run object violation

end MantelExample
