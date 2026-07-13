import StructuralExhaustion.Graph.GreedyColoring

namespace GreedyColoringExample

open StructuralExhaustion

universe u

/-- Public target, stated directly with Mathlib's coloring API. -/
abbrev Target {V : Type u} (object : Graph.FiniteObject V) : Prop :=
  object.graph.Colorable (object.maxDegree + 1)

/-- The framework-generated deterministic coloring certificate. -/
abbrev coloring {V : Type u} (object : Graph.FiniteObject V) :=
  Graph.GreedyColoring.maxDegreeColoring object

end GreedyColoringExample
