import GreedyColoringExample.Problem

namespace GreedyColoringExample

open StructuralExhaustion

universe u

/-- Every explicitly finite Mathlib simple graph is colorable with one more
color than its maximum degree.  The external package supplies no proof
obligation beyond the graph's machine input. -/
theorem maxDegreeSucc_colorable {V : Type u}
    (object : Graph.FiniteObject V) : Target object :=
  Graph.GreedyColoring.colorable_maxDegree_succ object

/-- Exact CT12 run certifying the canonical vertex-peeling schedule. -/
abbrev ct12Run {V : Type u} (object : Graph.FiniteObject V) :=
  Graph.GreedyColoring.peelingRun object

/-- Exact CT1 run validating the final Mathlib coloring certificate. -/
abbrev ct1Run {V : Type u} (object : Graph.FiniteObject V) :=
  Graph.GreedyColoring.ct1Run object

end GreedyColoringExample
