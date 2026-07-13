import StructuralExhaustion.Graph.EndpointParityCycle

namespace EvenCycleExample

open StructuralExhaustion

universe u

/-!
The problem layer contains only the data that varies between graph problems.
The graph, degree, path, cycle, and deletion notions are all the Mathlib-native
ones exported by `StructuralExhaustion.Graph`.
-/

/-- The branch state remembers the root index required by Mathlib's dependent
path type together with the current rooted path. -/
abbrev PathState {V : Type u} :=
  Graph.EndpointParityCycle.PathState (V := V)

/-- The complete problem-specific API: one threshold and one decidable cycle-
length predicate.  Problem, target, CT1, and deletion-only CT2 are generated
from this record by the graph support layer. -/
abbrev endpointParityProfile (V : Type u) :
    Graph.EndpointParityCycle.Profile V :=
  Graph.EndpointParityCycle.Profile.evenCycle V

abbrev staticInput (V : Type u) := (endpointParityProfile V).base

abbrev problem (V : Type u) : Core.Problem.{u, u} :=
  (staticInput V).problem

abbrev Baseline {V : Type u} (object : Graph.FiniteObject V) : Prop :=
  (staticInput V).problem.Baseline object

abbrev HasEvenCycle {V : Type u} (object : Graph.FiniteObject V) : Prop :=
  (staticInput V).Target object

end EvenCycleExample
