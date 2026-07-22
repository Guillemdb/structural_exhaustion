import Hypostructure.Graph.InducedPath
import Hypostructure.Graph.Target

/-!
# Hegde--Sandeep--Shashank external theorem (migrated declaration)

This declaration mirrors the external theorem used in the legacy Erdős--Gyárfás
migration proof.  It is intentionally left as a trusted axiom in this package.
-/

namespace Hypostructure.Graph.External.HegdeSandeepShashank

open Hypostructure.Graph

universe u

/-- Every finite induced-`P₁₃`-free graph of minimum degree at least three
contains a cycle whose length is a power of two. -/
axiom p13Free_hasPowerOfTwoCycle
    (object : FiniteObject.{u})
    [Fintype object.Vertex] [DecidableRel object.graph.Adj]
    (minimumDegreeThree : 3 ≤ object.minDegree)
    (p13Free : InducedPathFree object 13) :
    HasCycleWithLength (fun length =>
      ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent)
      object

/-- Finite-object form of the external theorem, using exactly the object's
packed finite instances. -/
theorem finiteObject_p13Free_hasPowerOfTwoCycle
    (object : FiniteObject.{u})
    (minimumDegreeThree : 3 ≤ object.minDegree)
    (p13Free : InducedPathFree object 13) :
    HasCycleWithLength (fun length =>
      ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent)
      object := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  apply p13Free_hasPowerOfTwoCycle object
  · simpa only [FiniteObject.minDegree] using minimumDegreeThree
  · exact p13Free

end Hypostructure.Graph.External.HegdeSandeepShashank
