import StructuralExhaustion.Graph.Cycle
import StructuralExhaustion.Graph.InducedPath
import StructuralExhaustion.Graph.InducedSubgraph

namespace StructuralExhaustion.Graph.External.HegdeSandeepShashank

open StructuralExhaustion.Graph

universe u

/-!
# Hegde--Sandeep--Shashank external theorem

This module is the repository's sole trusted external graph-theorem import.
It records exactly the statement used by manuscript node `[16]`:

A. S. Hegde, R. B. Sandeep, and P. Shashank,
*Erdős--Gyárfás conjecture on graphs without long induced paths*,
arXiv:2410.22842v2 (2025), Theorem 1 (cited as Theorem 3 in the manuscript).

The theorem is isolated here so every downstream use has explicit provenance.
No CT capability or application is allowed to introduce another external
closure assumption.
-/

/-- Every finite induced-`P₁₃`-free graph of minimum degree at least three
contains a cycle whose length is a power of two. -/
axiom p13Free_hasPowerOfTwoCycle
    {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj]
    (minimumDegreeThree : 3 ≤ G.minDegree)
    (p13Free : InducedPathFree G 13) :
    HasCycleWithLength G (fun length =>
      ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent)

/-- Finite-object form of the external theorem, using exactly the object's
declared finite instances. -/
theorem finiteObject_p13Free_hasPowerOfTwoCycle
    {V : Type u} (object : FiniteObject V)
    (minimumDegreeThree : 3 ≤ object.minDegree)
    (p13Free : InducedPathFree object.graph 13) :
    HasCycleWithLength object.graph (fun length =>
      ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent) := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  apply p13Free_hasPowerOfTwoCycle object.graph
  · simpa only [FiniteObject.minDegree] using minimumDegreeThree
  · exact p13Free

/-- A finite `P₁₃`-free graph avoiding power-of-two cycles has no internal
minimum-degree-three core.  This is the reusable hereditary consequence of
the external theorem; all subgraph construction and cycle transport are
proved in the framework. -/
theorem internalMinDegreeThree_free_of_p13Free
    {V : Type u} (object : FiniteObject V)
    (p13Free : InducedPathFree object.graph 13)
    (avoidsPowerCycle :
      ¬HasCycleWithLength object.graph (fun length =>
        ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent)) :
    object.InternalMinDegreeFree 3 := by
  intro internalCore
  rcases internalCore with ⟨vertices, minimumDegreeThree⟩
  let core := object.induceFinset vertices
  have coreP13Free : InducedPathFree core.graph 13 := by
    intro realization
    rcases realization with ⟨window⟩
    exact p13Free
      ⟨(object.induceFinsetEmbedding vertices).comp window⟩
  have coreCycle := finiteObject_p13Free_hasPowerOfTwoCycle core
    minimumDegreeThree coreP13Free
  exact avoidsPowerCycle
    (hasCycleWithLength_mapHom
      (object.induceFinsetEmbedding vertices).toHom
      (object.induceFinsetEmbedding vertices).injective coreCycle)

/-- Exact arbitrary-subgraph form of the hereditary HSS consequence.  Every
ordinary finite internal subgraph of minimum degree at least three would
force the induced graph on the same support to have minimum degree at least
three, and hence force the forbidden power-of-two cycle. -/
theorem internalSubgraphMinDegreeThree_free_of_p13Free
    {V : Type u} (object : FiniteObject V)
    (p13Free : InducedPathFree object.graph 13)
    (avoidsPowerCycle :
      ¬HasCycleWithLength object.graph (fun length =>
        ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent)) :
    ¬object.HasInternalSubgraphMinDegreeAtLeast 3 :=
  object.internalSubgraphMinDegreeFree_of_internalMinDegreeFree 3
    (internalMinDegreeThree_free_of_p13Free object p13Free
      avoidsPowerCycle)

end StructuralExhaustion.Graph.External.HegdeSandeepShashank
