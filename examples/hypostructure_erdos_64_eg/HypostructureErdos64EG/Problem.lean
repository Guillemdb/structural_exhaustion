import Hypostructure.Graph.Target
import HypostructureErdos64EG.TargetAlgebra

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-!
# Minimal EG problem registration

The target is external to `Core.Problem`. The application registers only the
minimum-degree baseline, a trivial initial branch state, and the exact dyadic
cycle proposition from the official statement.
-/

/-- The sole baseline hypothesis in the official theorem. -/
def Baseline (object : Graph.FiniteObject.{u}) : Prop :=
  object.minDegree ≥ 3

/-- There is no additional theorem state at the application root. -/
def BranchState (_object : Graph.FiniteObject.{u}) : Type :=
  Unit

/-- The minimal domain-neutral problem registration for Problem 64. -/
def problem : Core.Problem :=
  Graph.problem Baseline BranchState

/-- A packed graph realizes the target when it has an accepted Mathlib cycle. -/
def Target (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.HasCycleWithLength PowerOfTwoLength object

/-- The packed target is exactly the conclusion of the pinned official
statement for the same underlying graph. -/
theorem target_iff_official_conclusion (object : Graph.FiniteObject.{u}) :
    Target object ↔
      ∃ (exponent : Nat) (vertex : object.Vertex)
        (cycle : object.graph.Walk vertex vertex),
        exponent ≥ 2 ∧ cycle.IsCycle ∧ cycle.length = 2 ^ exponent := by
  constructor
  · rintro ⟨certificate⟩
    obtain ⟨exponent, lower, lengthEq⟩ :=
      (powerOfTwoLength_iff certificate.walk.length).mp
        certificate.length_ok
    exact ⟨exponent, certificate.vertex, certificate.walk, lower,
      certificate.isCycle, lengthEq⟩
  · rintro ⟨exponent, vertex, cycle, lower, isCycle, lengthEq⟩
    exact ⟨{
      vertex := vertex
      walk := cycle
      isCycle := isCycle
      length_ok := (powerOfTwoLength_iff cycle.length).mpr
        ⟨exponent, lower, lengthEq⟩
    }⟩

/-- The EG baseline descends through packed graph isomorphism. -/
def baselineIsomorphismInvariant :
    Graph.FiniteObject.IsomorphismInvariant Baseline where
  iff_of_iso := by
    intro left right equivalent
    unfold Baseline
    rw [Graph.FiniteObject.minDegree_eq_of_isomorphic equivalent]

/-- Canonical Core semantics obtained from the graph layer. -/
def isomorphismSemantics : Core.SemanticEquivalence problem :=
  Graph.isomorphismEquivalence Baseline BranchState
    baselineIsomorphismInvariant

/-- The reusable graph interface instantiated by the dyadic length predicate. -/
def targetInterface : Graph.TargetInterface Target :=
  Graph.cycleTargetInterface PowerOfTwoLength

/-- The dyadic-cycle target depends only on the graph's isomorphism class. -/
def targetIsomorphismInvariant :
    Graph.FiniteObject.IsomorphismInvariant Target :=
  targetInterface.isomorphismInvariant

/-- Core target invariance induced by the graph-isomorphism registration. -/
def targetInvariant :
    Core.TargetInvariant isomorphismSemantics Target :=
  targetInterface.coreInvariant Baseline BranchState
    baselineIsomorphismInvariant

end HypostructureErdos64EG
