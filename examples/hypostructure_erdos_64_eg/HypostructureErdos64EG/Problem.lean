import Hypostructure.Graph.Target
import HypostructureErdos64EG.TargetAlgebra

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-!
# EG problem and target registration

The application boundary exposes one Core problem and one Core target.  The
remaining declarations are compatibility names for the manuscript facades.
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

/-! The public theorem proposition is registered beside the Core problem
contract.  Core keeps targets separate from `Problem`; this alias is the
application boundary consumed by strategy-level terminal proofs. -/
abbrev officialStatement : Prop := OfficialStatement.{u}

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

/-! The single public target contract consumed by strategy code. -/

def target : Core.Target problem where
  Predicate := Target
  Statement := officialStatement
  statement_to_target := by
    intro official object baseline
    change OfficialStatement at official
    letI : Fintype object.Vertex :=
      @FinEnum.instFintype _ object.vertices
    letI : DecidableRel object.graph.Adj := object.decideAdj
    apply (target_iff_official_conclusion object).mpr
    simpa [Baseline] using
      official object.Vertex object.graph baseline
  target_to_statement := by
    intro all V G _ _ minimumDegree
    let vertices : FinEnum V :=
      FinEnum.ofEquiv (Fin (Fintype.card V))
        (Fintype.equivFin V)
    let object : Graph.FiniteObject :=
      Graph.FiniteObject.of G vertices inferInstance
    have baseline : Baseline object := by
      have fintype_eq :
          (inferInstance : Fintype V) = @FinEnum.instFintype _ vertices :=
        Subsingleton.elim _ _
      have decide_eq :
          (inferInstance : DecidableRel G.Adj) = object.decideAdj :=
        Subsingleton.elim _ _
      unfold Baseline
      change 3 ≤ @SimpleGraph.minDegree V G
        (@FinEnum.instFintype _ vertices) object.decideAdj
      rw [← fintype_eq, ← decide_eq]
      exact minimumDegree
    rcases (target_iff_official_conclusion object).mp
      (all object baseline) with
      ⟨exponent, vertex, cycle, lower, isCycle, lengthEq⟩
    exact ⟨exponent, vertex, cycle, lower, isCycle, lengthEq⟩

/-- Complete problem registration consumed by the strategy DAG runner. -/
def definition : Core.ProblemDefinition where
  problem := problem
  target := target
  initialState := fun _ => ()

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
