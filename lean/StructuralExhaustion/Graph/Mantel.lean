import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import StructuralExhaustion.CT11.Automation
import StructuralExhaustion.Graph.FiniteObject

namespace StructuralExhaustion.Graph.Mantel

open StructuralExhaustion
open scoped BigOperators

universe u

/-- CT11 cells are the existing exact dart enumeration of the finite graph. -/
def dartCells (object : FiniteObject V) :
    Core.OrderedCollection object.graph.Dart :=
  object.input.darts.toOrderedCollection

/-- The local Mantel budget at an oriented edge.  Each undirected edge occurs
twice, but the sign and the selected contradiction are orientation-invariant. -/
def localBudget (object : FiniteObject V) (dart : object.graph.Dart) : Int :=
  (object.input.vertices.card : Int) - object.degree dart.fst -
    object.degree dart.snd

/-- Sum of squared Mathlib degrees using the finite instances carried by the
graph object. -/
def degreeSquareSum (object : FiniteObject V) : Nat := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact ∑ vertex : V, (object.graph.degree vertex) ^ 2

/-- The minimal CT11 profile for Mantel localization. -/
def profile (object : FiniteObject V) :
    CT11.NegativeBudgetProfile (FiniteObject.problem V) where
  Cell := object.graph.Dart
  localBudget := fun _context => localBudget object

private theorem sum_degrees_fst_darts (object : FiniteObject V) :
    letI : FinEnum V := object.input.vertices
    letI : DecidableRel object.graph.Adj := object.input.decideAdj
    (∑ dart : object.graph.Dart, object.graph.degree dart.fst) =
      degreeSquareSum object := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  classical
  change (∑ dart : object.graph.Dart, object.graph.degree dart.fst) =
    ∑ vertex : V, (object.graph.degree vertex) ^ 2
  rw [← Finset.sum_fiberwise (Finset.univ : Finset object.graph.Dart)
    (fun dart => dart.fst) (fun dart => object.graph.degree dart.fst)]
  apply Finset.sum_congr rfl
  intro vertex _member
  rw [Finset.sum_eq_card_nsmul (b := object.graph.degree vertex) (by
    intro dart member
    have equal : dart.fst = vertex := by simpa using member
    cases equal
    rfl)]
  change ({dart : object.graph.Dart | dart.fst = vertex} : Finset _).card *
      object.graph.degree vertex = object.graph.degree vertex ^ 2
  rw [object.graph.dart_fst_fiber_card_eq_degree vertex]
  simp [pow_two]

private theorem sum_degrees_snd_darts (object : FiniteObject V) :
    letI : FinEnum V := object.input.vertices
    letI : DecidableRel object.graph.Adj := object.input.decideAdj
    (∑ dart : object.graph.Dart, object.graph.degree dart.snd) =
      degreeSquareSum object := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  classical
  calc
    (∑ dart : object.graph.Dart, object.graph.degree dart.snd) =
        ∑ dart : object.graph.Dart, object.graph.degree dart.fst := by
      apply Fintype.sum_bijective SimpleGraph.Dart.symm
        SimpleGraph.Dart.symm_involutive.bijective
      intro dart
      rfl
    _ = degreeSquareSum object :=
      sum_degrees_fst_darts object

/-- In a triangle-free graph, the endpoint neighbourhoods of an edge are
disjoint, so the two endpoint degrees sum to at most the vertex count. -/
theorem degree_add_degree_le_card_of_triangleFree
    (object : FiniteObject V) (triangleFree : object.graph.CliqueFree 3)
    (dart : object.graph.Dart) :
    object.degree dart.fst + object.degree dart.snd ≤
      object.input.vertices.card := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : DecidableEq V := object.input.vertices.decEq
  have independent :=
    object.graph.isIndepSet_neighborSet_of_triangleFree triangleFree dart.fst
  have neighborhoodsDisjoint : Disjoint
      (object.graph.neighborFinset dart.fst)
      (object.graph.neighborFinset dart.snd) := by
    rw [Finset.disjoint_left]
    intro vertex firstNeighbor secondNeighbor
    have firstAdjacent : object.graph.Adj dart.fst vertex := by
      simpa using firstNeighbor
    have secondAdjacent : object.graph.Adj dart.snd vertex := by
      simpa using secondNeighbor
    exact independent dart.adj firstAdjacent secondAdjacent.ne secondAdjacent
  calc
    object.degree dart.fst + object.degree dart.snd =
        (object.graph.neighborFinset dart.fst).card +
          (object.graph.neighborFinset dart.snd).card := rfl
    _ = ((object.graph.neighborFinset dart.fst) ∪
          (object.graph.neighborFinset dart.snd)).card :=
      (Finset.card_union_of_disjoint neighborhoodsDisjoint).symm
    _ ≤ (Finset.univ : Finset V).card :=
      Finset.card_le_card (by simp)
    _ = object.input.vertices.card := FinEnum.card_eq_fintypeCard.symm

/-- Exact global budget identity.  The two dart orientations account for the
factor two on both the edge-count term and the squared-degree term. -/
theorem sum_localBudget_eq (object : FiniteObject V) :
    ((dartCells object).values.map (localBudget object)).sum =
      2 * (object.edgeCount : Int) * object.input.vertices.card -
        2 * (degreeSquareSum object : Int) := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  rw [Core.OrderedCollection.sum_values_eq_sum_toFinset]
  have cellsUniv : (dartCells object).toFinset =
      (Finset.univ : Finset object.graph.Dart) := by
    ext dart
    rw [Core.OrderedCollection.mem_toFinset]
    simp only [Finset.mem_univ, iff_true]
    exact object.input.darts.mem_orderedValues dart
  rw [cellsUniv]
  simp only [localBudget, FiniteObject.degree]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have fstSum := congrArg (fun value : Nat => (value : Int))
    (sum_degrees_fst_darts object)
  have sndSum := congrArg (fun value : Nat => (value : Int))
    (sum_degrees_snd_darts object)
  push_cast at fstSum sndSum
  rw [fstSum, sndSum]
  have dartCount := congrArg (fun value : Nat => (value : Int))
    object.graph.dart_card_eq_twice_card_edges
  push_cast at dartCount
  rw [dartCount]
  simp only [FiniteObject.edgeCount]
  ring

/-- Cauchy--Schwarz combined with Mathlib's degree-sum formula, expressed
entirely through the finite graph object's computed invariants. -/
theorem four_mul_edgeCount_sq_le_card_mul_degreeSquareSum
    (object : FiniteObject V) :
    (2 * object.edgeCount) ^ 2 ≤
      object.input.vertices.card * degreeSquareSum object := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  have cauchy := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset V)) (f := fun v => object.graph.degree v)
  rw [object.graph.sum_degrees_eq_twice_card_edges] at cauchy
  change (2 * object.graph.edgeFinset.card) ^ 2 ≤
    Fintype.card V * ∑ vertex : V, object.graph.degree vertex ^ 2 at cauchy
  change (2 * object.edgeCount) ^ 2 ≤
    object.input.vertices.card * degreeSquareSum object
  simpa only [degreeSquareSum, FiniteObject.edgeCount,
    FinEnum.card_eq_fintypeCard] using cauchy

/-- A counterexample to the numerical Mantel bound makes the exact dart
budget strictly negative. -/
theorem deficit_of_mantel_violation (object : FiniteObject V)
    (violation : object.input.vertices.card ^ 2 < 4 * object.edgeCount) :
    ((dartCells object).values.map (localBudget object)).sum < 0 := by
  have cauchy :=
    four_mul_edgeCount_sq_le_card_mul_degreeSquareSum object
  have squareSumLarge :
      object.input.vertices.card * object.edgeCount < degreeSquareSum object := by
    nlinarith
  rw [sum_localBudget_eq]
  exact sub_neg.mpr (by exact_mod_cast (by nlinarith :
    2 * object.edgeCount * object.input.vertices.card <
      2 * degreeSquareSum object))

/-- Exact CT11 input generated from a failed Mantel inequality. -/
def input (object : FiniteObject V)
    (violation : object.input.vertices.card ^ 2 < 4 * object.edgeCount) :=
  (profile object).input (FiniteObject.context object) (dartCells object)
    (deficit_of_mantel_violation object violation)

/-- Exact CT11 execution generated from a failed Mantel inequality. -/
def run (object : FiniteObject V)
    (violation : object.input.vertices.card ^ 2 < 4 * object.edgeCount) :=
  (profile object).run (FiniteObject.context object) (dartCells object)
    (deficit_of_mantel_violation object violation)

/-- The failed-bound execution reaches CT11's localized-deficit terminal. -/
theorem run_terminal_localized (object : FiniteObject V)
    (violation : object.input.vertices.card ^ 2 < 4 * object.edgeCount) :
    (run object violation).terminal = .localized :=
  (profile object).run_terminal_localized (FiniteObject.context object)
    (dartCells object) (deficit_of_mantel_violation object violation)

/-- The canonical dart selected by CT11 from a failed Mantel bound. -/
def offendingResidual (object : FiniteObject V)
    (violation : object.input.vertices.card ^ 2 < 4 * object.edgeCount) :=
  (profile object).residual (FiniteObject.context object) (dartCells object)
    (deficit_of_mantel_violation object violation)

/-- CT11's residual states that the selected dart has endpoint-degree sum
strictly larger than the vertex count. -/
theorem offending_degree_sum_gt (object : FiniteObject V)
    (violation : object.input.vertices.card ^ 2 < 4 * object.edgeCount) :
    object.input.vertices.card <
      object.degree (offendingResidual object violation).cell.fst +
        object.degree (offendingResidual object violation).cell.snd := by
  have negative := (offendingResidual object violation).negative
  change (object.input.vertices.card : Int) -
      object.degree (offendingResidual object violation).cell.fst -
      object.degree (offendingResidual object violation).cell.snd < 0 at negative
  omega

/-- Mantel's theorem in multiplication form, proved by CT11 localization. -/
theorem four_mul_edgeCount_le_card_sq_of_triangleFree
    (object : FiniteObject V) (triangleFree : object.graph.CliqueFree 3) :
    4 * object.edgeCount ≤ object.input.vertices.card ^ 2 := by
  by_contra notBounded
  have violation : object.input.vertices.card ^ 2 < 4 * object.edgeCount :=
    Nat.lt_of_not_ge notBounded
  have localized := offending_degree_sum_gt object violation
  have triangleBound := degree_add_degree_le_card_of_triangleFree object
    triangleFree (offendingResidual object violation).cell
  omega

/-- Standard floor-division form of Mantel's theorem. -/
theorem edgeCount_le_card_sq_div_four_of_triangleFree
    (object : FiniteObject V) (triangleFree : object.graph.CliqueFree 3) :
    object.edgeCount ≤ object.input.vertices.card ^ 2 / 4 := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
  rw [Nat.mul_comm]
  exact four_mul_edgeCount_le_card_sq_of_triangleFree object triangleFree

end StructuralExhaustion.Graph.Mantel
