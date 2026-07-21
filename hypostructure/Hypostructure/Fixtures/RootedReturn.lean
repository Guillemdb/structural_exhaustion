import Hypostructure.Graph.RootedReturn

/-!
# Edge-rooted return fixtures

The complete graph on four vertices supplies a literal two-edge return from
`1` to `0` after deleting the oriented root edge `0 → 1`. Restoring that
edge closes a triangle. The same return length is rejected by the shifted
length-four predicate.
-/

namespace Hypostructure.Fixtures.RootedReturn

open Graph
open scoped Sym2

abbrev Vertex := Fin 4

def graph : SimpleGraph Vertex := ⊤

def object : FiniteObject :=
  FiniteObject.of graph inferInstance (by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance)

/-- The concrete oriented edge `0 → 1` in `K4`. -/
def rootDart : object.graph.Dart := by
  change graph.Dart
  exact ⟨((0 : Vertex), (1 : Vertex)), by simp [graph]⟩

/-- The literal return `1-2-0` after deleting the root edge `0-1`. -/
def returnWalk :
    (object.graph.deleteEdges {rootDart.edge}).Walk
      rootDart.snd rootDart.fst := by
  change (graph.deleteEdges {s((0 : Vertex), (1 : Vertex))}).Walk 1 0
  exact .cons (v := (2 : Vertex)) (by simp [graph])
    (.cons (v := (0 : Vertex)) (by simp [graph]) .nil)

theorem returnWalk_isPath : returnWalk.IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  change ([1, 2, 0] : List Vertex).Nodup
  decide

def TriangleLength (length : Nat) : Prop := length = 3

def FourLength (length : Nat) : Prop := length = 4

/-- The concrete return is accepted precisely because restoring its root edge
gives length three. -/
def triangleReturn :
    EdgeRootedReturn object (ShiftedCycleLength TriangleLength) where
  dart := rootDart
  path := returnWalk
  isPath := returnWalk_isPath
  length_ok := rfl

theorem triangleReturn_dart : triangleReturn.dart = rootDart := rfl

theorem triangleReturn_length : triangleReturn.path.length = 2 := by
  change returnWalk.length = 2
  rfl

theorem triangleReturn_cycle_length : triangleReturn.cycle.length = 3 := by
  rw [triangleReturn.cycle_length, triangleReturn_length]

theorem triangleReturn_cycle_isCycle : triangleReturn.cycle.IsCycle :=
  triangleReturn.cycle_isCycle

def triangleAlgebra : RootedReturnTargetAlgebra TriangleLength :=
  RootedReturnTargetAlgebra.shifted TriangleLength

/-- The profile bridge turns the concrete rooted return into the public K4
cycle target without performing any search. -/
theorem k4_has_triangle_target :
    HasCycleWithLength TriangleLength object :=
  (triangleAlgebra.target_iff_hasRootedReturn object).mpr ⟨triangleReturn⟩

theorem two_mem_returnLengthSet :
    2 ∈ returnLengthSet object rootDart :=
  ⟨returnWalk, returnWalk_isPath, rfl⟩

/-- Length two does not close to a length-four cycle; the shifted target would
require a three-edge return. -/
theorem two_rejected_by_shifted_four :
    ¬ ShiftedCycleLength FourLength triangleReturn.path.length := by
  simp [ShiftedCycleLength, FourLength, triangleReturn_length]

theorem two_not_mem_shifted_four_set :
    2 ∉ shiftedAcceptedSet FourLength := by
  simp [shiftedAcceptedSet, ShiftedCycleLength, FourLength]

#print axioms Graph.EdgeRootedReturn.cycle_isCycle
#print axioms Graph.hasCycleWithLength_iff_hasEdgeRootedReturn
#print axioms Graph.not_hasCycleWithLength_iff_returnLengthSets_disjoint
#print axioms returnWalk_isPath
#print axioms triangleReturn_cycle_isCycle
#print axioms k4_has_triangle_target
#print axioms two_rejected_by_shifted_four

end Hypostructure.Fixtures.RootedReturn
