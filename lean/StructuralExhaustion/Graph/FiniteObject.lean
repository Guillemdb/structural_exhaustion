import Mathlib.Combinatorics.SimpleGraph.Dart
import StructuralExhaustion.Core.Context
import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Graph.Basic
import StructuralExhaustion.Graph.EdgeDeletion

namespace StructuralExhaustion.Graph

open StructuralExhaustion

universe u

/-!
# Finite graph objects for CT ambient types

`SimpleGraph` remains the mathematical graph.  `FiniteObject` only packages a
graph with the explicit finite execution input required by deterministic CT
machines.  This dependent bundle is useful as `Core.Problem.Ambient`, where an
edge deletion changes the graph and its adjacency decision procedure together.
-/

/-- A Mathlib graph bundled with deterministic finite execution input. -/
structure FiniteObject (V : Type u) where
  graph : SimpleGraph V
  input : FiniteInput graph

namespace FiniteInput

variable {V : Type u} {G : SimpleGraph V}

/-- Neighbours in the declared vertex order.  The underlying set is
`G.neighborFinset vertex`; this wrapper records only the observable CT scan
order. -/
def orderedNeighbors (input : FiniteInput G) (vertex : V) :
    Core.OrderedCollection V where
  values := input.vertices.orderedValues.filter fun other =>
    @decide (G.Adj vertex other) (input.decideAdj vertex other)
  nodup := input.vertices.nodup_orderedValues.filter _
  decEq := input.vertices.decEq

@[simp]
theorem mem_orderedNeighbors_iff (input : FiniteInput G)
    (vertex other : V) :
    other ∈ (input.orderedNeighbors vertex).values ↔ G.Adj vertex other := by
  letI : DecidableRel G.Adj := input.decideAdj
  simp [orderedNeighbors]

/-- Ordered and unordered neighbour views have the same cardinality. -/
theorem orderedNeighbors_length (input : FiniteInput G) (vertex : V) :
    (input.orderedNeighbors vertex).values.length =
      (letI : FinEnum V := input.vertices
       letI : DecidableRel G.Adj := input.decideAdj
       G.degree vertex) := by
  letI : FinEnum V := input.vertices
  letI : DecidableRel G.Adj := input.decideAdj
  rw [← List.toFinset_card_of_nodup
    (input.orderedNeighbors vertex).nodup]
  change (input.orderedNeighbors vertex).toFinset.card =
    (G.neighborFinset vertex).card
  congr 1
  ext other
  simp [SimpleGraph.mem_neighborFinset]

/-- Darts are enumerated lexicographically by their endpoint positions in the
declared vertex order. -/
@[implicit_reducible]
def darts (input : FiniteInput G) : FinEnum G.Dart := by
  let pairEnumeration :=
    Core.Enumeration.prod input.vertices input.vertices
  let adjacentPairs : FinEnum {pair : V × V // G.Adj pair.1 pair.2} :=
    Core.Enumeration.subtype pairEnumeration
      (fun pair => G.Adj pair.1 pair.2)
      (fun pair => input.decideAdj pair.1 pair.2)
  letI : FinEnum {pair : V × V // G.Adj pair.1 pair.2} := adjacentPairs
  exact FinEnum.ofEquiv {pair : V × V // G.Adj pair.1 pair.2}
    { toFun := fun dart => ⟨dart.toProd, dart.adj⟩
      invFun := fun pair => ⟨pair.1, pair.2⟩
      left_inv := fun dart => SimpleGraph.Dart.ext _ _ rfl
      right_inv := fun pair => Subtype.ext rfl }

end FiniteInput

namespace FiniteObject

variable {V : Type u}

/-- Shared unconditional problem used by graph profiles whose only ambient
datum is an explicitly finite Mathlib graph. -/
def problem (V : Type u) : Core.Problem.{u, 0} where
  Ambient := FiniteObject V
  Baseline := fun _object => True
  rank := fun object => object.input.vertices.card
  BranchState := fun _object => Unit

/-- Canonical branch context for an unconditional finite-graph computation. -/
def context (object : FiniteObject V) : Core.BranchContext (problem V) where
  G := object
  baseline := trivial
  state := ()

/-- Degree, computed by Mathlib after installing the object's explicit
instances locally. -/
def degree (object : FiniteObject V) (vertex : V) : Nat := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact object.graph.degree vertex

/-- Any explicit finite set of neighbours gives a reusable lower bound on
the degree.  This avoids repeating small-neighbour cardinality arguments in
local graph profiles. -/
theorem card_le_degree_of_adjacent_finset (object : FiniteObject V)
    (center : V) (neighbors : Finset V)
    (adjacent : ∀ vertex ∈ neighbors, object.graph.Adj center vertex) :
    neighbors.card ≤ object.degree center := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : DecidableEq V := object.input.vertices.decEq
  have subset : neighbors ⊆ object.graph.neighborFinset center := by
    intro vertex member
    simpa [SimpleGraph.mem_neighborFinset] using adjacent vertex member
  exact Finset.card_le_card subset

/-- Instance-independent set-cardinality form of the bundled degree.  This is
the convenient bridge when two finite schedules enumerate the same
mathematical neighbour set. -/
theorem degree_eq_ncard_neighborSet (object : FiniteObject V) (vertex : V) :
    object.degree vertex = (object.graph.neighborSet vertex).ncard := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  unfold degree
  rw [Set.ncard_eq_toFinset_card']
  rfl

/-- Mathlib minimum degree of the bundled graph. -/
def minDegree (object : FiniteObject V) : Nat := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact object.graph.minDegree

/-- Mathlib maximum degree of the bundled graph. -/
def maxDegree (object : FiniteObject V) : Nat := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact object.graph.maxDegree

/-- Mathlib edge count, used as the standard CT2 deletion rank. -/
def edgeCount (object : FiniteObject V) : Nat := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact object.graph.edgeFinset.card

theorem minDegree_le_degree (object : FiniteObject V) (vertex : V) :
    object.minDegree ≤ object.degree vertex := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact object.graph.minDegree_le_degree vertex

/-- Bundle-level form of Mathlib's pointwise minimum-degree introduction
rule. -/
theorem le_minDegree_of_forall_le_degree (object : FiniteObject V)
    [Nonempty V] (bound : Nat)
    (pointwise : ∀ vertex, bound ≤ object.degree vertex) :
    bound ≤ object.minDegree := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact object.graph.le_minDegree_of_forall_le_degree bound pointwise

/-- Every vertex degree is bounded by the object's Mathlib maximum degree. -/
theorem degree_le_maxDegree (object : FiniteObject V) (vertex : V) :
    object.degree vertex ≤ object.maxDegree := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact object.graph.degree_le_maxDegree vertex

/-- A positive Mathlib minimum degree certifies that the vertex type is
nonempty. -/
theorem nonempty_of_minDegree_pos (object : FiniteObject V)
    (positive : 0 < object.minDegree) : Nonempty V := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  cases isEmpty_or_nonempty V with
  | inl empty =>
      letI : IsEmpty V := empty
      have zero : object.minDegree = 0 := by
        exact object.graph.minDegree_of_isEmpty
      omega
  | inr nonempty => exact nonempty

/-- Delete the undirected edge underlying a Mathlib dart and retain the same
vertex schedule. -/
def deleteDart (object : FiniteObject V) (dart : object.graph.Dart) :
    FiniteObject V where
  graph := EdgeDeletion.deleteDart object.graph dart
  input := {
    vertices := object.input.vertices
    decideAdj := by
      letI : FinEnum V := object.input.vertices
      letI : DecidableRel object.graph.Adj := object.input.decideAdj
      infer_instance
  }

/-- Single-dart deletion strictly lowers the Mathlib edge-count rank. -/
theorem edgeCount_deleteDart_lt (object : FiniteObject V)
    (dart : object.graph.Dart) :
    (object.deleteDart dart).edgeCount < object.edgeCount := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact EdgeDeletion.card_edgeFinset_deleteDart_lt dart

/-- Endpoint slack is the complete condition needed to preserve a minimum
degree bound under one-dart deletion. -/
theorem deleteDart_preserves_minDegree (object : FiniteObject V)
    (dart : object.graph.Dart) (bound : Nat)
    (baseline : bound ≤ object.minDegree)
    (fstSlack : bound + 1 ≤ object.degree dart.fst)
    (sndSlack : bound + 1 ≤ object.degree dart.snd) :
    bound ≤ (object.deleteDart dart).minDegree := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : Nonempty V := ⟨dart.fst⟩
  exact EdgeDeletion.deleteDart_preserves_minDegree dart bound baseline
    fstSlack sndSlack

/-- The deleted graph is a standard Mathlib subgraph of the source graph. -/
theorem deleteDart_le (object : FiniteObject V)
    (dart : object.graph.Dart) :
    (object.deleteDart dart).graph ≤ object.graph :=
  EdgeDeletion.deleteDart_le dart

/-- Every cycle-length target in the deleted object transports to the source
object through Mathlib graph inclusion. -/
theorem hasCycleWithLength_of_deleteDart (object : FiniteObject V)
    (dart : object.graph.Dart) {LengthOK : Nat → Prop} :
    HasCycleWithLength (object.deleteDart dart).graph LengthOK →
      HasCycleWithLength object.graph LengthOK :=
  EdgeDeletion.hasCycleWithLength_of_deleteDart dart

end FiniteObject

end StructuralExhaustion.Graph
