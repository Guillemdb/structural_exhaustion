import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import StructuralExhaustion.Graph.Cycle

namespace StructuralExhaustion.Graph.EdgeDeletion

universe u

open Finset

variable {V : Type u} {G : SimpleGraph V}

/-!
# Deleting one actual Mathlib edge

Mathlib supplies `SimpleGraph.deleteEdges`; an actual oriented edge is its
standard `SimpleGraph.Dart`.  This file adds only the exact one-edge accounting
lemmas needed by minimal-counterexample machines.
-/

/-- Delete the undirected edge underlying an actual Mathlib dart. -/
def deleteDart (G : SimpleGraph V) (dart : G.Dart) : SimpleGraph V :=
  G.deleteEdges {dart.edge}

instance instDecidableRelDeleteDart [DecidableEq V] [DecidableRel G.Adj]
    (dart : G.Dart) : DecidableRel (deleteDart G dart).Adj := by
  unfold deleteDart
  infer_instance

@[simp]
theorem deleteDart_adj (dart : G.Dart) (left right : V) :
    (deleteDart G dart).Adj left right ↔
      G.Adj left right ∧ s(left, right) ≠ dart.edge := by
  simp [deleteDart]

/-- One-edge deletion is standard graph inclusion. -/
theorem deleteDart_le (dart : G.Dart) : deleteDart G dart ≤ G :=
  G.deleteEdges_le {dart.edge}

private theorem mk_fst_eq_edge_iff (dart : G.Dart) (vertex : V) :
    s(dart.fst, vertex) = dart.edge ↔ vertex = dart.snd := by
  rw [eq_comm, SimpleGraph.dart_edge_eq_mk'_iff']
  simp [eq_comm]

private theorem mk_snd_eq_edge_iff (dart : G.Dart) (vertex : V) :
    s(dart.snd, vertex) = dart.edge ↔ vertex = dart.fst := by
  rw [eq_comm, SimpleGraph.dart_edge_eq_mk'_iff']
  simp [eq_comm]

private theorem mk_ne_edge_of_ne (dart : G.Dart) {vertex other : V}
    (notFst : vertex ≠ dart.fst) (notSnd : vertex ≠ dart.snd) :
    s(vertex, other) ≠ dart.edge := by
  intro equal
  rw [eq_comm, SimpleGraph.dart_edge_eq_mk'_iff'] at equal
  rcases equal with equal | equal
  · exact notFst equal.1.symm
  · exact notSnd equal.2.symm

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

@[simp]
theorem neighborFinset_deleteDart_fst (dart : G.Dart) :
    (deleteDart G dart).neighborFinset dart.fst =
      (G.neighborFinset dart.fst).erase dart.snd := by
  ext vertex
  simp [deleteDart_adj, mk_fst_eq_edge_iff, and_comm]

@[simp]
theorem neighborFinset_deleteDart_snd (dart : G.Dart) :
    (deleteDart G dart).neighborFinset dart.snd =
      (G.neighborFinset dart.snd).erase dart.fst := by
  ext vertex
  simp [deleteDart_adj, mk_snd_eq_edge_iff, and_comm]

@[simp]
theorem neighborFinset_deleteDart_other (dart : G.Dart) (vertex : V)
    (notFst : vertex ≠ dart.fst) (notSnd : vertex ≠ dart.snd) :
    (deleteDart G dart).neighborFinset vertex = G.neighborFinset vertex := by
  ext other
  simp [deleteDart_adj, mk_ne_edge_of_ne dart notFst notSnd]

/-- Deleting an actual edge lowers the degree of its first endpoint by one. -/
theorem degree_deleteDart_fst_add_one (dart : G.Dart) :
    (deleteDart G dart).degree dart.fst + 1 = G.degree dart.fst := by
  change #((deleteDart G dart).neighborFinset dart.fst) + 1 =
    #(G.neighborFinset dart.fst)
  rw [neighborFinset_deleteDart_fst]
  exact Finset.card_erase_add_one
    ((G.mem_neighborFinset dart.fst dart.snd).2 dart.adj)

/-- Deleting an actual edge lowers the degree of its second endpoint by one. -/
theorem degree_deleteDart_snd_add_one (dart : G.Dart) :
    (deleteDart G dart).degree dart.snd + 1 = G.degree dart.snd := by
  change #((deleteDart G dart).neighborFinset dart.snd) + 1 =
    #(G.neighborFinset dart.snd)
  rw [neighborFinset_deleteDart_snd]
  exact Finset.card_erase_add_one
    ((G.mem_neighborFinset dart.snd dart.fst).2 dart.adj.symm)

/-- All other vertex degrees are unchanged by one-edge deletion. -/
theorem degree_deleteDart_other (dart : G.Dart) (vertex : V)
    (notFst : vertex ≠ dart.fst) (notSnd : vertex ≠ dart.snd) :
    (deleteDart G dart).degree vertex = G.degree vertex := by
  change #((deleteDart G dart).neighborFinset vertex) =
    #(G.neighborFinset vertex)
  rw [neighborFinset_deleteDart_other dart vertex notFst notSnd]

/-- If both endpoints have one unit of slack, deleting their edge preserves a
minimum-degree lower bound. -/
theorem deleteDart_preserves_minDegree [Nonempty V]
    (dart : G.Dart) (bound : Nat)
    (baseline : bound ≤ G.minDegree)
    (fstSlack : bound + 1 ≤ G.degree dart.fst)
    (sndSlack : bound + 1 ≤ G.degree dart.snd) :
    bound ≤ (deleteDart G dart).minDegree := by
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro vertex
  by_cases isFst : vertex = dart.fst
  · subst vertex
    have drop := degree_deleteDart_fst_add_one dart
    omega
  · by_cases isSnd : vertex = dart.snd
    · subst vertex
      have drop := degree_deleteDart_snd_add_one dart
      omega
    · rw [degree_deleteDart_other dart vertex isFst isSnd]
      exact baseline.trans (G.minDegree_le_degree vertex)

@[simp]
theorem edgeFinset_deleteDart (dart : G.Dart) :
    (deleteDart G dart).edgeFinset = G.edgeFinset.erase dart.edge := by
  ext edge
  simp [deleteDart, SimpleGraph.edgeSet_deleteEdges, and_comm]

/-- Exact edge-count accounting for deleting an actual edge. -/
theorem card_edgeFinset_deleteDart_add_one (dart : G.Dart) :
    #(deleteDart G dart).edgeFinset + 1 = #G.edgeFinset := by
  rw [edgeFinset_deleteDart]
  exact Finset.card_erase_add_one (by simp)

theorem card_edgeFinset_deleteDart_lt (dart : G.Dart) :
    #(deleteDart G dart).edgeFinset < #G.edgeFinset := by
  rw [edgeFinset_deleteDart]
  exact Finset.card_erase_lt_of_mem (by simp)

/-- The degree sum drops by two; this is a direct consequence of Mathlib's
degree-sum theorem rather than a separate incidence implementation. -/
theorem sum_degrees_deleteDart_add_two (dart : G.Dart) :
    (∑ vertex, (deleteDart G dart).degree vertex) + 2 =
      ∑ vertex, G.degree vertex := by
  rw [(deleteDart G dart).sum_degrees_eq_twice_card_edges,
    G.sum_degrees_eq_twice_card_edges]
  have drop := card_edgeFinset_deleteDart_add_one dart
  omega

end Finite

/-- Every cycle-length target transports from the deleted graph back to its
source through Mathlib's `Walk.mapLe`. -/
theorem hasCycleWithLength_of_deleteDart (dart : G.Dart)
    {LengthOK : Nat → Prop} :
    HasCycleWithLength (deleteDart G dart) LengthOK →
      HasCycleWithLength G LengthOK :=
  hasCycleWithLength_mono (deleteDart_le dart)

end StructuralExhaustion.Graph.EdgeDeletion
