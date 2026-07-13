import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace StructuralExhaustion.Graph

universe u

/-!
# Cycle-length certificates

Mathlib already supplies walks and the graph-theoretic predicate
`SimpleGraph.Walk.IsCycle`.  This file only bundles a cycle with an
application-selected predicate on its length.  It deliberately introduces no
parallel walk, path, or cycle-list theory.
-/

/-- A Mathlib simple cycle whose length satisfies `LengthOK`. -/
structure CycleWithLength {V : Type u} (G : SimpleGraph V)
    (LengthOK : Nat → Prop) where
  vertex : V
  walk : G.Walk vertex vertex
  isCycle : walk.IsCycle
  length_ok : LengthOK walk.length

/-- Public existence predicate shared by graph problems that constrain cycle
lengths. -/
def HasCycleWithLength {V : Type u} (G : SimpleGraph V)
    (LengthOK : Nat → Prop) : Prop :=
  Nonempty (CycleWithLength G LengthOK)

/-- Exact length predicate for triangles. -/
def TriangleLength (length : Nat) : Prop := length = 3

/-- Triangle-freeness excludes exactly the length-three cycle target. -/
theorem not_hasCycleWithTriangleLength_of_cliqueFree
    {V : Type u} {G : SimpleGraph V} (triangleFree : G.CliqueFree 3) :
    ¬HasCycleWithLength G TriangleLength := by
  rintro ⟨cycle⟩
  have triangle : ∃ label : Finset V, G.IsNClique 3 label :=
    (SimpleGraph.is3Clique_iff_exists_cycle_length_three (G := G)).2
      ⟨cycle.vertex, cycle.walk, cycle.isCycle, cycle.length_ok⟩
  obtain ⟨label, clique⟩ := triangle
  exact triangleFree label clique

namespace CycleWithLength

variable {V : Type u} {G H : SimpleGraph V} {LengthOK : Nat → Prop}

/-- The number of edges in the certified Mathlib cycle. -/
def length (cycle : CycleWithLength G LengthOK) : Nat :=
  cycle.walk.length

theorem three_le_length (cycle : CycleWithLength G LengthOK) :
    3 ≤ cycle.length :=
  cycle.isCycle.three_le_length

/-- Package an existing Mathlib cycle proof. -/
def ofIsCycle {vertex : V} {walk : G.Walk vertex vertex}
    (isCycle : walk.IsCycle) (length_ok : LengthOK walk.length) :
    CycleWithLength G LengthOK where
  vertex := vertex
  walk := walk
  isCycle := isCycle
  length_ok := length_ok

/-- Transport a cycle certificate along standard graph inclusion. -/
def mapLe (included : G ≤ H) (cycle : CycleWithLength G LengthOK) :
    CycleWithLength H LengthOK where
  vertex := cycle.vertex
  walk := cycle.walk.mapLe included
  isCycle := cycle.isCycle.mapLe included
  length_ok := by
    change LengthOK (cycle.walk.map (.ofLE included)).length
    rw [SimpleGraph.Walk.length_map]
    exact cycle.length_ok

/-- Transport a cycle certificate through an injective graph homomorphism,
preserving its exact Mathlib walk length. -/
def mapHom {W : Type*} {K : SimpleGraph W}
    (hom : G →g K) (injective : Function.Injective hom)
    (cycle : CycleWithLength G LengthOK) :
    CycleWithLength K LengthOK where
  vertex := hom cycle.vertex
  walk := cycle.walk.map hom
  isCycle := cycle.isCycle.map injective
  length_ok := by
    rw [SimpleGraph.Walk.length_map]
    exact cycle.length_ok

end CycleWithLength

/-- Cycle-length existence is monotone under standard graph inclusion. -/
theorem hasCycleWithLength_mono {V : Type u} {G H : SimpleGraph V}
    {LengthOK : Nat → Prop} (included : G ≤ H) :
    HasCycleWithLength G LengthOK → HasCycleWithLength H LengthOK := by
  rintro ⟨cycle⟩
  exact ⟨cycle.mapLe included⟩

/-- Cycle-length existence is monotone through injective graph
homomorphisms. -/
theorem hasCycleWithLength_mapHom {V : Type u} {W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} {LengthOK : Nat → Prop}
    (hom : G →g H) (injective : Function.Injective hom) :
    HasCycleWithLength G LengthOK → HasCycleWithLength H LengthOK := by
  rintro ⟨cycle⟩
  exact ⟨cycle.mapHom hom injective⟩

/-- In a finite graph whose non-isolated components are cycles, every simple
cycle visits its entire connected component. -/
theorem cycle_length_eq_component_card_of_isCycles
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (isCycles : G.IsCycles) {vertex : V}
    (walk : G.Walk vertex vertex) (isCycle : walk.IsCycle) :
    walk.length = (G.connectedComponentMk vertex).supp.ncard := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  letI : G.LocallyFinite := inferInstance
  have closed :
      ∀ v ∈ walk.toSubgraph.verts, ∀ w, G.Adj v w →
        walk.toSubgraph.Adj v w := by
    intro v vertexMember w adjacent
    exact (isCycle.adj_toSubgraph_iff_of_isCycles
      isCycles vertexMember w).mpr adjacent
  obtain ⟨component, componentEq⟩ :=
    walk.toSubgraph_connected.exists_verts_eq_connectedComponentSupp closed
  have componentId : G.connectedComponentMk vertex = component := by
    rw [← SimpleGraph.ConnectedComponent.mem_supp_iff]
    rw [← componentEq]
    exact walk.start_mem_verts_toSubgraph
  have tailSetEq :
      {w | w ∈ walk.support.tail} = component.supp := by
    ext w
    constructor
    · intro tailMember
      rw [← componentEq, walk.mem_verts_toSubgraph]
      exact List.mem_of_mem_tail tailMember
    · intro componentMember
      have supportMember : w ∈ walk.support := by
        rw [← walk.mem_verts_toSubgraph, componentEq]
        exact componentMember
      by_cases atStart : w = vertex
      · subst w
        exact walk.end_mem_tail_support isCycle.not_nil
      · rw [← walk.cons_tail_support] at supportMember
        exact (List.mem_cons.mp supportMember).resolve_left atStart
  have tailLength : walk.support.tail.length = walk.length := by
    rw [List.length_tail, walk.length_support]
    omega
  have tailCard :
      walk.support.tail.length = ({w | w ∈ walk.support.tail} : Set V).ncard := by
    have setEq :
        ({w | w ∈ walk.support.tail} : Set V) =
          (walk.support.tail.toFinset : Set V) := by
      ext w
      simp
    rw [setEq, Set.ncard_coe_finset]
    exact (List.toFinset_card_of_nodup isCycle.support_nodup).symm
  rw [componentId, ← tailSetEq, ← tailCard, tailLength]

/-- The canonical cycle graph has one 2-regular component. -/
theorem cycleGraph_isCycles (offset : Nat) :
    (SimpleGraph.cycleGraph (offset + 3)).IsCycles := by
  intro vertex _nonisolated
  rw [SimpleGraph.cycleGraph_neighborSet]
  apply Set.ncard_pair
  simp only [ne_eq, sub_eq_iff_eq_add, add_assoc vertex, left_eq_add]
  exact ne_of_beq_false rfl

/-- Every simple cycle in a connected finite 2-regular graph visits the whole
graph.  This is the structural fact used by parity-series reductions; it
avoids enumerating closed walks or ambient graph universes. -/
theorem cycle_length_eq_card_of_connected_isCycles
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (connected : G.Connected)
    (isCycles : G.IsCycles) {vertex : V}
    (walk : G.Walk vertex vertex) (isCycle : walk.IsCycle) :
    walk.length = Fintype.card V := by
  rw [cycle_length_eq_component_card_of_isCycles isCycles walk isCycle]
  have componentUniv :
      (G.connectedComponentMk vertex).supp = (Set.univ : Set V) := by
    ext w
    simp only [Set.mem_univ, iff_true,
      SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.sound (connected w vertex)
  rw [componentUniv, Set.ncard_univ, Nat.card_eq_fintype_card]

/-- A canonical cycle graph realizes a selected length predicate exactly
when that predicate accepts its full cycle length. -/
theorem hasCycleWithLength_cycleGraph_iff
    (LengthOK : Nat → Prop) (offset : Nat) :
    HasCycleWithLength (SimpleGraph.cycleGraph (offset + 3)) LengthOK ↔
      LengthOK (offset + 3) := by
  constructor
  · rintro ⟨cycle⟩
    have lengthEq : cycle.walk.length = offset + 3 := by
      have exactCard := cycle_length_eq_card_of_connected_isCycles
        (SimpleGraph.cycleGraph_connected (n := offset + 2))
        (cycleGraph_isCycles offset) cycle.walk cycle.isCycle
      simp only [Fintype.card_fin] at exactCard
      omega
    simpa [lengthEq] using cycle.length_ok
  · intro accepted
    exact ⟨{
      vertex := 0
      walk := SimpleGraph.cycleGraph.cycle offset
      isCycle := SimpleGraph.cycleGraph.isCycle_cycle
      length_ok := by simpa using accepted
    }⟩

variable {V : Type u} {G : SimpleGraph V} {vertex : V}

/-- Decidability of Mathlib's cycle predicate on a concrete closed walk. -/
def isCycleDecidable [DecidableEq V] (walk : G.Walk vertex vertex) :
    Decidable walk.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
  infer_instance

/-- Exact acceptance predicate used by finite CT encodings of closed walks. -/
def AcceptsCycleLength (LengthOK : Nat → Prop)
    (walk : G.Walk vertex vertex) : Prop :=
  walk.IsCycle ∧ LengthOK walk.length

def acceptsCycleLengthDecidable [DecidableEq V]
    (LengthOK : Nat → Prop)
    (lengthDecidable : (length : Nat) → Decidable (LengthOK length))
    (walk : G.Walk vertex vertex) :
    Decidable (AcceptsCycleLength LengthOK walk) := by
  unfold AcceptsCycleLength
  exact @instDecidableAnd _ _ (isCycleDecidable walk)
    (lengthDecidable walk.length)

/-- Turn an accepted closed walk into the public bundled certificate. -/
def toCycleWithLength {LengthOK : Nat → Prop}
    {walk : G.Walk vertex vertex}
    (accepted : AcceptsCycleLength LengthOK walk) :
    CycleWithLength G LengthOK :=
  CycleWithLength.ofIsCycle accepted.1 accepted.2

end StructuralExhaustion.Graph
