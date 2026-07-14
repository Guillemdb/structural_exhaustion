import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic
import StructuralExhaustion.Graph.FiniteObject
import StructuralExhaustion.Graph.WalkMapping

namespace StructuralExhaustion.Graph

open StructuralExhaustion

universe u

/-!
# Contraction of a bridge

This file owns the graph mathematics behind the standard minimal-counterexample
reduction at a bridge.  The construction removes the second endpoint and
reattaches its remaining incident edges to the first endpoint.  Under the
`IsBridge` hypothesis no neighbour is lost, the minimum degree is preserved,
and every simple cycle of the contraction lifts to a simple cycle of exactly
the same length in the source graph.

Nothing in this file enumerates graphs, cycles, paths, or connected
components.  The only executable data added by `finiteObject` is the source
vertex schedule filtered once at the removed endpoint.
-/

namespace BridgeContraction

variable {V : Type u}

/-- Vertex type after identifying `v` with `u`, represented by deleting the
name `v`. -/
abbrev Vertex (v : V) := {x : V // x ≠ v}

/-- The surviving name of the contracted vertex. -/
def center (u v : V) (huv : u ≠ v) : Vertex v := ⟨u, huv⟩

/-- Explicit adjacency relation for contracting `uv` and deleting the loop
created by that edge. -/
def graph (G : SimpleGraph V) (u v : V) : SimpleGraph (Vertex v) where
  Adj x y := x ≠ y ∧
    (G.Adj x.1 y.1 ∨
      (x.1 = u ∧ G.Adj v y.1) ∨
      (y.1 = u ∧ G.Adj x.1 v))
  symm.symm := by
    intro x y adjacency
    refine ⟨adjacency.1.symm, ?_⟩
    rcases adjacency.2 with direct | fromV | toV
    · exact Or.inl direct.symm
    · exact Or.inr (Or.inr ⟨fromV.1, fromV.2.symm⟩)
    · exact Or.inr (Or.inl ⟨toV.1, toV.2.symm⟩)
  loopless.irrefl := by
    intro x adjacency
    exact adjacency.1 rfl

@[simp]
theorem graph_adj {G : SimpleGraph V} {u v : V}
    {x y : Vertex v} :
    (graph G u v).Adj x y ↔ x ≠ y ∧
      (G.Adj x.1 y.1 ∨
        (x.1 = u ∧ G.Adj v y.1) ∨
        (y.1 = u ∧ G.Adj x.1 v)) :=
  Iff.rfl

/-- Collapse the removed endpoint onto the surviving endpoint. -/
def collapse [DecidableEq V] (u v : V) (huv : u ≠ v) (x : V) : Vertex v :=
  if h : x = v then center u v huv else ⟨x, h⟩

@[simp]
theorem collapse_v [DecidableEq V] (u v : V) (huv : u ≠ v) :
    collapse u v huv v = center u v huv := by
  simp [collapse]

@[simp]
theorem collapse_of_ne [DecidableEq V] (u v : V) (huv : u ≠ v)
    {x : V} (hx : x ≠ v) :
    collapse u v huv x = ⟨x, hx⟩ := by
  simp [collapse, hx]

private theorem bridge_forbids_common_neighbor
    {G : SimpleGraph V} {u v w : V}
    (bridge : G.IsBridge s(u, v))
    (uw : G.Adj u w) (vw : G.Adj v w) : False := by
  have huv : u ≠ v := by
    have noReach := (SimpleGraph.isBridge_iff).mp bridge
    intro equality
    subst v
    exact noReach SimpleGraph.Reachable.rfl
  apply bridge
  rw [SimpleGraph.reachable_deleteEdges_iff_exists_walk]
  refine ⟨SimpleGraph.Walk.cons uw (SimpleGraph.Walk.cons vw.symm .nil), ?_⟩
  simp [huv, huv.symm, uw.ne, vw.ne]

/-- Away from the contracted vertex, contraction adjacency is exactly source
adjacency. -/
theorem adj_away_from_center
    {G : SimpleGraph V} {u v : V} (huv : u ≠ v)
    {x y : Vertex v}
    (hx : x ≠ center u v huv) (hy : y ≠ center u v huv) :
    (graph G u v).Adj x y ↔ G.Adj x.1 y.1 := by
  rw [graph_adj]
  constructor
  · rintro ⟨_, direct | fromV | toV⟩
    · exact direct
    · exfalso
      apply hx
      exact Subtype.ext fromV.1
    · exfalso
      apply hy
      exact Subtype.ext toV.1
  · intro adjacent
    exact ⟨fun equality => G.loopless.irrefl _ (equality ▸ adjacent),
      Or.inl adjacent⟩

/-- Adjacency at the contracted vertex comes from one of the two original
endpoints. -/
theorem center_adj_iff
    {G : SimpleGraph V} {u v : V} (huv : u ≠ v)
    {x : Vertex v} :
    (graph G u v).Adj (center u v huv) x ↔
      x ≠ center u v huv ∧ (G.Adj u x.1 ∨ G.Adj v x.1) := by
  rw [graph_adj]
  constructor
  · rintro ⟨different, direct | fromV | toV⟩
    · exact ⟨different.symm, Or.inl direct⟩
    · exact ⟨different.symm, Or.inr fromV.2⟩
    · exact ⟨different.symm, Or.inr (toV.1 ▸ toV.2.symm)⟩
  · rintro ⟨different, adjacent⟩
    refine ⟨different.symm, ?_⟩
    · rcases adjacent with direct | fromV
      · exact Or.inl direct
      · exact Or.inr (Or.inl ⟨rfl, fromV⟩)

/-- The contracted graph with the source inspection order filtered at the
removed endpoint. -/
def finiteObject (object : FiniteObject V) (u v : V) :
    FiniteObject (Vertex v) where
  graph := graph object.graph u v
  input := {
    vertices := Core.Enumeration.subtype object.input.vertices
      (fun x => x ≠ v) (by
        letI : DecidableEq V := object.input.vertices.decEq
        infer_instance)
    decideAdj := by
      letI : DecidableEq V := object.input.vertices.decEq
      letI : DecidableRel object.graph.Adj := object.input.decideAdj
      intro x y
      change Decidable (x ≠ y ∧
        (object.graph.Adj x.1 y.1 ∨
          (x.1 = u ∧ object.graph.Adj v y.1) ∨
          (y.1 = u ∧ object.graph.Adj x.1 v)))
      infer_instance
  }

/-- Contracting distinct endpoints removes exactly one vertex, in particular
it strictly lowers the packed vertex count. -/
theorem vertexCount_lt (object : FiniteObject V) (u v : V) :
    (finiteObject object u v).input.vertices.card <
      object.input.vertices.card := by
  letI : FinEnum V := object.input.vertices
  letI : FinEnum (Vertex v) := (finiteObject object u v).input.vertices
  simpa [FinEnum.card_eq_fintypeCard] using
    (Fintype.card_subtype_lt (p := fun x : V => x ≠ v) (x := v) (by simp))

private theorem collapse_eq_of_ne [DecidableEq V]
    (u v : V) (huv : u ≠ v) {x y : V}
    (hx : x ≠ v) (hy : y ≠ v)
    (equality : collapse u v huv x = collapse u v huv y) : x = y := by
  rw [collapse_of_ne u v huv hx, collapse_of_ne u v huv hy] at equality
  exact congrArg Subtype.val equality

/-- Every noncentral source neighbour survives injectively at the
corresponding contracted vertex. -/
theorem degree_le_degree_away
    (object : FiniteObject V) {u v : V} (huv : u ≠ v)
    (bridge : object.graph.IsBridge s(u, v))
    (x : Vertex v) (hx : x ≠ center u v huv) :
    object.degree x.1 ≤ (finiteObject object u v).degree x := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : FinEnum (Vertex v) := (finiteObject object u v).input.vertices
  letI : DecidableRel (graph object.graph u v).Adj :=
    (finiteObject object u v).input.decideAdj
  let f : V → Vertex v := collapse u v huv
  have maps : ∀ y ∈ object.graph.neighborFinset x.1,
      f y ∈ (graph object.graph u v).neighborFinset x := by
    intro y hy
    have adjacent : object.graph.Adj x.1 y := by simpa using hy
    by_cases hyv : y = v
    · subst y
      rw [SimpleGraph.mem_neighborFinset]
      simp only [f, collapse_v]
      exact ((center_adj_iff huv).2
        ⟨hx, Or.inr adjacent.symm⟩).symm
    · rw [SimpleGraph.mem_neighborFinset]
      simp only [f, collapse_of_ne u v huv hyv]
      rw [graph_adj]
      exact ⟨fun equality => adjacent.ne (Subtype.ext_iff.mp equality),
        Or.inl adjacent⟩
  have injective : Set.InjOn f
      (object.graph.neighborFinset x.1 : Set V) := by
    intro a ha b hb equality
    have adjacentA : object.graph.Adj x.1 a := by simpa using ha
    have adjacentB : object.graph.Adj x.1 b := by simpa using hb
    by_cases hav : a = v
    · subst a
      by_cases hbv : b = v
      · exact hbv.symm
      · have hbu : b = u := by
          have equality' : center u v huv = ⟨b, hbv⟩ := by
            simpa only [f, collapse_v, collapse_of_ne u v huv hbv] using
              equality
          exact (congrArg Subtype.val equality').symm
        subst b
        exact (bridge_forbids_common_neighbor bridge adjacentB.symm
          adjacentA.symm).elim
    · by_cases hbv : b = v
      · subst b
        have hau : a = u := by
          have equality' : (⟨a, hav⟩ : Vertex v) = center u v huv := by
            simpa only [f, collapse_v, collapse_of_ne u v huv hav] using
              equality
          exact congrArg Subtype.val equality'
        subst a
        exact (bridge_forbids_common_neighbor bridge adjacentA.symm
          adjacentB.symm).elim
      · exact collapse_eq_of_ne u v huv hav hbv equality
  have setMaps : ∀ y ∈ object.graph.neighborSet x.1,
      f y ∈ (graph object.graph u v).neighborSet x := by
    intro y hy
    simpa using maps y (by simpa using hy)
  have setInjective : Set.InjOn f (object.graph.neighborSet x.1) := by
    intro a ha b hb equality
    exact injective (by simpa using ha) (by simpa using hb) equality
  rw [object.degree_eq_ncard_neighborSet,
    (finiteObject object u v).degree_eq_ncard_neighborSet]
  simpa only [finiteObject] using
    Set.ncard_le_ncard_of_injOn f setMaps setInjective

/-- At the contracted vertex the two endpoint neighbourhoods, with the
bridge edge removed, inject disjointly into the new neighbourhood. -/
theorem bound_le_degree_center
    (object : FiniteObject V) {u v : V} (adjacent : object.graph.Adj u v)
    (bridge : object.graph.IsBridge s(u, v))
    (bound : Nat) (boundAtLeastTwo : 2 ≤ bound)
    (baseline : bound ≤ object.minDegree) :
    bound ≤ (finiteObject object u v).degree
      (center u v adjacent.ne) := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : FinEnum (Vertex v) := (finiteObject object u v).input.vertices
  letI : DecidableRel (graph object.graph u v).Adj :=
    (finiteObject object u v).input.decideAdj
  let left := (object.graph.neighborFinset u).erase v
  let right := (object.graph.neighborFinset v).erase u
  let domain := left.disjSum right
  let f : Sum V V → Vertex v
    | .inl x => collapse u v adjacent.ne x
    | .inr x => collapse u v adjacent.ne x
  have maps : ∀ x ∈ domain,
      f x ∈ (graph object.graph u v).neighborFinset
        (center u v adjacent.ne) := by
    intro x hx
    rw [SimpleGraph.mem_neighborFinset, center_adj_iff]
    rcases x with x | x
    · have hx' : x ∈ left := by simpa [domain] using hx
      have xneV : x ≠ v := (Finset.mem_erase.mp hx').1
      have ux : object.graph.Adj u x := by
        simpa [left] using (Finset.mem_erase.mp hx').2
      rw [show f (Sum.inl x) = (⟨x, xneV⟩ : Vertex v) by
        simp [f, collapse_of_ne u v adjacent.ne xneV]]
      exact ⟨fun equality => ux.ne (Subtype.ext_iff.mp equality).symm,
        Or.inl ux⟩
    · have hx' : x ∈ right := by simpa [domain] using hx
      have xneU : x ≠ u := (Finset.mem_erase.mp hx').1
      have vx : object.graph.Adj v x := by
        simpa [right] using (Finset.mem_erase.mp hx').2
      have xneV : x ≠ v := vx.ne.symm
      rw [show f (Sum.inr x) = (⟨x, xneV⟩ : Vertex v) by
        simp [f, collapse_of_ne u v adjacent.ne xneV]]
      exact ⟨fun equality => xneU (Subtype.ext_iff.mp equality),
        Or.inr vx⟩
  have injective : Set.InjOn f (domain : Set (Sum V V)) := by
    intro a ha b hb equality
    rcases a with a | a <;> rcases b with b | b
    · have ha' : a ∈ left := by simpa [domain] using ha
      have hb' : b ∈ left := by simpa [domain] using hb
      have ane : a ≠ v := (Finset.mem_erase.mp ha').1
      have bne : b ≠ v := (Finset.mem_erase.mp hb').1
      congr 1
      exact collapse_eq_of_ne u v adjacent.ne ane bne equality
    · have ha' : a ∈ left := by simpa [domain] using ha
      have hb' : b ∈ right := by simpa [domain] using hb
      have ane : a ≠ v := (Finset.mem_erase.mp ha').1
      have bne : b ≠ v := by
        have vb : object.graph.Adj v b := by
          simpa [right] using (Finset.mem_erase.mp hb').2
        exact vb.ne.symm
      have ab : a = b := collapse_eq_of_ne u v adjacent.ne ane bne equality
      subst b
      have ua : object.graph.Adj u a := by
        simpa [left] using (Finset.mem_erase.mp ha').2
      have va : object.graph.Adj v a := by
        simpa [right] using (Finset.mem_erase.mp hb').2
      exact (bridge_forbids_common_neighbor bridge ua va).elim
    · have ha' : a ∈ right := by simpa [domain] using ha
      have hb' : b ∈ left := by simpa [domain] using hb
      have ane : a ≠ v := by
        have va : object.graph.Adj v a := by
          simpa [right] using (Finset.mem_erase.mp ha').2
        exact va.ne.symm
      have bne : b ≠ v := (Finset.mem_erase.mp hb').1
      have ab : a = b := collapse_eq_of_ne u v adjacent.ne ane bne equality
      subst b
      have va : object.graph.Adj v a := by
        simpa [right] using (Finset.mem_erase.mp ha').2
      have ua : object.graph.Adj u a := by
        simpa [left] using (Finset.mem_erase.mp hb').2
      exact (bridge_forbids_common_neighbor bridge ua va).elim
    · have ha' : a ∈ right := by simpa [domain] using ha
      have hb' : b ∈ right := by simpa [domain] using hb
      have ane : a ≠ v := by
        have va : object.graph.Adj v a := by
          simpa [right] using (Finset.mem_erase.mp ha').2
        exact va.ne.symm
      have bne : b ≠ v := by
        have vb : object.graph.Adj v b := by
          simpa [right] using (Finset.mem_erase.mp hb').2
        exact vb.ne.symm
      congr 1
      exact collapse_eq_of_ne u v adjacent.ne ane bne equality
  have cardDomain : domain.card ≤
      ((graph object.graph u v).neighborFinset
        (center u v adjacent.ne)).card :=
    Finset.card_le_card_of_injOn f maps injective
  have leftCard : left.card + 1 = object.graph.degree u := by
    simpa [left] using Finset.card_erase_add_one
      (s := object.graph.neighborFinset u) (by simpa using adjacent)
  have rightCard : right.card + 1 = object.graph.degree v := by
    simpa [right] using Finset.card_erase_add_one
      (s := object.graph.neighborFinset v) (by simpa using adjacent.symm)
  have boundU : bound ≤ object.graph.degree u :=
    baseline.trans (object.minDegree_le_degree u)
  have boundV : bound ≤ object.graph.degree v :=
    baseline.trans (object.minDegree_le_degree v)
  have boundDomain : bound ≤ domain.card := by
    rw [Finset.card_disjSum]
    omega
  rw [(finiteObject object u v).degree_eq_ncard_neighborSet]
  have cardDomain' : domain.card ≤
      ((graph object.graph u v).neighborSet
        (center u v adjacent.ne)).ncard := by
    rw [Set.ncard_eq_toFinset_card']
    exact cardDomain
  exact boundDomain.trans cardDomain'

/-- Contracting a genuine bridge preserves every minimum-degree bound at
least two. -/
theorem preserves_minDegree
    (object : FiniteObject V) (dart : object.graph.Dart)
    (bridge : object.graph.IsBridge dart.edge)
    (bound : Nat) (boundAtLeastTwo : 2 ≤ bound)
    (baseline : bound ≤ object.minDegree) :
    bound ≤ (finiteObject object dart.fst dart.snd).minDegree := by
  have endpointsDifferent : dart.fst ≠ dart.snd := dart.adj.ne
  let contracted := finiteObject object dart.fst dart.snd
  let contractedCenter : Vertex dart.snd :=
    center dart.fst dart.snd endpointsDifferent
  letI : Nonempty (Vertex dart.snd) := ⟨contractedCenter⟩
  apply contracted.le_minDegree_of_forall_le_degree bound
  intro x
  by_cases hx : x = contractedCenter
  · subst x
    exact bound_le_degree_center object dart.adj bridge bound
      boundAtLeastTwo baseline
  · have sourceBound : bound ≤ object.degree x.1 :=
      baseline.trans (object.minDegree_le_degree x.1)
    exact sourceBound.trans
      (degree_le_degree_away object endpointsDifferent bridge x hx)

/-! ## Exact cycle transport -/

/-- Replace the contracted vertex by a chosen original endpoint and leave all
other surviving names unchanged. -/
noncomputable def liftVertex (u v : V) (huv : u ≠ v) (chosen : V)
    (x : Vertex v) : V :=
  @ite V (x = center u v huv)
    (@Classical.decEq (Vertex v) x (center u v huv))
    chosen x.1

@[simp]
theorem liftVertex_center (u v : V) (huv : u ≠ v) (chosen : V) :
    liftVertex u v huv chosen (center u v huv) = chosen := by
  simp [liftVertex]

theorem liftVertex_of_ne (u v : V) (huv : u ≠ v) (chosen : V)
    {x : Vertex v} (hx : x ≠ center u v huv) :
    liftVertex u v huv chosen x = x.1 := by
  simp [liftVertex, hx]

theorem liftVertex_u_injective (u v : V) (huv : u ≠ v) :
    Function.Injective (liftVertex u v huv u) := by
  intro x y equality
  by_cases hx : x = center u v huv
  · subst x
    by_cases hy : y = center u v huv
    · exact hy.symm
    · have : y.1 = u := by
        simpa [liftVertex_of_ne u v huv u hy] using equality.symm
      exact (hy (Subtype.ext this)).elim
  · by_cases hy : y = center u v huv
    · subst y
      have : x.1 = u := by
        simpa [liftVertex_of_ne u v huv u hx] using equality
      exact (hx (Subtype.ext this)).elim
    · apply Subtype.ext
      simpa [liftVertex_of_ne u v huv u hx,
        liftVertex_of_ne u v huv u hy] using equality

theorem liftVertex_v_injective (u v : V) (huv : u ≠ v) :
    Function.Injective (liftVertex u v huv v) := by
  intro x y equality
  by_cases hx : x = center u v huv
  · subst x
    by_cases hy : y = center u v huv
    · exact hy.symm
    · have : y.1 = v := by
        simpa [liftVertex_of_ne u v huv v hy] using equality.symm
      exact (y.2 this).elim
  · by_cases hy : y = center u v huv
    · subst y
      have : x.1 = v := by
        simpa [liftVertex_of_ne u v huv v hx] using equality
      exact (x.2 this).elim
    · apply Subtype.ext
      simpa [liftVertex_of_ne u v huv v hx,
        liftVertex_of_ne u v huv v hy] using equality

theorem liftVertex_u_ne_v (u v : V) (huv : u ≠ v) (x : Vertex v) :
    liftVertex u v huv u x ≠ v := by
  by_cases hx : x = center u v huv
  · simp [hx, huv]
  · simpa [liftVertex_of_ne u v huv u hx] using x.2

theorem liftVertex_v_ne_u (u v : V) (huv : u ≠ v) (x : Vertex v) :
    liftVertex u v huv v x ≠ u := by
  by_cases hx : x = center u v huv
  · simp [hx, huv.symm]
  · intro equality
    have equality' : x.1 = u := by
      simpa [liftVertex_of_ne u v huv v hx] using equality
    exact hx (Subtype.ext equality')

private theorem edge_ne_bridge_of_range_ne_v
    {u v a b : V} (ha : a ≠ v) (hb : b ≠ v) :
    s(a, b) ≠ s(u, v) := by
  intro equality
  simp only [Sym2.eq_iff] at equality
  rcases equality with direct | swapped
  · exact hb direct.2
  · exact ha swapped.1

private theorem edge_ne_bridge_of_range_ne_u
    {u v a b : V} (ha : a ≠ u) (hb : b ≠ u) :
    s(a, b) ≠ s(u, v) := by
  intro equality
  simp only [Sym2.eq_iff] at equality
  rcases equality with direct | swapped
  · exact ha direct.1
  · exact hb swapped.2

private theorem cycle_edge_map
    {G : SimpleGraph V} {u v : V} (huv : u ≠ v)
    (walk : (graph G u v).Walk (center u v huv) (center u v huv))
    (cycle : walk.IsCycle) (chosen : V)
    (first : G.Adj chosen (walk.snd).1)
    (last : G.Adj chosen (walk.penultimate).1)
    {x y : Vertex v} (member : s(x, y) ∈ walk.edges) :
    G.Adj (liftVertex u v huv chosen x)
      (liftVertex u v huv chosen y) := by
  have adjacent : (graph G u v).Adj x y := walk.adj_of_mem_edges member
  have fromCenter : ∀ {z : Vertex v},
      s(center u v huv, z) ∈ walk.edges →
      G.Adj (liftVertex u v huv chosen (center u v huv))
        (liftVertex u v huv chosen z) := by
    intro z edgeMember
    have centerAdjacent : (graph G u v).Adj (center u v huv) z :=
      walk.adj_of_mem_edges edgeMember
    have subgraphAdjacent : walk.toSubgraph.Adj (center u v huv) z :=
      (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges).2 edgeMember
    have neighbor : z ∈ walk.toSubgraph.neighborSet (center u v huv) :=
      subgraphAdjacent
    rw [cycle.neighborSet_toSubgraph_endpoint] at neighbor
    rcases neighbor with equality | equality
    · subst z
      have sndNe : walk.snd ≠ center u v huv := centerAdjacent.ne.symm
      simpa [liftVertex_center,
        liftVertex_of_ne u v huv chosen sndNe] using first
    · subst z
      have penultimateNe : walk.penultimate ≠ center u v huv :=
        centerAdjacent.ne.symm
      simpa [liftVertex_center,
        liftVertex_of_ne u v huv chosen penultimateNe] using last
  by_cases hx : x = center u v huv
  · subst x
    exact fromCenter member
  · by_cases hy : y = center u v huv
    · subst y
      exact (fromCenter (Sym2.eq_swap ▸ member)).symm
    · simpa [liftVertex_of_ne u v huv chosen hx,
        liftVertex_of_ne u v huv chosen hy] using
        (adj_away_from_center huv hx hy).1 adjacent

private theorem prefix_edge_map
    {G : SimpleGraph V} {u v : V} (huv : u ≠ v)
    (walk : (graph G u v).Walk (center u v huv) (center u v huv))
    (cycle : walk.IsCycle) (chosen : V)
    (first : G.Adj chosen (walk.snd).1)
    {x y : Vertex v} (member : s(x, y) ∈ walk.edges)
    (notLast : s(x, y) ≠ s(walk.penultimate, center u v huv)) :
    G.Adj (liftVertex u v huv chosen x)
      (liftVertex u v huv chosen y) := by
  have adjacent : (graph G u v).Adj x y := walk.adj_of_mem_edges member
  have fromCenter : ∀ {z : Vertex v},
      s(center u v huv, z) ∈ walk.edges →
      s(center u v huv, z) ≠
        s(walk.penultimate, center u v huv) →
      G.Adj (liftVertex u v huv chosen (center u v huv))
        (liftVertex u v huv chosen z) := by
    intro z edgeMember edgeNotLast
    have centerAdjacent : (graph G u v).Adj (center u v huv) z :=
      walk.adj_of_mem_edges edgeMember
    have subgraphAdjacent : walk.toSubgraph.Adj (center u v huv) z :=
      (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges).2 edgeMember
    have neighbor : z ∈ walk.toSubgraph.neighborSet (center u v huv) :=
      subgraphAdjacent
    rw [cycle.neighborSet_toSubgraph_endpoint] at neighbor
    rcases neighbor with equality | equality
    · subst z
      have sndNe : walk.snd ≠ center u v huv := centerAdjacent.ne.symm
      simpa [liftVertex_center,
        liftVertex_of_ne u v huv chosen sndNe] using first
    · subst z
      exact (edgeNotLast (by simp [Sym2.eq_swap])).elim
  by_cases hx : x = center u v huv
  · subst x
    exact fromCenter member notLast
  · by_cases hy : y = center u v huv
    · subst y
      apply (fromCenter (Sym2.eq_swap ▸ member) ?_).symm
      intro equality
      exact notLast (Sym2.eq_swap ▸ equality)
    · simpa [liftVertex_of_ne u v huv chosen hx,
        liftVertex_of_ne u v huv chosen hy] using
        (adj_away_from_center huv hx hy).1 adjacent

private theorem mixed_u_v_impossible
    {G : SimpleGraph V} {u v : V} (adjacent : G.Adj u v)
    (bridge : G.IsBridge s(u, v))
    (walk : (graph G u v).Walk (center u v adjacent.ne)
      (center u v adjacent.ne))
    (cycle : walk.IsCycle)
    (firstU : G.Adj u (walk.snd).1)
    (lastV : G.Adj v (walk.penultimate).1) : False := by
  let initialWalk := walk.dropLast
  have lastContracted : (graph G u v).Adj walk.penultimate
      (center u v adjacent.ne) := walk.adj_penultimate cycle.not_nil
  have decomposition : initialWalk.concat lastContracted = walk := by
    exact walk.concat_dropLast lastContracted
  have lastNotPrefix : s(walk.penultimate, center u v adjacent.ne) ∉
      initialWalk.edges := by
    have nodup := cycle.edges_nodup
    rw [← decomposition, SimpleGraph.Walk.edges_concat] at nodup
    rw [List.concat_eq_append] at nodup
    intro member
    have disjoint := List.disjoint_of_nodup_append nodup
    exact (List.disjoint_iff_ne.mp disjoint _ member _ (by simp)) rfl
  have mapsPrefix : ∀ {x y : Vertex v}, s(x, y) ∈ initialWalk.edges →
      (G.deleteEdges {s(u, v)}).Adj
        (liftVertex u v adjacent.ne u x)
        (liftVertex u v adjacent.ne u y) := by
    intro x y member
    have memberWalk : s(x, y) ∈ walk.edges := by
      rw [← decomposition, SimpleGraph.Walk.edges_concat]
      simp [initialWalk, member]
    have notLast : s(x, y) ≠
        s(walk.penultimate, center u v adjacent.ne) := by
      intro equality
      exact lastNotPrefix (equality ▸ member)
    rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
    exact ⟨prefix_edge_map adjacent.ne walk cycle u firstU memberWalk notLast,
      edge_ne_bridge_of_range_ne_v
        (liftVertex_u_ne_v u v adjacent.ne x)
        (liftVertex_u_ne_v u v adjacent.ne y)⟩
  let mappedPrefix := WalkMapping.mapVertices initialWalk
    (liftVertex u v adjacent.ne u) mapsPrefix
  have penultimateNeCenter : walk.penultimate ≠ center u v adjacent.ne :=
    lastContracted.ne
  have penultimateNeU : (walk.penultimate).1 ≠ u := by
    intro equality
    exact penultimateNeCenter (Subtype.ext equality)
  have lastDeleted : (G.deleteEdges {s(u, v)}).Adj
      (walk.penultimate).1 v := by
    rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
    refine ⟨lastV.symm, ?_⟩
    intro equality
    simp only [Sym2.eq_iff] at equality
    rcases equality with direct | swapped
    · exact penultimateNeU direct.1
    · exact walk.penultimate.2 swapped.1
  have forbiddenReachability :
      (G.deleteEdges {s(u, v)}).Reachable u v := by
    have lastMapped : (G.deleteEdges {s(u, v)}).Adj
        (liftVertex u v adjacent.ne u walk.penultimate) v := by
      simpa [liftVertex_of_ne u v adjacent.ne u penultimateNeCenter] using
        lastDeleted
    let completed := mappedPrefix.concat lastMapped
    exact ⟨completed.copy (by simp [liftVertex_center]) rfl⟩
  exact ((SimpleGraph.isBridge_iff).mp bridge) forbiddenReachability

private theorem mixed_v_u_impossible
    {G : SimpleGraph V} {u v : V} (adjacent : G.Adj u v)
    (bridge : G.IsBridge s(u, v))
    (walk : (graph G u v).Walk (center u v adjacent.ne)
      (center u v adjacent.ne))
    (cycle : walk.IsCycle)
    (firstV : G.Adj v (walk.snd).1)
    (lastU : G.Adj u (walk.penultimate).1) : False := by
  let initialWalk := walk.dropLast
  have lastContracted : (graph G u v).Adj walk.penultimate
      (center u v adjacent.ne) := walk.adj_penultimate cycle.not_nil
  have decomposition : initialWalk.concat lastContracted = walk := by
    exact walk.concat_dropLast lastContracted
  have lastNotPrefix : s(walk.penultimate, center u v adjacent.ne) ∉
      initialWalk.edges := by
    have nodup := cycle.edges_nodup
    rw [← decomposition, SimpleGraph.Walk.edges_concat] at nodup
    rw [List.concat_eq_append] at nodup
    intro member
    have disjoint := List.disjoint_of_nodup_append nodup
    exact (List.disjoint_iff_ne.mp disjoint _ member _ (by simp)) rfl
  have mapsPrefix : ∀ {x y : Vertex v}, s(x, y) ∈ initialWalk.edges →
      (G.deleteEdges {s(u, v)}).Adj
        (liftVertex u v adjacent.ne v x)
        (liftVertex u v adjacent.ne v y) := by
    intro x y member
    have memberWalk : s(x, y) ∈ walk.edges := by
      rw [← decomposition, SimpleGraph.Walk.edges_concat]
      simp [initialWalk, member]
    have notLast : s(x, y) ≠
        s(walk.penultimate, center u v adjacent.ne) := by
      intro equality
      exact lastNotPrefix (equality ▸ member)
    rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
    exact ⟨prefix_edge_map adjacent.ne walk cycle v firstV memberWalk notLast,
      edge_ne_bridge_of_range_ne_u
        (liftVertex_v_ne_u u v adjacent.ne x)
        (liftVertex_v_ne_u u v adjacent.ne y)⟩
  let mappedPrefix := WalkMapping.mapVertices initialWalk
    (liftVertex u v adjacent.ne v) mapsPrefix
  have penultimateNeCenter : walk.penultimate ≠ center u v adjacent.ne :=
    lastContracted.ne
  have penultimateNeU : (walk.penultimate).1 ≠ u := by
    intro equality
    exact penultimateNeCenter (Subtype.ext equality)
  have lastDeleted : (G.deleteEdges {s(u, v)}).Adj
      (walk.penultimate).1 u := by
    rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
    refine ⟨lastU.symm, ?_⟩
    intro equality
    simp only [Sym2.eq_iff] at equality
    rcases equality with direct | swapped
    · exact penultimateNeU direct.1
    · exact walk.penultimate.2 swapped.1
  have forbiddenReachability :
      (G.deleteEdges {s(u, v)}).Reachable v u := by
    have lastMapped : (G.deleteEdges {s(u, v)}).Adj
        (liftVertex u v adjacent.ne v walk.penultimate) u := by
      simpa [liftVertex_of_ne u v adjacent.ne v penultimateNeCenter] using
        lastDeleted
    let completed := mappedPrefix.concat lastMapped
    exact ⟨completed.copy (by simp [liftVertex_center]) rfl⟩
  exact ((SimpleGraph.isBridge_iff).mp bridge)
    forbiddenReachability.symm

/-- The two cycle edges at the contracted vertex originate at the same
source endpoint. -/
inductive CycleSide {G : SimpleGraph V} {u v : V} (adjacent : G.Adj u v)
    (walk : (graph G u v).Walk (center u v adjacent.ne)
      (center u v adjacent.ne)) : Prop where
  | fst (first : G.Adj u (walk.snd).1)
      (last : G.Adj u (walk.penultimate).1) : CycleSide adjacent walk
  | snd (first : G.Adj v (walk.snd).1)
      (last : G.Adj v (walk.penultimate).1) : CycleSide adjacent walk

theorem cycleSide_of_bridge
    {G : SimpleGraph V} {u v : V} (adjacent : G.Adj u v)
    (bridge : G.IsBridge s(u, v))
    (walk : (graph G u v).Walk (center u v adjacent.ne)
      (center u v adjacent.ne))
    (cycle : walk.IsCycle) : CycleSide adjacent walk := by
  have firstContracted : (graph G u v).Adj (center u v adjacent.ne)
      walk.snd := walk.toSubgraph_adj_snd cycle.not_nil |>.adj_sub
  have lastContracted : (graph G u v).Adj (center u v adjacent.ne)
      walk.penultimate :=
    (walk.toSubgraph_adj_penultimate cycle.not_nil |>.adj_sub).symm
  have firstSide := ((center_adj_iff adjacent.ne).mp firstContracted).2
  have lastSide := ((center_adj_iff adjacent.ne).mp lastContracted).2
  rcases firstSide with firstU | firstV <;>
    rcases lastSide with lastU | lastV
  · exact .fst firstU lastU
  · exact (mixed_u_v_impossible adjacent bridge walk cycle firstU lastV).elim
  · exact (mixed_v_u_impossible adjacent bridge walk cycle firstV lastU).elim
  · exact .snd firstV lastV

/-- Every cycle of a bridge contraction lifts to a source cycle of exactly
the same length. -/
theorem hasCycleWithLength_of_contraction
    {G : SimpleGraph V} {u v : V} (adjacent : G.Adj u v)
    (bridge : G.IsBridge s(u, v)) {LengthOK : Nat → Prop} :
    HasCycleWithLength (graph G u v) LengthOK →
      HasCycleWithLength G LengthOK := by
  classical
  rintro ⟨certificate⟩
  by_cases centerMem : center u v adjacent.ne ∈ certificate.walk.support
  · let rotated := certificate.walk.rotate
        (center u v adjacent.ne) centerMem
    have rotatedCycle : rotated.IsCycle :=
      certificate.isCycle.rotate centerMem
    rcases cycleSide_of_bridge adjacent bridge rotated rotatedCycle with
      ⟨firstU, lastU⟩ | ⟨firstV, lastV⟩
    · let mapped := WalkMapping.mapVertices rotated
          (liftVertex u v adjacent.ne u)
          (fun {_ _} member =>
            cycle_edge_map adjacent.ne rotated rotatedCycle u
              firstU lastU member)
      exact ⟨{
        vertex := liftVertex u v adjacent.ne u (center u v adjacent.ne)
        walk := mapped
        isCycle := WalkMapping.isCycle_mapVertices rotatedCycle
          (liftVertex u v adjacent.ne u)
          (liftVertex_u_injective u v adjacent.ne) _
        length_ok := by
          simpa [mapped, rotated] using certificate.length_ok
      }⟩
    · let mapped := WalkMapping.mapVertices rotated
          (liftVertex u v adjacent.ne v)
          (fun {_ _} member =>
            cycle_edge_map adjacent.ne rotated rotatedCycle v
              firstV lastV member)
      exact ⟨{
        vertex := liftVertex u v adjacent.ne v (center u v adjacent.ne)
        walk := mapped
        isCycle := WalkMapping.isCycle_mapVertices rotatedCycle
          (liftVertex u v adjacent.ne v)
          (liftVertex_v_injective u v adjacent.ne) _
        length_ok := by
          simpa [mapped, rotated] using certificate.length_ok
      }⟩
  · let f : Vertex v → V := Subtype.val
    have maps : ∀ {x y : Vertex v}, s(x, y) ∈ certificate.walk.edges →
        G.Adj (f x) (f y) := by
      intro x y member
      have xMem := certificate.walk.fst_mem_support_of_mem_edges member
      have yMem := certificate.walk.snd_mem_support_of_mem_edges member
      have xNe : x ≠ center u v adjacent.ne := by
        intro equality
        exact centerMem (equality ▸ xMem)
      have yNe : y ≠ center u v adjacent.ne := by
        intro equality
        exact centerMem (equality ▸ yMem)
      exact (adj_away_from_center adjacent.ne xNe yNe).1
        (certificate.walk.adj_of_mem_edges member)
    let mapped := WalkMapping.mapVertices certificate.walk f maps
    exact ⟨{
      vertex := f certificate.vertex
      walk := mapped
      isCycle := WalkMapping.isCycle_mapVertices certificate.isCycle f
        Subtype.val_injective maps
      length_ok := by simpa [mapped] using certificate.length_ok
    }⟩

/-- Finite-object wrapper for exact cycle transport. -/
theorem finiteObject_targetMonotone
    (object : FiniteObject V) (dart : object.graph.Dart)
    (bridge : object.graph.IsBridge dart.edge)
    {LengthOK : Nat → Prop} :
    HasCycleWithLength (finiteObject object dart.fst dart.snd).graph LengthOK →
      HasCycleWithLength object.graph LengthOK :=
  hasCycleWithLength_of_contraction dart.adj bridge

end BridgeContraction

end StructuralExhaustion.Graph
