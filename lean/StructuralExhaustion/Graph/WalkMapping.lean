import Mathlib.Combinatorics.SimpleGraph.Paths

namespace StructuralExhaustion.Graph

universe u v

/-!
# Mapping one certified walk

Unlike `SimpleGraph.Walk.map`, this helper does not require a function to be a
homomorphism on every edge of the source graph.  It requires adjacency only on
the finitely many edges already present in the supplied walk.  This is useful
for local graph reductions whose vertex map is valid on one cycle but not on
all ambient chords.
-/

namespace WalkMapping

variable {V : Type u} {W : Type v}
variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Map the vertices of one walk, with an adjacency proof for each edge of
that walk. -/
def mapVertices {a b : V} (walk : G.Walk a b) (f : V → W)
    (mapsEdge : ∀ {x y : V}, s(x, y) ∈ walk.edges → H.Adj (f x) (f y)) :
    H.Walk (f a) (f b) :=
  match walk with
  | .nil => .nil
  | .cons adjacent rest =>
      .cons (mapsEdge (by simp))
        (mapVertices rest f (fun {_ _} member =>
          mapsEdge (by simp [member])))

@[simp]
theorem length_mapVertices {a b : V} (walk : G.Walk a b) (f : V → W)
    (mapsEdge : ∀ {x y : V}, s(x, y) ∈ walk.edges → H.Adj (f x) (f y)) :
    (mapVertices walk f mapsEdge).length = walk.length := by
  induction walk with
  | nil => rfl
  | cons adjacent rest induction =>
      simp only [mapVertices, SimpleGraph.Walk.length_cons]
      rw [induction]
      intro x y member
      exact mapsEdge (by simp [member])

@[simp]
theorem support_mapVertices {a b : V} (walk : G.Walk a b) (f : V → W)
    (mapsEdge : ∀ {x y : V}, s(x, y) ∈ walk.edges → H.Adj (f x) (f y)) :
    (mapVertices walk f mapsEdge).support = walk.support.map f := by
  induction walk with
  | nil => rfl
  | cons adjacent rest induction =>
      simp only [mapVertices, SimpleGraph.Walk.support_cons, List.map_cons,
        List.cons.injEq, true_and]
      rw [induction]
      intro x y member
      exact mapsEdge (by simp [member])

@[simp]
theorem edges_mapVertices {a b : V} (walk : G.Walk a b) (f : V → W)
    (mapsEdge : ∀ {x y : V}, s(x, y) ∈ walk.edges → H.Adj (f x) (f y)) :
    (mapVertices walk f mapsEdge).edges =
      walk.edges.map (Sym2.map f) := by
  induction walk with
  | nil => rfl
  | cons adjacent rest induction =>
      simp only [mapVertices, SimpleGraph.Walk.edges_cons, List.map_cons,
        Sym2.map_mk, List.cons.injEq, true_and]
      rw [induction]
      intro x y member
      exact mapsEdge (by simp [member])

/-- An injective vertex map preserves a simple cycle when it is known to map
the edges of that cycle. -/
theorem isCycle_mapVertices {a : V} {walk : G.Walk a a}
    (cycle : walk.IsCycle) (f : V → W) (injective : Function.Injective f)
    (mapsEdge : ∀ {x y : V}, s(x, y) ∈ walk.edges → H.Adj (f x) (f y)) :
    (mapVertices walk f mapsEdge).IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def] at cycle ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def, edges_mapVertices]
    exact cycle.1.edges_nodup.map (Sym2.map.injective injective)
  · intro equality
    have mappedNil : (mapVertices walk f mapsEdge).Nil := by
      rw [equality]
      exact SimpleGraph.Walk.Nil.nil
    have zero : (mapVertices walk f mapsEdge).length = 0 :=
      SimpleGraph.Walk.length_eq_zero_iff.mpr mappedNil
    rw [length_mapVertices] at zero
    exact cycle.2.1 (SimpleGraph.Walk.Nil.eq_nil
      (SimpleGraph.Walk.length_eq_zero_iff.mp zero))
  · rw [support_mapVertices]
    simpa using cycle.2.2.map injective

end WalkMapping

end StructuralExhaustion.Graph
