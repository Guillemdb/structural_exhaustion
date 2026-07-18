import StructuralExhaustion.Graph.PackedMinimumDegreeCycle
import StructuralExhaustion.Graph.TypeACanonicalReceiverTrace

namespace StructuralExhaustion.Graph.WalkTypeASupportProfile

open StructuralExhaustion

universe u

variable {V : Type u} (object : FiniteObject V)

/-- The literal finite support of one proof-selected walk. -/
noncomputable def support {left right : V}
    (walk : object.graph.Walk left right) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact walk.support.toFinset

theorem support_nonempty {left right : V}
    (walk : object.graph.Walk left right) :
    (support object walk).Nonempty := by
  refine ⟨left, ?_⟩
  simp [support]

/-- A walk support is connected by paths staying in that identical support.
The proof uses connectivity of the induced support and maps only its selected
path back to the host graph. -/
theorem connectedOn {left right : V}
    (walk : object.graph.Walk left right) :
    NegativeSupportHandoff.ConnectedOn object (support object walk) := by
  classical
  refine ⟨support_nonempty object walk, ?_⟩
  intro first second firstMem secondMem
  let first' : {v : V // v ∈ walk.support} :=
    ⟨first, by simpa [support] using firstMem⟩
  let second' : {v : V // v ∈ walk.support} :=
    ⟨second, by simpa [support] using secondMem⟩
  obtain ⟨path, pathIsPath⟩ :=
    walk.connected_induce_support.exists_isPath first' second'
  let inclusion : object.graph.induce {v | v ∈ walk.support} →g object.graph := {
    toFun := fun vertex ↦ vertex.1
    map_rel' := by intro _ _ adjacent; exact adjacent
  }
  refine ⟨path.map inclusion, SimpleGraph.Walk.map_isPath_of_injective
    Subtype.val_injective pathIsPath, ?_⟩
  intro vertex member
  rw [SimpleGraph.Walk.support_map] at member
  rcases List.mem_map.mp member with ⟨inside, insideMem, rfl⟩
  rw [show inclusion inside = inside.1 by rfl]
  have insideProp := inside.2
  change inside.1 ∈ walk.support at insideProp
  simpa only [support, List.mem_toFinset] using insideProp

/-- A proper walk support in a packed minimal counterexample is internally
three-core-free.  This is node-[8]'s no-proper-core theorem applied to the
literal induced support; no subgraph family is searched. -/
theorem internalCoreFree
    {input : PackedMinimumDegreeCycle.StaticInput}
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    {left right : ctx.G.Vertex}
    (walk : ctx.G.object.graph.Walk left right)
    (minimumDegree_eq : input.minimumDegree = 3)
    (outside : ctx.G.Vertex)
    (outsideNotMem : outside ∉ support ctx.G.object walk) :
    (ctx.G.object.induceFinset (support ctx.G.object walk)).InternalMinDegreeFree 3 := by
  classical
  have supportStrict : (support ctx.G.object walk).card < ctx.G.vertexCount := by
    rw [PackedFiniteObject.vertexCount, ← ctx.G.object.card_vertexFinset]
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro vertex _
      exact ctx.G.object.mem_vertexFinset vertex
    · intro equal
      exact outsideNotMem (equal ▸ ctx.G.object.mem_vertexFinset outside)
  apply PackedFiniteObject.ProperSubgraph.internalMinDegreeFree_induceFinset_of_noProperCore
    ctx.G 3 (support ctx.G.object walk) supportStrict
  intro subgraph minimumThree
  apply input.noProperCore ctx subgraph
  change input.minimumDegree ≤ subgraph.value.object.minDegree
  rw [minimumDegree_eq]
  exact minimumThree

/-- Inducing on a finite support cannot increase a supported vertex's degree.
The proof compares exact neighbor sets and is independent of the particular
finite enumeration instances used on the two sides. -/
theorem inducedDegree_le_ambient (vertices : Finset V)
    (vertex : {value : V // value ∈ vertices}) :
    (object.induceFinset vertices).degree vertex ≤ object.degree vertex.1 := by
  letI : FinEnum V := object.input.vertices
  rw [(object.induceFinset vertices).degree_eq_ncard_neighborSet,
    object.degree_eq_ncard_neighborSet]
  rw [← Set.ncard_image_of_injective
    ((object.induceFinset vertices).graph.neighborSet vertex)
      Subtype.val_injective]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro neighbor ⟨inside, adjacent, rfl⟩
  exact adjacent

/-- Construct the complete D5 Type-A ownership profile on one actual walk
support after the local high-center scan has certified ambient cubicity.
Connectivity, the internal degree bound, and core-freeness are derived. -/
noncomputable def profile
    {input : PackedMinimumDegreeCycle.StaticInput}
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    {left right : ctx.G.Vertex}
    (walk : ctx.G.object.graph.Walk left right)
    (minimumDegree_eq : input.minimumDegree = 3)
    (ambientCubic : ∀ vertex ∈ support ctx.G.object walk,
      ctx.G.object.degree vertex = 3)
    (outside : ctx.G.Vertex)
    (outsideNotMem : outside ∉ support ctx.G.object walk) :
    TypeACanonicalReceiverTrace.SupportProfile ctx.G.object where
  support := support ctx.G.object walk
  connected := connectedOn ctx.G.object walk
  ambient_cubic := ambientCubic
  degree_le_three := fun vertex ↦
    (inducedDegree_le_ambient ctx.G.object
      (support ctx.G.object walk) vertex).trans_eq
        (ambientCubic vertex.1 vertex.2)
  coreFree := internalCoreFree ctx walk minimumDegree_eq outside outsideNotMem

end StructuralExhaustion.Graph.WalkTypeASupportProfile
