import Erdos64EG.CT1InducedP13
import StructuralExhaustion.Graph.External.HegdeSandeepShashank

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT12: maximum induced-`P₁₃` packing and remainder

This single structural stage covers manuscript node `[17]` and the
packing-derived clauses later displayed at nodes `[25]`--`[27]`:

* the selected family has maximum cardinality, defining `p₁₃`;
* maximum cardinality implies maximality, so every unselected window meets it;
* CT12 peels exactly the selected family to exhaustion with a vertex-linear
  iteration and trace bound;
* deleting the packed supports leaves an induced-`P₁₃`-free graph, and every
  induced subgraph of the remainder remains `P₁₃`-free; and
* HSS plus global target avoidance rules out every finite internal subgraph
  of minimum degree at least three in the remainder.

The later numerical assertion that the remainder is large depends on the
manuscript's window-density stage and is not part of this packing CT.
-/

private theorem thirteen_positive : 0 < 13 := by decide

/-- Reusable graph profile specialized to the selected packed graph and
thirteen-vertex path windows. -/
noncomputable def inducedP13PackingProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.InducedPathPacking.profile ctx.G.object 13 thirteen_positive

/-- One labelled induced-`P₁₃` window. -/
abbrev InducedP13Window
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.InducedPathPacking.Window ctx.G.object 13

/-- A finite pairwise vertex-disjoint family of induced-`P₁₃` windows. -/
abbrev InducedP13Packing
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.InducedPathPacking.Packing ctx.G.object 13 thirteen_positive

/-- The selected maximum family in CT12 peeling order. -/
noncomputable def p13Windows
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (InducedP13Window ctx) :=
  Graph.InducedPathPacking.windows ctx.G.object 13 thirteen_positive

/-- Manuscript parameter `p₁₃`, exactly the selected maximum packing size. -/
noncomputable def p13
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) : Nat :=
  Graph.InducedPathPacking.packingNumber ctx.G.object 13 thirteen_positive

/-- The union `W` of all packed window supports. -/
noncomputable def p13CoveredVertices
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Finset ctx.G.Vertex :=
  Graph.InducedPathPacking.coveredVertices ctx.G.object 13
    thirteen_positive

/-- Vertices of the manuscript remainder `R = G - W`. -/
noncomputable def p13RemainderVertices
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Finset ctx.G.Vertex :=
  Graph.InducedPathPacking.remainderVertices ctx.G.object 13
    thirteen_positive

/-- The actual finite induced remainder graph. -/
noncomputable def p13Remainder
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.InducedPathPacking.remainder ctx.G.object 13 thirteen_positive

/-- Vertex type of the induced remainder. -/
abbrev P13RemainderVertex
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  {vertex : ctx.G.Vertex // vertex ∈
    Graph.InducedPathPacking.remainderVertices ctx.G.object 13
      thirteen_positive}

/-! ## Exact CT12 execution -/

/-- CT12 audits exactly the selected maximum packing list. -/
noncomputable def runP13PackingCT12
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  (inducedP13PackingProfile ctx).run ctx.toBranchContext

theorem runP13PackingCT12_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runP13PackingCT12 ctx).terminal = .exhausted :=
  (inducedP13PackingProfile ctx).run_terminal_exhausted
    ctx.toBranchContext

theorem runP13PackingCT12_iterations
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runP13PackingCT12 ctx).iterations ≤ ctx.G.object.input.vertices.card :=
  (inducedP13PackingProfile ctx).run_iterations_le_vertices
    ctx.toBranchContext

/-- The executable CT12 schedule has exactly `p₁₃` local peeling steps. -/
theorem runP13PackingCT12_iterations_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runP13PackingCT12 ctx).iterations = p13 ctx :=
  (inducedP13PackingProfile ctx).run_iterations_eq_values
    ctx.toBranchContext

theorem runP13PackingCT12_trace_bound
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runP13PackingCT12 ctx).trace.length ≤
      4 * ctx.G.object.input.vertices.card + 3 :=
  (inducedP13PackingProfile ctx).run_trace_le_vertices ctx.toBranchContext

theorem runP13PackingCT12_verified
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runP13PackingCT12 ctx).outcome.Valid :=
  (inducedP13PackingProfile ctx).run_verified ctx.toBranchContext

/-! ## Maximum, maximal, and remainder clauses -/

/-- `p₁₃` is the maximum cardinality of a vertex-disjoint induced-`P₁₃`
family, not merely the size of a greedily maximal family. -/
theorem p13_maximum
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (other : InducedP13Packing ctx) :
    other.1.card ≤ p13 ctx :=
  Graph.InducedPathPacking.maximum ctx.G.object 13 thirteen_positive other

/-- The maximum family is maximal: every induced-`P₁₃` window intersects a
selected window. -/
theorem p13_saturated
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : InducedP13Window ctx) :
    ∃ selected ∈ p13Windows ctx,
      ¬Disjoint
        (Graph.InducedPathPacking.support ctx.G.object 13 window)
        (Graph.InducedPathPacking.support ctx.G.object 13 selected) :=
  Graph.InducedPathPacking.saturated ctx.G.object 13 thirteen_positive window

/-- Exact packed vertex count `|W| = 13 p₁₃`. -/
theorem p13CoveredVertices_card
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13CoveredVertices ctx).card = 13 * p13 ctx :=
  Graph.InducedPathPacking.coveredVertices_card ctx.G.object 13
    thirteen_positive

/-- Exact partition identity `|R| + 13 p₁₃ = n`. -/
theorem p13Remainder_partition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13RemainderVertices ctx).card + 13 * p13 ctx =
      ctx.G.object.input.vertices.card :=
  Graph.InducedPathPacking.remainder_partition ctx.G.object 13
    thirteen_positive

/-- Immediate packing bound `13 p₁₃ ≤ n`. -/
theorem thirteen_mul_p13_le_vertexCount
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    13 * p13 ctx ≤ ctx.G.object.input.vertices.card :=
  Graph.InducedPathPacking.packing_vertices_bound ctx.G.object 13
    thirteen_positive

/-- The remainder has no induced `P₁₃`. -/
theorem p13Remainder_free
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.InducedPathFree (p13Remainder ctx).graph 13 :=
  Graph.InducedPathPacking.remainder_free ctx.G.object 13 thirteen_positive

/-- Every induced subgraph of the remainder is `P₁₃`-free; this is the exact
componentwise inheritance needed by the manuscript. -/
theorem p13Remainder_componentwise_free
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (vertices : Set (P13RemainderVertex ctx)) :
    Graph.InducedPathFree ((p13Remainder ctx).graph.induce vertices) 13 :=
  Graph.InducedPathPacking.remainder_induce_free ctx.G.object 13
    thirteen_positive vertices

/-! ## Node [27]: no internal minimum-degree-three subgraph -/

/-- Any power-of-two cycle in the induced remainder maps injectively to the
selected ambient graph and contradicts its verified target avoidance. -/
theorem p13Remainder_avoidsPowerOfTwoCycle
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ¬Graph.HasCycleWithLength (p13Remainder ctx).graph (fun length =>
      ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent) := by
  intro remainderCycle
  let embedding : (p13Remainder ctx).graph ↪g ctx.G.object.graph :=
    Graph.InducedPathPacking.remainderEmbedding ctx.G.object 13
      thirteen_positive
  have ambientCycle := Graph.hasCycleWithLength_mapHom embedding.toHom
    embedding.injective remainderCycle
  exact ctx.avoids
    (target_of_unboundedPowerOfTwoCycle ctx.G.object ambientCycle)

/-- Induced-core form of the HSS consequence used by the arbitrary-subgraph
bridge below. -/
theorem p13Remainder_internalThreeCore_free
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13Remainder ctx).InternalMinDegreeFree 3 :=
  Graph.External.HegdeSandeepShashank.internalMinDegreeThree_free_of_p13Free
      (p13Remainder ctx)
      (p13Remainder_free ctx) (p13Remainder_avoidsPowerOfTwoCycle ctx)

/-- Exact manuscript clause: the remainder contains no ordinary finite
subgraph of minimum degree at least three. -/
theorem p13Remainder_internalSubgraphThreeCore_free
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ¬(p13Remainder ctx).HasInternalSubgraphMinDegreeAtLeast 3 :=
  Graph.External.HegdeSandeepShashank.internalSubgraphMinDegreeThree_free_of_p13Free
      (p13Remainder ctx)
      (p13Remainder_free ctx) (p13Remainder_avoidsPowerOfTwoCycle ctx)

/-! ## Fully connected verified prefix -/

/-- Generic graph/framework prefix for the maximum induced-`P₁₃` packing. -/
abbrev GenericP13PackingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  packedStaticInput.InducedPathPackingPrefix 13 thirteen_positive ctx

/-- Exact output of the CT12 stage, retaining nodes `[5]`--`[16]` and adding
all packing-derived clauses of `[17]`, `[25]`--`[27]` that are independent of
the later density estimate, including the arbitrary-subgraph form of the
minimum-degree-three exclusion. -/
structure VerifiedP13PackingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedInducedP13Prefix ctx
  generic : GenericP13PackingPrefix ctx
  noInternalThreeCore : (p13Remainder ctx).InternalMinDegreeFree 3
  noInternalSubgraphThreeCore :
    ¬(p13Remainder ctx).HasInternalSubgraphMinDegreeAtLeast 3

/-- Extend the exact HSS-forced CT1 prefix through CT12 on the same selected
minimal context. -/
noncomputable def verifiedP13PackingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedInducedP13Prefix ctx) :
    VerifiedP13PackingPrefix ctx where
  previous := previous
  generic :=
    packedStaticInput.inducedPathPackingPrefix 13 thirteen_positive ctx
      previous.inducedPathStage
  noInternalThreeCore := p13Remainder_internalThreeCore_free ctx
  noInternalSubgraphThreeCore :=
    p13Remainder_internalSubgraphThreeCore_free ctx

/-- Provenance: the CT12 result consumes and retains the exact preceding CT1
prefix. -/
theorem p13PackingPrefix_previous
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedP13PackingPrefix ctx) :
    VerifiedInducedP13Prefix ctx :=
  verified.previous

/-- The composed prefix contains the complete reusable graph-level CT12
stage. -/
theorem p13PackingPrefix_stage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedP13PackingPrefix ctx) :
    Graph.InducedPathPacking.VerifiedStage ctx.G.object 13 thirteen_positive
      ctx.toBranchContext :=
  verified.generic.packingStage

/-- The selected packing is nonempty because the preceding CT1 stage retains
an induced `P₁₃` realization. -/
theorem p13PackingPrefix_nonempty
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedP13PackingPrefix ctx) :
    p13Windows ctx ≠ [] :=
  verified.generic.packingNonempty

/-- Starting only from the official internal counterexample data, retain one
selected graph and the entire verified proof through this CT12 stage. -/
theorem exists_verifiedP13PackingPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedP13PackingPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedInducedP13Prefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedP13PackingPrefix ctx previous⟩

end Erdos64EG.Internal
