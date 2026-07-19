import Erdos64EG.CT6SparseSurplus
import StructuralExhaustion.Graph.DegeneracyPeeling

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT12: sparse upper envelope

This stage implements manuscript node `[126]`, Lemma
`lem:sparse-upper-envelope`.  Deletion criticality selects an actual cubic
vertex.  The no-proper-core theorem makes the graph remaining after that one
vertex deletion internally minimum-degree-three-free.  The reusable
degeneracy profile constructs a complete two-bounded elimination certificate
and CT12 checks that finite schedule with one local peeling step per remaining
vertex.  Its sharp edge theorem then gives `m ≤ 2n - 2` for the selected
minimal graph.
-/

/-- Deletion criticality and positive minimum degree provide an actual cubic
vertex of the selected graph. -/
private theorem exists_sparseEnvelopeRoot
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ∃ vertex : ctx.G.Vertex, ctx.G.object.degree vertex = 3 := by
  apply ctx.G.object.exists_vertex_degree_eq_of_dart_endpoints 3
  · have baseline := (packedStaticInput.fixedContext ctx).baseline
    change 3 ≤ ctx.G.object.minDegree at baseline
    omega
  · exact (fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx)

/-- Proof-selected cubic vertex used by the sparse-envelope argument. -/
noncomputable def sparseEnvelopeRoot
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ctx.G.Vertex :=
  Classical.choose (exists_sparseEnvelopeRoot ctx)

theorem sparseEnvelopeRoot_degree
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ctx.G.object.degree (sparseEnvelopeRoot ctx) = 3 :=
  Classical.choose_spec (exists_sparseEnvelopeRoot ctx)

/-- Exact remaining support after deleting the selected cubic vertex. -/
noncomputable def sparseEnvelopeSupport
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Finset ctx.G.Vertex :=
  @Finset.erase ctx.G.Vertex ctx.G.object.input.vertices.decEq
    ctx.G.object.vertexFinset (sparseEnvelopeRoot ctx)

/-- The finite induced graph on the remaining support. -/
noncomputable def sparseEnvelopeRemaining
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  ctx.G.object.induceFinset (sparseEnvelopeSupport ctx)

theorem sparseEnvelope_vertexCount_gt_three
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    3 < ctx.G.object.input.vertices.card := by
  rw [← sparseEnvelopeRoot_degree ctx]
  exact ctx.G.object.degree_lt_vertexCount (sparseEnvelopeRoot ctx)

theorem sparseEnvelopeSupport_card_add_one
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (sparseEnvelopeSupport ctx).card + 1 =
      ctx.G.object.input.vertices.card := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  unfold sparseEnvelopeSupport
  rw [Finset.card_erase_of_mem
    (ctx.G.object.mem_vertexFinset (sparseEnvelopeRoot ctx))]
  rw [ctx.G.object.card_vertexFinset]
  have countLarge := sparseEnvelope_vertexCount_gt_three ctx
  omega

theorem sparseEnvelopeSupport_strict
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (sparseEnvelopeSupport ctx).card < ctx.G.vertexCount := by
  change (sparseEnvelopeSupport ctx).card <
    ctx.G.object.input.vertices.card
  have recurrence := sparseEnvelopeSupport_card_add_one ctx
  omega

theorem sparseEnvelopeRemaining_vertexCount
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (sparseEnvelopeRemaining ctx).input.vertices.card + 1 =
      ctx.G.object.input.vertices.card := by
  change (ctx.G.object.induceFinset
      (sparseEnvelopeSupport ctx)).input.vertices.card + 1 = _
  calc
    (ctx.G.object.induceFinset
        (sparseEnvelopeSupport ctx)).input.vertices.card + 1 =
        (sparseEnvelopeSupport ctx).card + 1 := by
      rw [ctx.G.object.induceFinset_vertexCount]
    _ = ctx.G.object.input.vertices.card :=
      sparseEnvelopeSupport_card_add_one ctx

/-- Every induced subgraph of the remaining graph has a vertex of degree at
most two, derived from the already verified no-proper-core theorem. -/
theorem sparseEnvelopeRemaining_coreFree
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (sparseEnvelopeRemaining ctx).InternalMinDegreeFree 3 := by
  exact Graph.PackedFiniteObject.ProperSubgraph.internalMinDegreeFree_induceFinset_of_noProperCore
      ctx.G 3 (sparseEnvelopeSupport ctx)
      (sparseEnvelopeSupport_strict ctx)
      (packedStaticInput.noProperCore ctx)

/-- Reusable two-degenerate graph profile instantiated on the actual
remaining graph. -/
noncomputable def sparseEnvelopeProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.DegeneracyPeeling.Profile (sparseEnvelopeRemaining ctx) 2 where
  free := by
    simpa using sparseEnvelopeRemaining_coreFree ctx

def sparseEnvelopeContext
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Core.BranchContext ((fixedPackedInput ctx).problem) :=
  (packedStaticInput.fixedContext ctx).toBranchContext

/-- Exact CT12 execution on the proof-selected bounded elimination order. -/
noncomputable def runSparseEnvelopeCT12
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  (sparseEnvelopeProfile ctx).run (sparseEnvelopeContext ctx)

theorem runSparseEnvelopeCT12_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runSparseEnvelopeCT12 ctx).terminal = .exhausted :=
  ((sparseEnvelopeProfile ctx).verifiedStage
    (sparseEnvelopeContext ctx)).terminal

theorem runSparseEnvelopeCT12_trace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runSparseEnvelopeCT12 ctx).trace =
      CT12.ListPeeling.expectedTrace
        (sparseEnvelopeRemaining ctx).input.vertices.card :=
  ((sparseEnvelopeProfile ctx).verifiedStage
    (sparseEnvelopeContext ctx)).trace

theorem runSparseEnvelopeCT12_verified
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runSparseEnvelopeCT12 ctx).outcome.Valid :=
  ((sparseEnvelopeProfile ctx).verifiedStage
    (sparseEnvelopeContext ctx)).verified

theorem runSparseEnvelopeCT12_traceValid
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    CT12.Graph.ValidTrace
      (CT12.ListPeeling.capability
        ((fixedPackedInput ctx).problem)
          {vertex : ctx.G.Vertex // vertex ∈ sparseEnvelopeSupport ctx})
      (runSparseEnvelopeCT12 ctx).trace :=
  ((sparseEnvelopeProfile ctx).verifiedStage
    (sparseEnvelopeContext ctx)).traceValid

theorem runSparseEnvelopeCT12_iterations
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runSparseEnvelopeCT12 ctx).iterations =
      (sparseEnvelopeRemaining ctx).input.vertices.card :=
  ((sparseEnvelopeProfile ctx).verifiedStage
    (sparseEnvelopeContext ctx)).linearWork

theorem runSparseEnvelopeCT12_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ∃ result, result = runSparseEnvelopeCT12 ctx ∧
      result.outcome.Valid ∧
      CT12.Graph.ValidTrace
        (CT12.ListPeeling.capability ((fixedPackedInput ctx).problem)
          {vertex : ctx.G.Vertex // vertex ∈ sparseEnvelopeSupport ctx})
        result.trace ∧
      result.iterations ≤
        (sparseEnvelopeRemaining ctx).input.vertices.card :=
  ((sparseEnvelopeProfile ctx).verifiedStage
    (sparseEnvelopeContext ctx)).total

/-- Native linear polynomial budget for the exact local CT12 run. -/
theorem runSparseEnvelopeCT12_linearBudget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ((sparseEnvelopeProfile ctx).budget
        (sparseEnvelopeContext ctx)).checks () ≤
      ((sparseEnvelopeProfile ctx).budget
          (sparseEnvelopeContext ctx)).coefficient *
        (((sparseEnvelopeProfile ctx).budget
            (sparseEnvelopeContext ctx)).size () + 1) ^
          ((sparseEnvelopeProfile ctx).budget
            (sparseEnvelopeContext ctx)).degree :=
  ((sparseEnvelopeProfile ctx).budget
    (sparseEnvelopeContext ctx)).bounded ()

theorem sparseEnvelopeRemaining_atLeastTwo
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    2 ≤ (sparseEnvelopeRemaining ctx).input.vertices.card := by
  have originalLarge := sparseEnvelope_vertexCount_gt_three ctx
  have recurrence := sparseEnvelopeRemaining_vertexCount ctx
  omega

theorem sparseEnvelopeRemaining_edgeBound
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (sparseEnvelopeRemaining ctx).edgeCount ≤
      2 * (sparseEnvelopeRemaining ctx).input.vertices.card - 3 :=
  (sparseEnvelopeProfile ctx).edgeCount_le_two_mul_vertexCount_sub_three
    (sparseEnvelopeRemaining_atLeastTwo ctx)

/-- Exact edge recurrence for adding the selected cubic vertex back. -/
theorem sparseEnvelope_edgeRecurrence
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (sparseEnvelopeRemaining ctx).edgeCount + 3 =
      ctx.G.object.edgeCount := by
  have recurrence :=
    ctx.G.object.edgeCount_induceFinset_erase_add_degree
      ctx.G.object.vertexFinset (sparseEnvelopeRoot ctx)
        (ctx.G.object.mem_vertexFinset (sparseEnvelopeRoot ctx))
  rw [ctx.G.object.induceFinset_univ_edgeCount,
    ctx.G.object.induceFinset_univ_degree,
    sparseEnvelopeRoot_degree] at recurrence
  simpa [sparseEnvelopeRemaining, sparseEnvelopeSupport] using recurrence

/-- Manuscript Lemma `lem:sparse-upper-envelope`: `m ≤ 2n-2`. -/
theorem sparseEnvelope_edgeBound
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ctx.G.object.edgeCount ≤
      2 * ctx.G.object.input.vertices.card - 2 := by
  have remainingBound := sparseEnvelopeRemaining_edgeBound ctx
  have edgeRecurrence := sparseEnvelope_edgeRecurrence ctx
  have vertexRecurrence := sparseEnvelopeRemaining_vertexCount ctx
  have remainingLarge := sparseEnvelopeRemaining_atLeastTwo ctx
  omega

/-- Integer sparse slack `λ=2n-3-m`. -/
def sparseSlack
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Int :=
  2 * (ctx.G.object.input.vertices.card : Int) - 3 -
    (ctx.G.object.edgeCount : Int)

/-- Integer degree surplus `σ=2m-3n`. -/
def sparseSurplus
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Int :=
  2 * (ctx.G.object.edgeCount : Int) -
    3 * (ctx.G.object.input.vertices.card : Int)

/-- Manuscript Lemma `lem:sparse-slack-surplus`, first identity. -/
theorem sparseSlack_surplus_identity
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    sparseSurplus ctx =
      (ctx.G.object.input.vertices.card : Int) - 6 -
        2 * sparseSlack ctx := by
  simp only [sparseSurplus, sparseSlack]
  ring

/-- Division-free form of `m = 3n/2 + σ/2`. -/
theorem sparseEdge_surplus_identity
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    2 * (ctx.G.object.edgeCount : Int) =
      3 * (ctx.G.object.input.vertices.card : Int) + sparseSurplus ctx := by
  simp [sparseSurplus]

/-- The exact CT6 degree-excess ledger is the manuscript surplus `σ`. -/
theorem sparseSurplus_eq_degreeExcessLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    sparseSurplus ctx =
      ((ctx.G.object.input.vertices.orderedValues.map
        (fun vertex => ctx.G.object.degree vertex - 3)).sum : Int) := by
  symm
  apply Graph.SurplusPortActivity.degreeExcess_sum_int_eq
  intro vertex
  exact (packedStaticInput.fixedContext ctx).baseline.trans
    (ctx.G.object.minDegree_le_degree vertex)

/-- Verified prefix through the complete sparse-envelope CT12 block. -/
structure SparseEnvelopeFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Type (u + 1) where
  rootDegree : ctx.G.object.degree (sparseEnvelopeRoot ctx) = 3
  coreFree : (sparseEnvelopeRemaining ctx).InternalMinDegreeFree 3
  terminal : (runSparseEnvelopeCT12 ctx).terminal = .exhausted
  trace : (runSparseEnvelopeCT12 ctx).trace =
    CT12.ListPeeling.expectedTrace
      (sparseEnvelopeRemaining ctx).input.vertices.card
  verified : (runSparseEnvelopeCT12 ctx).outcome.Valid
  total : ∃ result, result = runSparseEnvelopeCT12 ctx ∧
    result.outcome.Valid ∧
    CT12.Graph.ValidTrace
      (CT12.ListPeeling.capability ((fixedPackedInput ctx).problem)
        {vertex : ctx.G.Vertex // vertex ∈ sparseEnvelopeSupport ctx})
      result.trace ∧
    result.iterations ≤ (sparseEnvelopeRemaining ctx).input.vertices.card
  iterations : (runSparseEnvelopeCT12 ctx).iterations =
    (sparseEnvelopeRemaining ctx).input.vertices.card
  linearBudget :
    ((sparseEnvelopeProfile ctx).budget
        (sparseEnvelopeContext ctx)).checks () ≤
      ((sparseEnvelopeProfile ctx).budget
          (sparseEnvelopeContext ctx)).coefficient *
        (((sparseEnvelopeProfile ctx).budget
            (sparseEnvelopeContext ctx)).size () + 1) ^
          ((sparseEnvelopeProfile ctx).budget
            (sparseEnvelopeContext ctx)).degree
  remainingEdgeBound : (sparseEnvelopeRemaining ctx).edgeCount ≤
    2 * (sparseEnvelopeRemaining ctx).input.vertices.card - 3
  edgeBound : ctx.G.object.edgeCount ≤
    2 * ctx.G.object.input.vertices.card - 2
  slackSurplus : sparseSurplus ctx =
    (ctx.G.object.input.vertices.card : Int) - 6 - 2 * sparseSlack ctx
  ledgerSurplus : sparseSurplus ctx =
    ((ctx.G.object.input.vertices.orderedValues.map
      (fun vertex => ctx.G.object.degree vertex - 3)).sum : Int)

abbrev VerifiedSparseEnvelopePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma fun previous : VerifiedSparseSurplusPrefix ctx =>
    Core.ExactStageHandoff previous (fun _ => SparseEnvelopeFacts ctx)

noncomputable def verifiedSparseEnvelopePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSparseSurplusPrefix ctx) :
    VerifiedSparseEnvelopePrefix ctx :=
  ⟨previous, Core.ExactStageHandoff.refl previous {
  rootDegree := sparseEnvelopeRoot_degree ctx
  coreFree := sparseEnvelopeRemaining_coreFree ctx
  terminal := runSparseEnvelopeCT12_terminal ctx
  trace := runSparseEnvelopeCT12_trace ctx
  verified := runSparseEnvelopeCT12_verified ctx
  total := runSparseEnvelopeCT12_total ctx
  iterations := runSparseEnvelopeCT12_iterations ctx
  linearBudget := runSparseEnvelopeCT12_linearBudget ctx
  remainingEdgeBound := sparseEnvelopeRemaining_edgeBound ctx
  edgeBound := sparseEnvelope_edgeBound ctx
  slackSurplus := sparseSlack_surplus_identity ctx
  ledgerSurplus := sparseSurplus_eq_degreeExcessLedger ctx }⟩

theorem exists_verifiedSparseEnvelopePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedSparseEnvelopePrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedSparseSurplusPrefix object baseline avoids
  exact ⟨ctx, verifiedSparseEnvelopePrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
