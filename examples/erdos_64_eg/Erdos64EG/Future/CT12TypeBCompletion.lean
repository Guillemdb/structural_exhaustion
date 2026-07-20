import Erdos64EG.Future.CT12TypeBDemandSystem
import StructuralExhaustion.CT12.RefinedLedgerCompletion
import StructuralExhaustion.Routes.Accumulated

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT12: unconditional completion of a declared Type B demand family

The finite demand schedule and every candidate fibre come from
`TypeBAssignedSupport`; this file supplies no candidate predicate, support
map, obstruction, or satisfiability hypothesis.  CT12 peels the literal
declared center schedule and proves the exhaustive alternative between a
pairwise-disjoint full choice and a minimal overlap obstruction.

This is deliberately not called residual-core maximality: proving that no
additional high center or decorated handoff remains requires a separate
graph transition.
-/

namespace TypeBAssignedSupport

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (support : TypeBAssignedSupport ctx)

/-- The derived core ledger viewed through the CT12 completion API. -/
noncomputable def completionProfile :
    CT12.RefinedLedgerCompletion.Profile support.Demand ctx.G.Vertex :=
  support.ledgerProfile

/-- The common CT12 verified stage on the branch-derived ledger. -/
noncomputable def completionStage :
    support.completionProfile.VerifiedStage ctx.toBranchContext :=
  support.completionProfile.verifiedStage ctx.toBranchContext

theorem completion_exhausted :
    (support.completionProfile.run ctx.toBranchContext).terminal = .exhausted :=
  support.completionStage.terminal

theorem completion_iterations_exact :
    (support.completionProfile.run ctx.toBranchContext).iterations =
      support.demands.card :=
  support.completionStage.iterationsExact

/-- CT12 performs at most one peeling iteration per graph vertex. -/
theorem completion_iterations_le_vertices :
    (support.completionProfile.run ctx.toBranchContext).iterations ≤
      ctx.G.object.input.vertices.card := by
  rw [support.completion_iterations_exact]
  exact support.demand_card_le_vertices

/-- The exact full-family alternative, with no nonemptiness premise. -/
theorem full_choice_or_obstruction :
    Nonempty support.completionProfile.FullChoice ∨
      support.completionProfile.FullObstruction :=
  support.completionStage.alternative

/-- If a full disjoint choice does not exist, CT12 returns a nonempty
inclusion-minimal obstructing subschedule. -/
theorem full_choice_or_minimal_obstruction :
    Nonempty support.completionProfile.FullChoice ∨
      ∃ selected : List support.Demand,
        selected.Sublist support.completionProfile.fullSchedule ∧
          support.completionProfile.MinimalOverlapObstruction selected :=
  support.completionStage.minimalAlternative

end TypeBAssignedSupport

/-- Canonical executable CT12 target selected by one concrete assigned
support. -/
noncomputable def typeBCompletionTarget
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (support : TypeBAssignedSupport ctx) :=
  support.completionProfile.executableTarget PackedProblem.{u}

/-- The only application-owned part of the CT14→CT12 edge: the accumulated
demand-system theorem selects the inherited branch context and the literal
indexed peeling state. -/
noncomputable def typeBCompletionAdapter
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (support : TypeBAssignedSupport ctx) :
    Routes.Accumulated.Adapter (VerifiedTypeBDemandSystem support)
      (typeBCompletionTarget support) :=
  support.completionProfile.transitionAdapter ctx.toBranchContext
    (VerifiedTypeBDemandSystem support)

/-- Pointwise CT14→CT12 family over the supplied assigned supports.  This is
a dependent function and performs no traversal of the support type. -/
noncomputable def typeBCompletionPointwiseAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Routes.Accumulated.PointwiseAdapter .ct14 .ct12
      (TypeBAssignedSupport ctx) (VerifiedTypeBDemandSystemPrefix ctx) where
  Source := VerifiedTypeBDemandSystem
  target := typeBCompletionTarget
  adapter := typeBCompletionAdapter
  current := fun support ledger => ledger.added support

noncomputable def typeBCompletionTransitionFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Routes.Accumulated.pointwiseFamily (typeBCompletionPointwiseAdapter ctx)

noncomputable def typeBCompletionTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct14
      (VerifiedTypeBDemandSystemPrefix ctx)) :=
  Routes.Accumulated.advancePointwise
    (typeBCompletionPointwiseAdapter ctx) source

abbrev TypeBCompletionTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct14
      (VerifiedTypeBDemandSystemPrefix ctx)) :=
  Routes.Accumulated.PointwiseOutputLedger
    (typeBCompletionPointwiseAdapter ctx) source

/-- The literal CT12 result at one supplied support, projected without
reconstructing either the predecessor or the peeling input. -/
noncomputable def typeBCompletionLocalResult
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {source : Core.Routing.ResidualStage .ct14
      (VerifiedTypeBDemandSystemPrefix ctx)}
    (execution : TypeBCompletionTransitionLedger ctx source)
    (support : TypeBAssignedSupport ctx) :=
  (execution.localStage support).targetResult

@[simp] theorem typeBCompletionLocalResult_transition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct14
      (VerifiedTypeBDemandSystemPrefix ctx))
    (support : TypeBAssignedSupport ctx) :
    typeBCompletionLocalResult ctx
        (typeBCompletionTransitionStage ctx source).output support =
      support.completionProfile.run ctx.toBranchContext :=
  rfl

/-- Node-local semantic facts attached to the exact pointwise CT12
execution. -/
structure TypeBCompletionFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {source : Core.Routing.ResidualStage .ct14
      (VerifiedTypeBDemandSystemPrefix ctx)}
    (execution : TypeBCompletionTransitionLedger ctx source) : Prop where
  completion : ∀ support : TypeBAssignedSupport ctx,
    support.completionProfile.VerifiedStage ctx.toBranchContext
  iterationsLeVertices : ∀ support : TypeBAssignedSupport ctx,
    (typeBCompletionLocalResult ctx execution support).iterations ≤
      ctx.G.object.input.vertices.card

abbrev TypeBCompletionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct14
      (VerifiedTypeBDemandSystemPrefix ctx)) :=
  Core.Routing.LedgerExtension
    (TypeBCompletionTransitionLedger ctx source)
    (TypeBCompletionFacts ctx)

noncomputable def typeBCompletionLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct14
      (VerifiedTypeBDemandSystemPrefix ctx)) :
    Core.Routing.ResidualStage .ct12 (TypeBCompletionLedger ctx source) := by
  let execution := typeBCompletionTransitionStage ctx source
  let executionStage : Core.Routing.ResidualStage .ct12
      (TypeBCompletionTransitionLedger ctx source) :=
    execution
  exact executionStage.extend {
    completion := fun support => support.completionStage
    iterationsLeVertices := fun support => by
      change (typeBCompletionLocalResult ctx executionStage.output support).iterations ≤
        ctx.G.object.input.vertices.card
      rw [typeBCompletionLocalResult_transition]
      exact support.completion_iterations_le_vertices
  }

/-- The full accumulated residual after the CT14→CT12 execution. -/
abbrev VerifiedTypeBCompletionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedTypeBDemandSystemPrefix ctx)
    (fun previous => Core.Routing.ResidualStage .ct12
      (TypeBCompletionLedger ctx (Core.Routing.ResidualStage.exact previous)))

noncomputable def verifiedTypeBCompletionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTypeBDemandSystemPrefix ctx) :
    VerifiedTypeBCompletionPrefix ctx :=
  ⟨previous, typeBCompletionLedgerStage ctx
    (Core.Routing.ResidualStage.exact previous)⟩

theorem exists_verifiedTypeBCompletionPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedTypeBCompletionPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedTypeBDemandSystemPrefix object baseline avoids
  exact ⟨ctx, verifiedTypeBCompletionPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
