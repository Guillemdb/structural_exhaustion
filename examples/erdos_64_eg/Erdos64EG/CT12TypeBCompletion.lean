import Erdos64EG.CT12TypeBDemandSystem
import StructuralExhaustion.CT12.RefinedLedgerCompletion

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

/-- Verified endpoint for complete choice versus obstruction on every
declared assigned-center family, with its graph-size work bound. -/
structure VerifiedTypeBCompletionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedTypeBDemandSystemPrefix ctx
  completion : ∀ support : TypeBAssignedSupport ctx,
    support.completionProfile.VerifiedStage ctx.toBranchContext
  iterationsLeVertices : ∀ support : TypeBAssignedSupport ctx,
    (support.completionProfile.run ctx.toBranchContext).iterations ≤
      ctx.G.object.input.vertices.card

noncomputable def verifiedTypeBCompletionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTypeBDemandSystemPrefix ctx) :
    VerifiedTypeBCompletionPrefix ctx where
  previous := previous
  completion := fun support => support.completionStage
  iterationsLeVertices := fun support =>
    support.completion_iterations_le_vertices

theorem exists_verifiedTypeBCompletionPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedTypeBCompletionPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedTypeBDemandSystemPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedTypeBCompletionPrefix ctx previous⟩

end Erdos64EG.Internal
