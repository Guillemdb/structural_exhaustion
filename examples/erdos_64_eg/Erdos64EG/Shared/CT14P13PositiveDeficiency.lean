import Erdos64EG.Shared.P13RemainderResidual
import StructuralExhaustion.Graph.AssignedSupportCharge

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact positive deficiency of the selected P13 remainder

Diagram node `[28]` is an accounting definition, not a new mathematical
assumption.  The reusable assigned-support graph profile already owns induced
degree and positive deficiency.  This file instantiates it on the exact CT12
remainder retained by nodes `[25]`--`[27]` and proves that the resulting sum is
literally the manuscript formula.
-/

/-- The graph-owned charge profile on the exact selected remainder.  There
are no assigned high centers at this definition-only stage. -/
noncomputable def p13RemainderDeficiencyProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.AssignedSupportCharge.Profile ctx.G.object where
  core := p13RemainderVertices ctx
  assignedCenters := ∅

/-- Internal degree is computed in the literal induced remainder. -/
theorem p13Remainder_internalDegree_eq
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (vertex : ctx.G.Vertex) :
    (p13RemainderDeficiencyProfile ctx).internalDegree vertex =
      (letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
       letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
       letI : DecidableRel ctx.G.object.graph.Adj := ctx.G.object.input.decideAdj
       (ctx.G.object.graph.neighborFinset vertex ∩
          p13RemainderVertices ctx).card) := by
  rfl

/-- Exact node-[28] formula
`def⁺(R)=sum_{v in R} max(0,3-d_R(v))`; natural subtraction is exactly the
displayed maximum with zero. -/
theorem p13Remainder_positiveDeficiency_eq
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13RemainderDeficiencyProfile ctx).positiveDeficiency =
      Finset.sum (p13RemainderVertices ctx) (fun vertex : ctx.G.Vertex =>
        3 - (p13RemainderDeficiencyProfile ctx).internalDegree vertex) := by
  rfl

/-- The node-[28] definition retains the exact node-[27] no-three-core
predecessor on the same selected graph. -/
structure P13PositiveDeficiencyFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Type (u + 1) where
  exactFormula :
    (p13RemainderDeficiencyProfile ctx).positiveDeficiency =
      Finset.sum (p13RemainderVertices ctx) (fun vertex : ctx.G.Vertex =>
        3 - (p13RemainderDeficiencyProfile ctx).internalDegree vertex)
  noInternalThreeCore : (p13Remainder ctx).InternalMinDegreeFree 3

/-- Framework-owned exact node handoff.  The Sigma index names the literal
incoming CT12 ledger; `ExactStageHandoff` owns retention and transports the
definition-only accounting facts. -/
abbrev VerifiedP13PositiveDeficiencyPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma fun previous : VerifiedP13PackingPrefix ctx =>
    Core.ExactStageHandoff previous (fun _ => P13PositiveDeficiencyFacts ctx)

noncomputable def verifiedP13PositiveDeficiencyPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13PackingPrefix ctx) :
    VerifiedP13PositiveDeficiencyPrefix ctx :=
  ⟨previous, Core.ExactStageHandoff.refl previous {
    exactFormula := p13Remainder_positiveDeficiency_eq ctx
    noInternalThreeCore := previous.2.output.added.noInternalThreeCore }⟩

def p13PositiveDeficiencyPrefix_previous
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedP13PositiveDeficiencyPrefix ctx) :
    VerifiedP13PackingPrefix ctx :=
  verified.1

theorem exists_verifiedP13PositiveDeficiencyPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedP13PositiveDeficiencyPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedP13PackingPrefix object baseline avoids
  exact ⟨ctx, verifiedP13PositiveDeficiencyPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
