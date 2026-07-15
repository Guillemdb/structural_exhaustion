import Erdos64EG.CT15BaselineSpineDemand
import StructuralExhaustion.Graph.SurplusPairResponse

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT15: exact free/blocked surplus-pair quotient rank

This is the application layer for manuscript nodes `[130]`--`[132]`.  It
passes the exact activated surplus output from `[128]` and the retained
baseline-demand prefix from `[129]` to the graph-owned pair-response stage.
All pair generation, blocker search, shortest connectors, exact boundaried
responses, admissible-quotient reduction, and CT15 execution remain reusable.
The entropy realization contract is tracked separately and is not implied by
the quotient-rank result.
-/

noncomputable abbrev sparsePairActivationStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  activatedSurplusStage ctx

noncomputable def sparsePairResponseStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusPairResponse.VerifiedStage
      (sparsePairActivationStage ctx) :=
  Graph.SurplusPairResponse.verifiedStage
    (sparsePairActivationStage ctx)

def SparsePairCT15Verified
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop :=
  CT15.AdmissibleQuotient.VerifiedFor
    (Graph.SurplusPairResponse.responseCT15Profile
      (sparsePairActivationStage ctx))

theorem sparsePairCT15_verified
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    SparsePairCT15Verified ctx := by
  exact (sparsePairResponseStage ctx).ct15

theorem sparsePair_exact_partition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusPairResponse.blockedPairEnumeration
        (sparsePairActivationStage ctx)).card +
      (Graph.SurplusPairResponse.freePairEnumeration
        (sparsePairActivationStage ctx)).card =
      (Graph.SurplusPairResponse.pairEnumeration
        (setup := surplusPortActivationSetup ctx)).card :=
  (sparsePairResponseStage ctx).partition

theorem sparsePair_schedule_quartic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusPairResponse.pairEnumeration
        (setup := surplusPortActivationSetup ctx)).card ≤
      ctx.G.object.input.vertices.card ^ 4 :=
  (sparsePairResponseStage ctx).pairWork

/-- Verified proof prefix through the free/blocked pair-response quotient-rank
block.  The previous prefix is retained verbatim and the new stage consumes
its exact activation object definitionally. -/
structure VerifiedSparsePairResponsePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedBaselineSpineDemandPrefix ctx
  pairStage : Graph.SurplusPairResponse.VerifiedStage
    (sparsePairActivationStage ctx)
  ct15 : SparsePairCT15Verified ctx
  partition :
    (Graph.SurplusPairResponse.blockedPairEnumeration
        (sparsePairActivationStage ctx)).card +
      (Graph.SurplusPairResponse.freePairEnumeration
        (sparsePairActivationStage ctx)).card =
      (Graph.SurplusPairResponse.pairEnumeration
        (setup := surplusPortActivationSetup ctx)).card
  polynomialPairs :
    (Graph.SurplusPairResponse.pairEnumeration
        (setup := surplusPortActivationSetup ctx)).card ≤
      ctx.G.object.input.vertices.card ^ 4

noncomputable def verifiedSparsePairResponsePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedBaselineSpineDemandPrefix ctx) :
    VerifiedSparsePairResponsePrefix ctx where
  previous := previous
  pairStage := sparsePairResponseStage ctx
  ct15 := sparsePairCT15_verified ctx
  partition := sparsePair_exact_partition ctx
  polynomialPairs := sparsePair_schedule_quartic ctx

theorem exists_verifiedSparsePairResponsePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedSparsePairResponsePrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedBaselineSpineDemandPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedSparsePairResponsePrefix ctx previous⟩

end Erdos64EG.Internal
