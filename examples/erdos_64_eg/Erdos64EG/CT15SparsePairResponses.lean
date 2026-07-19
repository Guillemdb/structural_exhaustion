import Erdos64EG.CT15BaselineSpineDemand
import StructuralExhaustion.Graph.SurplusPairResponse

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v

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

/-- Mathematical adapter for the canonical CT15→CT15 quotient-rank edge. -/
noncomputable def sparsePairResponseAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Source : Sort v} :
    Routes.Accumulated.Adapter Source
      (Graph.SurplusPairResponse.responseCT15Profile
        (sparsePairActivationStage ctx)).capability.executableInterface where
  targetContext := fun _source =>
    (Graph.SurplusPairResponse.responseCT15Profile
      (sparsePairActivationStage ctx)).branchInput
  trigger := fun _source => ()

noncomputable def sparsePairResponseTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedBaselineSpineDemandPrefix ctx) :=
  Routes.Accumulated.advanceCurrent
    (Graph.SurplusPairResponse.responseCT15Profile
      (sparsePairActivationStage ctx)).capability.executableInterface
    (sparsePairResponseAdapter
      (Source := BaselineSpineDemandLedger ctx previous.1) ctx)
    (baselineSpineDemandLedgerStage ctx previous)

abbrev SparsePairResponseTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedBaselineSpineDemandPrefix ctx) :=
  Routes.Accumulated.OutputLedger (sourceTactic := .ct15)
    (Graph.SurplusPairResponse.responseCT15Profile
      (sparsePairActivationStage ctx)).capability.executableInterface
    (sparsePairResponseAdapter
      (Source := BaselineSpineDemandLedger ctx previous.1) ctx)
    (baselineSpineDemandLedgerStage ctx previous)

/-- Mathematical obligations of nodes `[130]`--`[132]`, attached to the
literal quotient-rank CT15 execution. -/
structure SparsePairResponseFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {previous : VerifiedBaselineSpineDemandPrefix ctx}
    (_stage : SparsePairResponseTransitionLedger ctx previous) : Prop where
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

abbrev SparsePairResponseLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedBaselineSpineDemandPrefix ctx) :=
  Core.Routing.LedgerExtension
    (SparsePairResponseTransitionLedger ctx previous)
    (SparsePairResponseFacts ctx)

/-- Verified proof prefix through the free/blocked quotient-rank block.  The
literal CT15 predecessor is the `previous` component of the ledger extension,
not an application-owned equality field. -/
abbrev VerifiedSparsePairResponsePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma fun previous : VerifiedBaselineSpineDemandPrefix ctx =>
    Core.Routing.ResidualStage .ct15 (SparsePairResponseLedger ctx previous)

noncomputable def verifiedSparsePairResponsePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedBaselineSpineDemandPrefix ctx) :
    VerifiedSparsePairResponsePrefix ctx :=
  let stage := sparsePairResponseTransitionStage ctx previous
  ⟨previous, stage.extend {
    pairStage := sparsePairResponseStage ctx
    ct15 := sparsePairCT15_verified ctx
    partition := sparsePair_exact_partition ctx
    polynomialPairs := sparsePair_schedule_quartic ctx
  }⟩

/-- Canonical complete CT15 stage after nodes `[130]`--`[132]`. -/
noncomputable def sparsePairResponseLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSparsePairResponsePrefix ctx) :=
  verified.2

theorem exists_verifiedSparsePairResponsePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedSparsePairResponsePrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedBaselineSpineDemandPrefix object baseline avoids
  exact ⟨ctx, verifiedSparsePairResponsePrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
