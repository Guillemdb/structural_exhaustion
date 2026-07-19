import Erdos64EG.CT6SurplusPortActivation
import StructuralExhaustion.CT15.BaselineDemand
import StructuralExhaustion.CT15.Automation

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v

/-!
# CT15: executable baseline-spine demand

Manuscript node `[129]` defines a baseline demand by an independently
target-testable finite coordinate family and its deficit from the cubic
skeleton bit budget.  The definition itself does not construct a family with
linear deficit.  The canonical empty family below realizes the definition
unconditionally with its exact (maximal) deficit.  CT15 checks the complete
declared coordinate universe and returns the full-rank ledger.  A later use of
the entropy sandwich must supply and verify any stronger deficit bound it
needs; none is assumed here.
-/

/-- Number of possible undirected edge slots on the selected vertex set. -/
def baselineSpineEdgeSlots
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat :=
  Nat.choose ctx.G.object.input.vertices.card 2

/-- Exact ceiling of the cubic edge baseline `3n/2`. -/
def baselineSpineEdgeCount
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat :=
  (3 * ctx.G.object.input.vertices.card + 1) / 2

/-- Exact number of labelled skeletons at the cubic baseline edge count. -/
def baselineSpineStateCount
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat :=
  Nat.choose (baselineSpineEdgeSlots ctx) (baselineSpineEdgeCount ctx)

/-- Executable integer bit budget: the largest `b` with `2^b` bounded by the
cubic-baseline skeleton count. -/
def baselineSpineBitBudget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat :=
  Nat.log2 (baselineSpineStateCount ctx)

/-- The empty declared family is the canonical unconditional inhabitant of
the baseline-demand definition.  Its deficit is exactly the full executable
cubic bit budget; no asymptotic deficit estimate is hidden in the data. -/
def baselineSpineProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    CT15.BaselineDemand.Profile ((fixedPackedInput ctx).problem) where
  Coordinate := Empty
  coordinates := Core.Enumeration.empty
  TargetDependent := fun _ _ => False
  independent := fun _ _ => id
  baseline := fun _ => baselineSpineBitBudget ctx
  deficit := fun _ => baselineSpineBitBudget ctx
  deficit_le_baseline := fun _ => le_rfl
  lowerBound := by intro _; simp

def runBaselineSpineCT15
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  (baselineSpineProfile ctx).run (sparseEnvelopeContext ctx)

theorem baselineSpineProfile_coordinateCount
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (baselineSpineProfile ctx).coordinates.card = 0 :=
  rfl

theorem baselineSpineProfile_exactDeficit
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (baselineSpineProfile ctx).deficit (sparseEnvelopeContext ctx) =
      baselineSpineBitBudget ctx :=
  rfl

theorem baselineSpineProfile_lowerBound
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (baselineSpineProfile ctx).baseline (sparseEnvelopeContext ctx) -
        (baselineSpineProfile ctx).deficit (sparseEnvelopeContext ctx) ≤
      (baselineSpineProfile ctx).coordinates.card :=
  (baselineSpineProfile ctx).lowerBound (sparseEnvelopeContext ctx)

theorem runBaselineSpineCT15_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runBaselineSpineCT15 ctx).terminal = .fullRankLedger :=
  (baselineSpineProfile ctx).terminal (sparseEnvelopeContext ctx)

theorem runBaselineSpineCT15_trace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runBaselineSpineCT15 ctx).trace =
      [.entry, .rankComputation, .rankSplit, .ledgerComputation,
        .ledgerComparison, .fullRankLedgerTerminal] :=
  (baselineSpineProfile ctx).trace (sparseEnvelopeContext ctx)

theorem runBaselineSpineCT15_verified
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runBaselineSpineCT15 ctx).outcome.Valid :=
  (baselineSpineProfile ctx).verified (sparseEnvelopeContext ctx)

theorem runBaselineSpineCT15_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ∃ result, result = runBaselineSpineCT15 ctx ∧
      result.outcome.Valid ∧
      @CT15.Graph.ValidTrace ((fixedPackedInput ctx).problem)
        (baselineSpineProfile ctx).spec
        (baselineSpineProfile ctx).capability
        (sparseEnvelopeContext ctx) result.trace :=
  (baselineSpineProfile ctx).total (sparseEnvelopeContext ctx)

theorem runBaselineSpineCT15_linearBudget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ((baselineSpineProfile ctx).budget
        (sparseEnvelopeContext ctx)).checks () ≤
      ((baselineSpineProfile ctx).budget
          (sparseEnvelopeContext ctx)).coefficient *
        (((baselineSpineProfile ctx).budget
            (sparseEnvelopeContext ctx)).size () + 1) ^
          ((baselineSpineProfile ctx).budget
            (sparseEnvelopeContext ctx)).degree :=
  (baselineSpineProfile ctx).linearWork (sparseEnvelopeContext ctx)

/-- Mathematical adapter for the canonical CT6→CT15 baseline-demand edge. -/
def baselineSpineDemandAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Source : Sort v} :
    Routes.Accumulated.Adapter Source
      (baselineSpineProfile ctx).capability.executableInterface where
  targetContext := fun _previous => sparseEnvelopeContext ctx
  trigger := fun _previous => ()

/-- Framework-owned CT6→CT15 execution retaining the complete activation
ledger. -/
noncomputable def baselineSpineDemandTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPortActivationPrefix ctx) :=
  Routes.Accumulated.advanceCurrent
    (baselineSpineProfile ctx).capability.executableInterface
    (baselineSpineDemandAdapter ctx)
    (surplusPortActivationLedgerStage ctx previous)

abbrev BaselineSpineDemandTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPortActivationPrefix ctx) :=
  Routes.Accumulated.OutputLedger (sourceTactic := .ct6)
    (baselineSpineProfile ctx).capability.executableInterface
    (baselineSpineDemandAdapter ctx)
    (surplusPortActivationLedgerStage ctx previous)

/-- The exact node-`[129]` mathematical obligations, attached to the literal
CT15 execution returned by the framework edge. -/
structure BaselineSpineDemandFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {previous : VerifiedSurplusPortActivationPrefix ctx}
    (_stage : BaselineSpineDemandTransitionLedger ctx previous) : Prop where
  coordinateCount : (baselineSpineProfile ctx).coordinates.card = 0
  exactDeficit :
    (baselineSpineProfile ctx).deficit (sparseEnvelopeContext ctx) =
      baselineSpineBitBudget ctx
  lowerBound :
    (baselineSpineProfile ctx).baseline (sparseEnvelopeContext ctx) -
        (baselineSpineProfile ctx).deficit (sparseEnvelopeContext ctx) ≤
      (baselineSpineProfile ctx).coordinates.card
  terminal : (runBaselineSpineCT15 ctx).terminal = .fullRankLedger
  trace : (runBaselineSpineCT15 ctx).trace =
    [.entry, .rankComputation, .rankSplit, .ledgerComputation,
      .ledgerComparison, .fullRankLedgerTerminal]
  verified : (runBaselineSpineCT15 ctx).outcome.Valid
  total : ∃ result, result = runBaselineSpineCT15 ctx ∧
    result.outcome.Valid ∧
    @CT15.Graph.ValidTrace ((fixedPackedInput ctx).problem)
      (baselineSpineProfile ctx).spec
      (baselineSpineProfile ctx).capability
      (sparseEnvelopeContext ctx) result.trace
  linearBudget :
    ((baselineSpineProfile ctx).budget
        (sparseEnvelopeContext ctx)).checks () ≤
      ((baselineSpineProfile ctx).budget
          (sparseEnvelopeContext ctx)).coefficient *
        (((baselineSpineProfile ctx).budget
            (sparseEnvelopeContext ctx)).size () + 1) ^
          ((baselineSpineProfile ctx).budget
            (sparseEnvelopeContext ctx)).degree

abbrev BaselineSpineDemandLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPortActivationPrefix ctx) :=
  Core.Routing.LedgerExtension
    (BaselineSpineDemandTransitionLedger ctx previous)
    (BaselineSpineDemandFacts ctx)

abbrev VerifiedBaselineSpineDemandPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma (BaselineSpineDemandLedger ctx)

noncomputable def verifiedBaselineSpineDemandPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusPortActivationPrefix ctx) :
    VerifiedBaselineSpineDemandPrefix ctx :=
  let stage := baselineSpineDemandTransitionStage ctx previous
  ⟨previous, ⟨stage, {
    coordinateCount := baselineSpineProfile_coordinateCount ctx
    exactDeficit := baselineSpineProfile_exactDeficit ctx
    lowerBound := baselineSpineProfile_lowerBound ctx
    terminal := runBaselineSpineCT15_terminal ctx
    trace := runBaselineSpineCT15_trace ctx
    verified := runBaselineSpineCT15_verified ctx
    total := runBaselineSpineCT15_total ctx
    linearBudget := runBaselineSpineCT15_linearBudget ctx
  }⟩⟩

/-- Canonical CT15 continuation stage after node `[129]`. -/
noncomputable def baselineSpineDemandLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedBaselineSpineDemandPrefix ctx) :=
  verified.2.previous.ledgerStage.extend verified.2.added

theorem exists_verifiedBaselineSpineDemandPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedBaselineSpineDemandPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedSurplusPortActivationPrefix object baseline avoids
  exact ⟨ctx, verifiedBaselineSpineDemandPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
