import Hypostructure.Fixtures.PDERow5DirectedExhaustiveness
import Hypostructure.PDE.FastTrack.DefectRouting

/-!
# PDE row-6 raw defect-routing fixture

This finite fixture verifies the source-neutral part of row 6.  Four CT13
outcomes and three CT7 outcomes are independently selectable on the same
literal row-5 target-visible predecessor.  Every one of the twelve pairs runs
both generators, retains their exact outputs in one raw transcript, and stops
at the typed unaligned residual because no analytic alignment is registered.

The fixture deliberately proves no relation between a CT terminal and a PDE
semantic tag.  The positive-gap and zero-boundary row-5 siblings are also run
through the same executor and pay only the target-visible focus selector.
-/

namespace Hypostructure.Fixtures.PDERow6DefectRoutingRaw

open Hypostructure
open Hypostructure.Core
open Hypostructure.Core.Residual
open Hypostructure.PDE.FastTrack

noncomputable section

abbrev Previous := PDERow5DirectedExhaustiveness.Previous
abbrev ParentFocus := PDERow5DirectedExhaustiveness.focus
abbrev RowFiveProfile :=
  DirectedExhaustiveness.Profile Previous ParentFocus Real Real

inductive TierMode where
  | tierOne
  | overlap
  | deficit
  | reconciled
  deriving DecidableEq, Repr

inductive ContextMode where
  | realization
  | distinguishing
  | neutral
  deriving DecidableEq, Repr

def expectedTierTerminal : TierMode -> CT13.Terminal
  | .tierOne => .tierOne
  | .overlap => .overlap
  | .deficit => .deficit
  | .reconciled => .reconciled

def expectedContextTerminal : ContextMode -> CT7.Terminal
  | .realization => .realization
  | .distinguishing => .distinguishing
  | .neutral => .neutral

def expectedTierChecks : TierMode -> Nat
  | .tierOne => 2
  | .overlap => 6
  | .deficit => 11
  | .reconciled => 11

def expectedContextChecks : ContextMode -> Nat
  | .realization => 2
  | .distinguishing => 4
  | .neutral => 4

/-! ## Residual-owned CT13 registration -/

abbrev View (rowFive : RowFiveProfile) := DefectRouting.ActiveView rowFive

def viewQuery (rowFive : RowFiveProfile) :
    Residual.Query (View rowFive) fun _view => View rowFive :=
  Residual.Query.residual

def payerSchedule : Core.Finite.Enumeration (Fin 3) :=
  Core.Finite.Enumeration.ofNodupList [0, 1, 2] (by decide)

def obstructionSchedule : CT13.ObstructionSchedule (Fin 2) where
  fallbackDefault := 0
  remaining := [1]
  nodup := by decide
  decEq := inferInstance

def tierTwoSchedule (_obstruction : Fin 2) :
    Core.Finite.Enumeration (Fin 3) :=
  Core.Finite.Enumeration.ofNodupList [0, 1] (by decide)

def payerQuery (rowFive : RowFiveProfile) :
    Residual.Query (View rowFive) fun _view =>
      Core.Finite.Enumeration (Fin 3) :=
  (viewQuery rowFive).map fun _view _root => payerSchedule

def obstructionQuery (rowFive : RowFiveProfile) :
    Residual.Query (View rowFive) fun _view =>
      CT13.ObstructionSchedule (Fin 2) :=
  (viewQuery rowFive).map fun _view _root => obstructionSchedule

def tierTwoQuery (rowFive : RowFiveProfile) :
    Residual.Query (View rowFive) fun _view =>
      Fin 2 -> Core.Finite.Enumeration (Fin 3) :=
  (viewQuery rowFive).map fun _view _root => tierTwoSchedule

def tieredSpec (rowFive : RowFiveProfile) (mode : TierMode) :
    CT13.Spec (View rowFive) where
  Payer := fun _view => Fin 3
  Obstruction := fun _view => Fin 2
  Resource := fun _view => Bool
  Eligible := fun _view payer => mode = .tierOne /\ payer = 1
  obstructionCost := fun _view obstruction =>
    if mode = .reconciled then 0
    else if obstruction = 1 then 0 else 1
  payerResource := fun _view payer =>
    if mode = .overlap then false else payer == 1
  charge := fun _view _payer => 1
  demand := fun _view => if mode = .deficit then 3 else 2

def tieredCapability (rowFive : RowFiveProfile) (mode : TierMode) :
    CT13.Capability (tieredSpec rowFive mode) where
  payers := payerQuery rowFive
  obstructions := obstructionQuery rowFive
  tierTwo := tierTwoQuery rowFive
  eligibleDecidable := fun _view payer => by
    change Fin 3 at payer
    change Decidable (mode = .tierOne /\ payer = (1 : Fin 3))
    infer_instance
  resourceDecidableEq := fun _view => by
    change DecidableEq Bool
    infer_instance
  inputSize := fun _view => 0
  workCoefficient := 25
  workDegree := 0
  workBound := by
    intro _view
    change CT13.localCheckBound payerSchedule obstructionSchedule
      tierTwoSchedule <= 25
    decide

/-! ## Residual-owned CT7 registration -/

def contextSchedule : Core.Finite.Enumeration Bool :=
  Core.Finite.Enumeration.ofNodupList [false, true] (by decide)

theorem contextSchedule_complete (context : Bool) :
    Exists fun index : Fin contextSchedule.card =>
      context = contextSchedule.get index := by
  cases context
  · exact ⟨⟨0, by decide⟩, rfl⟩
  · exact ⟨⟨1, by decide⟩, rfl⟩

def response (representative context : Bool) : Bool :=
  representative && context

abbrev responseSystem : Core.Response.System Bool :=
  Core.Response.System.ofDecodedContexts Bool Bool Bool response id

def representatives : ContextMode -> Core.Response.Representatives Bool
  | .realization => ⟨true, false⟩
  | .distinguishing => ⟨false, true⟩
  | .neutral => ⟨false, false⟩

def representativesQuery (rowFive : RowFiveProfile) (mode : ContextMode) :
    Residual.Query (View rowFive) fun _view =>
      Core.Response.Representatives Bool :=
  (viewQuery rowFive).map fun _view _root => representatives mode

def contextsQuery (rowFive : RowFiveProfile) :
    Residual.Query (View rowFive) fun _view =>
      Core.Finite.Enumeration Bool :=
  (viewQuery rowFive).map fun _view _root => contextSchedule

def contextSpec (rowFive : RowFiveProfile) (mode : ContextMode) :
    CT7.Spec (View rowFive) where
  Representative := Bool
  system := responseSystem
  Realizes := fun _view representative context =>
    mode = .realization /\ representative = true /\ context = true

def contextCapability (rowFive : RowFiveProfile) (mode : ContextMode) :
    CT7.Capability (contextSpec rowFive mode) :=
  CT7.Capability.ofExactContexts
    (representativesQuery rowFive mode) (contextsQuery rowFive)
    (by
      change DecidableEq Bool
      infer_instance)
    (fun _view coordinate => by
      change Bool at coordinate
      change Decidable
        (mode = .realization /\
          (representatives mode).source = true /\ coordinate = true)
      infer_instance)
    (fun _view context => contextSchedule_complete context)

/-! ## Explicitly unavailable analytic alignment -/

def profile (rowFive : RowFiveProfile) (tier : TierMode)
    (context : ContextMode) : DefectRouting.Profile rowFive where
  tieredSpec := tieredSpec rowFive tier
  tieredCapability := tieredCapability rowFive tier
  contextSpec := contextSpec rowFive context
  contextCapability := contextCapability rowFive context
  FiniteResistance := fun _view _boundary _raw => False
  HarmonicZero := fun _view _boundary _raw => False
  HarmonicLedgerMember := fun _view _boundary _raw => False
  NonroutableTargetVisible := fun _view _boundary _raw => False
  alignmentRegistration :=
    rowFive.targetVisibleBoundaryQuery.map
      fun _stage _active _boundary =>
        .unavailable .notRegistered

/-! ## The complete active four-by-three product -/

def predecessor := PDERow5DirectedExhaustiveness.visibleBoundaryRun.value

def predecessorActive :
    PDERow5DirectedExhaustiveness.visibleBoundaryProfile.TargetVisibleFocus.Active
      predecessor :=
  PDERow5DirectedExhaustiveness.visibleBoundaryRefinedActive

def activeView : View PDERow5DirectedExhaustiveness.visibleBoundaryProfile :=
  Focus.ActiveView.of predecessor predecessorActive

def activeGeneration (tier : TierMode) (context : ContextMode) :=
  DefectRouting.generateActiveCounted
    (profile PDERow5DirectedExhaustiveness.visibleBoundaryProfile tier context)
    activeView

theorem every_pair_has_exact_terminals (tier : TierMode)
    (context : ContextMode) :
    (activeGeneration tier context).value.raw.ct13.terminal =
        expectedTierTerminal tier /\
      (activeGeneration tier context).value.raw.ct7.terminal =
        expectedContextTerminal context := by
  cases tier <;> cases context <;> decide

theorem fixed_ct13_allows_every_ct7_terminal :
    (activeGeneration .tierOne .realization).value.raw.ct13.terminal =
        .tierOne /\
      (activeGeneration .tierOne .distinguishing).value.raw.ct13.terminal =
        .tierOne /\
      (activeGeneration .tierOne .neutral).value.raw.ct13.terminal =
        .tierOne /\
      (activeGeneration .tierOne .realization).value.raw.ct7.terminal =
        .realization /\
      (activeGeneration .tierOne .distinguishing).value.raw.ct7.terminal =
        .distinguishing /\
      (activeGeneration .tierOne .neutral).value.raw.ct7.terminal =
        .neutral := by
  decide

theorem fixed_ct7_allows_every_ct13_terminal :
    (activeGeneration .tierOne .neutral).value.raw.ct7.terminal = .neutral /\
      (activeGeneration .overlap .neutral).value.raw.ct7.terminal = .neutral /\
      (activeGeneration .deficit .neutral).value.raw.ct7.terminal = .neutral /\
      (activeGeneration .reconciled .neutral).value.raw.ct7.terminal = .neutral /\
      (activeGeneration .tierOne .neutral).value.raw.ct13.terminal = .tierOne /\
      (activeGeneration .overlap .neutral).value.raw.ct13.terminal = .overlap /\
      (activeGeneration .deficit .neutral).value.raw.ct13.terminal = .deficit /\
      (activeGeneration .reconciled .neutral).value.raw.ct13.terminal =
        .reconciled := by
  decide

theorem both_generators_have_exact_work (tier : TierMode)
    (context : ContextMode) :
    (CT13.generateCounted
        (tieredCapability
          PDERow5DirectedExhaustiveness.visibleBoundaryProfile tier)
        activeView).checks = expectedTierChecks tier /\
      (CT7.generateCounted
        (contextCapability
          PDERow5DirectedExhaustiveness.visibleBoundaryProfile context)
        activeView).checks = expectedContextChecks context /\
      (activeGeneration tier context).checks =
        expectedTierChecks tier + expectedContextChecks context := by
  cases tier <;> cases context <;> decide

theorem every_active_pair_remains_unaligned (tier : TierMode)
    (context : ContextMode) :
    (activeGeneration tier context).value.disposition = .unaligned := by
  cases tier <;> cases context <;> rfl

def execution (tier : TierMode) (context : ContextMode) :=
  DefectRouting.run
    (profile PDERow5DirectedExhaustiveness.visibleBoundaryProfile tier context)
    predecessor

def successorActive (tier : TierMode) (context : ContextMode) :
    (profile PDERow5DirectedExhaustiveness.visibleBoundaryProfile tier
      context).SuccessorFocus.Active
      (execution tier context).value := by
  change PDERow5DirectedExhaustiveness.visibleBoundaryProfile.TargetVisibleFocus.Active
    (execution tier context).value.previous
  unfold execution
  rw [DefectRouting.run_previous]
  exact predecessorActive

def generated (tier : TierMode) (context : ContextMode) :=
  (profile PDERow5DirectedExhaustiveness.visibleBoundaryProfile tier
    context).outputQuery.read
    (execution tier context).value (successorActive tier context)

theorem execution_retains_literal_row_five (tier : TierMode)
    (context : ContextMode) :
    (execution tier context).value.previous = predecessor :=
  DefectRouting.run_previous
    (profile PDERow5DirectedExhaustiveness.visibleBoundaryProfile tier context)
    predecessor

theorem execution_retains_root_residual (tier : TierMode)
    (context : ContextMode) :
    Residual.residualOf (execution tier context).value = () :=
  rfl

theorem active_execution_exact_work (tier : TierMode)
    (context : ContextMode) :
    (execution tier context).checks =
      1 + expectedTierChecks tier + expectedContextChecks context := by
  cases tier <;> cases context <;> decide

def unalignedActive (tier : TierMode) (context : ContextMode) :
    (profile PDERow5DirectedExhaustiveness.visibleBoundaryProfile tier
      context).UnalignedFocus.Active
      (execution tier context).value where
  parent := successorActive tier context
  accepted := every_active_pair_remains_unaligned tier context

theorem capacity_ready_focus_rejects_unaligned (tier : TierMode)
    (context : ContextMode) :
    Not ((profile PDERow5DirectedExhaustiveness.visibleBoundaryProfile tier
      context).CapacityReadyFocus.Active
      (execution tier context).value) := by
  intro selected
  have impossible := selected.accepted
  change (generated tier context).disposition = .capacityReady at impossible
  have unaligned : (generated tier context).disposition = .unaligned := by
    cases tier <;> cases context <;> rfl
  rw [unaligned] at impossible
  cases impossible

theorem target_visible_focus_rejects_unaligned (tier : TierMode)
    (context : ContextMode) :
    Not ((profile PDERow5DirectedExhaustiveness.visibleBoundaryProfile tier
      context).TargetVisibleHarmonicFocus.Active
      (execution tier context).value) := by
  intro selected
  have impossible := selected.accepted
  change (generated tier context).disposition =
    .targetVisibleHarmonic at impossible
  have unaligned : (generated tier context).disposition = .unaligned := by
    cases tier <;> cases context <;> rfl
  rw [unaligned] at impossible
  cases impossible

def queriedUnaligned (tier : TierMode) (context : ContextMode) :=
  (profile PDERow5DirectedExhaustiveness.visibleBoundaryProfile tier
    context).unalignedOutputQuery.read
    (execution tier context).value (unalignedActive tier context)

theorem unaligned_query_reads_the_exact_output (tier : TierMode)
    (context : ContextMode) :
    (queriedUnaligned tier context).val = generated tier context :=
  rfl

/-! ## Inactive row-5 siblings -/

def positiveGapExecution :=
  DefectRouting.run
    (profile PDERow5DirectedExhaustiveness.fullRankProfile
      .tierOne .realization)
    PDERow5DirectedExhaustiveness.fullRankRun.value

def zeroBoundaryExecution :=
  DefectRouting.run
    (profile PDERow5DirectedExhaustiveness.zeroBoundaryProfile
      .tierOne .realization)
    PDERow5DirectedExhaustiveness.zeroBoundaryRun.value

theorem positive_gap_sibling_pays_only_focus :
    positiveGapExecution.checks =
      PDERow5DirectedExhaustiveness.fullRankProfile.TargetVisibleFocus.selectionBudget.checks
        PDERow5DirectedExhaustiveness.fullRankRun.value :=
  DefectRouting.run_checks_of_inactive
    (profile PDERow5DirectedExhaustiveness.fullRankProfile
      .tierOne .realization)
    PDERow5DirectedExhaustiveness.fullRankRun.value
    PDERow5DirectedExhaustiveness.fullRankRefinedInactive

theorem zero_boundary_sibling_pays_only_focus :
    zeroBoundaryExecution.checks =
      PDERow5DirectedExhaustiveness.zeroBoundaryProfile.TargetVisibleFocus.selectionBudget.checks
        PDERow5DirectedExhaustiveness.zeroBoundaryRun.value :=
  DefectRouting.run_checks_of_inactive
    (profile PDERow5DirectedExhaustiveness.zeroBoundaryProfile
      .tierOne .realization)
    PDERow5DirectedExhaustiveness.zeroBoundaryRun.value
    PDERow5DirectedExhaustiveness.zeroBoundaryRefinedInactive

theorem inactive_sibling_checks_are_exact :
    positiveGapExecution.checks = 1 /\
      zeroBoundaryExecution.checks = 1 := by
  decide

theorem every_active_execution_is_bounded (tier : TierMode)
    (context : ContextMode) :
    (execution tier context).checks <=
      (PDERow5DirectedExhaustiveness.visibleBoundaryProfile.TargetVisibleFocus.selectionBudget.add
        (DefectRouting.payloadBudget
          (profile PDERow5DirectedExhaustiveness.visibleBoundaryProfile tier
            context))).coefficient *
      ((PDERow5DirectedExhaustiveness.visibleBoundaryProfile.TargetVisibleFocus.selectionBudget.add
        (DefectRouting.payloadBudget
          (profile PDERow5DirectedExhaustiveness.visibleBoundaryProfile tier
            context))).size
          predecessor + 1) ^
      (PDERow5DirectedExhaustiveness.visibleBoundaryProfile.TargetVisibleFocus.selectionBudget.add
        (DefectRouting.payloadBudget
          (profile PDERow5DirectedExhaustiveness.visibleBoundaryProfile tier
            context))).degree :=
  DefectRouting.run_checks_bounded
    (profile PDERow5DirectedExhaustiveness.visibleBoundaryProfile tier context)
    predecessor

#print axioms every_pair_has_exact_terminals
#print axioms both_generators_have_exact_work
#print axioms every_active_pair_remains_unaligned
#print axioms execution_retains_literal_row_five
#print axioms execution_retains_root_residual
#print axioms active_execution_exact_work
#print axioms capacity_ready_focus_rejects_unaligned
#print axioms target_visible_focus_rejects_unaligned
#print axioms inactive_sibling_checks_are_exact
#print axioms every_active_execution_is_bounded

end

end Hypostructure.Fixtures.PDERow6DefectRoutingRaw
