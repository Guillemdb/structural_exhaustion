import Hypostructure.Fixtures.PDEStructuralGradient
import Hypostructure.PDE.FastTrack.DirectedExhaustiveness

/-!
# PDE row-5 directed-exhaustiveness fixture

One literal unit predecessor is focused by Core and passed to three finite
row-5 registrations.  The registrations exercise all public terminals:

* CT15 full rank, followed by an explicit analytic bridge to the positive gap
  of the finite identity structural gradient;
* CT15 rank drop, CT16 exact code, and target-complete ClassClosure exhaustion;
* CT15 rank drop, CT16 code mismatch, and the first exact target-visible class.

The fixture supplies only finite schedules, primitive decisions, represented
quotients, and semantic bridge laws.  The row-5 executor owns every scan,
route, generated output, ledger extension, and exact work count.
-/

namespace Hypostructure.Fixtures.PDERow5DirectedExhaustiveness

open Hypostructure
open Hypostructure.Core
open Hypostructure.Core.NormalForm
open Hypostructure.Core.Residual
open Hypostructure.PDE
open Hypostructure.PDE.FastTrack
open Hypostructure.Fixtures

noncomputable section

/-! ## One literal focused predecessor -/

abbrev Previous := Core.Residual.Ledger Unit

def previous : Previous :=
  Core.Residual.Ledger.initial ()

def focus := Focus.always Previous

abbrev View := DirectedExhaustiveness.ActiveView focus

def active : focus.Active previous :=
  trivial

def view : View :=
  Focus.ActiveView.of previous active

def predecessorQuery : Core.Residual.Query Previous fun _previous => Unit :=
  Core.Residual.Query.residual

def predecessorActiveQuery : Focus.ActiveQuery focus fun _previous _proof => Unit :=
  Focus.ActiveQuery.ofQuery predecessorQuery

def viewQuery : Core.Residual.Query View fun _view => View :=
  Core.Residual.Query.residual

def gradientQuery : Focus.ActiveQuery focus fun _previous _proof =>
    StructuralGradient Real Real :=
  predecessorActiveQuery.map fun _previous _proof _residual =>
    PDEStructuralGradient.identityGradient

def criterionQuery : Focus.ActiveQuery focus fun _previous _proof =>
    StructuralGradient.ClosedRangeCriterion
      PDEStructuralGradient.identityGradient :=
  predecessorActiveQuery.map fun _previous _proof _residual =>
    PDEStructuralGradient.identityCriterion

/-! ## Exact finite schedules -/

def unitSchedule : Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.singleton ()

def unitScheduleQuery : Core.Residual.Query View fun _view =>
    Core.Finite.Enumeration Unit :=
  viewQuery.map fun _view _root => unitSchedule

def boolVisibleSchedule : Core.Finite.Enumeration Bool :=
  Core.Finite.Enumeration.singleton true

def boolVisibleScheduleQuery : Core.Residual.Query View fun _view =>
    Core.Finite.Enumeration Bool :=
  viewQuery.map fun _view _root => boolVisibleSchedule

/-! ## CT15 full-rank and rank-drop registrations -/

def fullRankSpec : CT15.Spec View where
  Coordinate := fun _view => Unit
  TargetDependent := fun _view _coordinate => False
  charge := fun _view _coordinate => 0
  capacity := fun _view => 0

def fullRankCapability : CT15.Capability fullRankSpec where
  coordinates := unitScheduleQuery
  targetDependentDecidable := fun _view _coordinate => isFalse id
  inputSize := fun _view => 1
  workCoefficient := 2
  workDegree := 1
  workBound := by
    intro current
    change 3 <= 2 * (1 + 1) ^ 1
    decide

def rankDropSpec : CT15.Spec View where
  Coordinate := fun _view => Unit
  TargetDependent := fun _view _coordinate => True
  charge := fun _view _coordinate => 0
  capacity := fun _view => 0

def rankDropCapability : CT15.Capability rankDropSpec where
  coordinates := unitScheduleQuery
  targetDependentDecidable := fun _view _coordinate => isTrue trivial
  inputSize := fun _view => 1
  workCoefficient := 2
  workDegree := 1
  workBound := by
    intro current
    change 3 <= 2 * (1 + 1) ^ 1
    decide

/-! ## Counted CT16 exact-code and mismatch registrations -/

def supportSpec (closed target : Bool) : CT16.Spec View where
  Coordinate := fun _view => Unit
  InSupport := fun _view _coordinate => True
  ClosedCode := fun _view => Bool
  closedCode := fun _view => closed
  targetCode := fun _view => target

def codeBudget : Core.PolynomialCheckBudget View :=
  Core.PolynomialCheckBudget.constant (fun _view => 1) 2

def codeComputation (closed target : Bool) :
    CT16.ClosedCodeComputation (supportSpec closed target) where
  run := fun _view => ⟨closed, 2⟩
  correct := by intros; rfl
  budget := codeBudget
  checks_eq := by intros; rfl

def equalityDecision (closed target : Bool) :
    CT16.CodeEqualityDecision (supportSpec closed target) :=
  CT16.CodeEqualityDecision.unitCost (fun _view => 1) fun _view => by
    change DecidableEq Bool
    infer_instance

def supportCapability (closed target : Bool) :
    CT16.Capability (supportSpec closed target) where
  coordinates := unitScheduleQuery
  inSupportDecidable := fun _view _coordinate => isTrue trivial
  codeComputation := codeComputation closed target
  equalityDecision := equalityDecision closed target

abbrev exactSupportSpec := supportSpec false false
abbrev exactSupportCapability := supportCapability false false

abbrev mismatchSupportSpec := supportSpec true false
abbrev mismatchSupportCapability := supportCapability true false

/-! ## Target-complete unit quotient for the exact-code branch -/

def unitClosure : Core.ClosureOperator Unit :=
  Core.ClosureOperator.identity Unit

def unitTargetNull (_carrier : Unit) : Prop :=
  True

def unitLedger : Core.ClosedClassLedger unitClosure unitTargetNull where
  classes := Set.univ
  closed := rfl
  targetNull := by simp [unitTargetNull]

def unitQuotientUniversal :
    Core.QuotientUniversalProperty (fun _carrier : Unit => ()) where
  descend := fun map _compatible _quotientClass => map ()
  descend_project := by intros; rfl
  descend_unique := by
    intro Result map compatible candidate commutes quotientClass
    cases quotientClass
    exact commutes ()

def unitQuotient : Core.LedgerQuotient unitLedger where
  Quotient := Unit
  project := fun _carrier => ()
  null := ()
  killsClosed := by intros; rfl
  universal := unitQuotientUniversal

def unitFamilyQuery : Core.Residual.Query View fun _view =>
    Core.Finite.Enumeration Unit :=
  unitScheduleQuery

def unitLedgerQuery : Core.Residual.Query View fun _view =>
    Core.ClosedClassLedger unitClosure unitTargetNull :=
  viewQuery.map fun _view _root => unitLedger

def zeroClosureProfile : ClassClosure.Profile View where
  Carrier := Unit
  closure := unitClosure
  TargetNull := unitTargetNull
  family := unitFamilyQuery
  ledger := unitLedgerQuery
  quotient := fun _view => unitQuotient
  TargetVisible := fun _view _quotientClass => False
  targetVisibleDecidable := fun _view _quotientClass => isFalse id
  visibleNonzero := by simp
  nullOfNotVisible := by intros; rfl
  targetNullOfNull := by simp [unitTargetNull]
  closureStable := Core.ClosureStable.identity

def zeroTargetComplete : ClassClosure.TargetComplete zeroClosureProfile where
  representsNonzero := by
    intro current quotientClass nonzero
    exact (nonzero (by cases quotientClass; rfl)).elim

def nextUnitQuotient (current : View)
    (avoids : zeroClosureProfile.AvoidsTargetVisible current) :
    Core.LedgerQuotient (zeroClosureProfile.extendedLedger current avoids) where
  Quotient := Unit
  project := fun _carrier => ()
  null := ()
  killsClosed := by intros; rfl
  universal := unitQuotientUniversal

def zeroClosureRegistration :
    ClassClosure.ExtensionRegistration zeroClosureProfile where
  nextQuotient := nextUnitQuotient
  quotientTransport := fun _current _avoids _quotientClass => ()
  quotientTransport_project := by intros; rfl
  quotientTransport_null := by intros; rfl

/-! ## Complete Bool quotient with one exact visible class -/

def boolClosure : Core.ClosureOperator Bool :=
  Core.ClosureOperator.identity Bool

def boolTargetNull (carrier : Bool) : Prop :=
  carrier = false

def boolLedger : Core.ClosedClassLedger boolClosure boolTargetNull where
  classes := {carrier | carrier = false}
  closed := rfl
  targetNull := by
    intro carrier closed
    exact closed

def boolQuotientUniversal :
    Core.QuotientUniversalProperty (fun carrier : Bool => carrier) where
  descend := fun map _compatible quotientClass => map quotientClass
  descend_project := by intros; rfl
  descend_unique := by
    intro Result map compatible candidate commutes quotientClass
    exact commutes quotientClass

def boolQuotient : Core.LedgerQuotient boolLedger where
  Quotient := Bool
  project := id
  null := false
  killsClosed := by
    intro carrier closed
    exact closed
  universal := boolQuotientUniversal

def boolLedgerQuery : Core.Residual.Query View fun _view =>
    Core.ClosedClassLedger boolClosure boolTargetNull :=
  viewQuery.map fun _view _root => boolLedger

def visibleClosureProfile : ClassClosure.Profile View where
  Carrier := Bool
  closure := boolClosure
  TargetNull := boolTargetNull
  family := boolVisibleScheduleQuery
  ledger := boolLedgerQuery
  quotient := fun _view => boolQuotient
  TargetVisible := fun _view quotientClass => quotientClass = true
  targetVisibleDecidable := fun _view quotientClass =>
    Bool.decEq quotientClass true
  visibleNonzero := by
    intro current carrier visible equalNull
    change carrier = true at visible
    change carrier = false at equalNull
    simp_all
  nullOfNotVisible := by
    intro current carrier invisible
    change Not (carrier = true) at invisible
    change carrier = false
    cases carrier with
    | false => rfl
    | true => exact (invisible rfl).elim
  targetNullOfNull := by
    intro current carrier equalNull
    exact equalNull
  closureStable := Core.ClosureStable.identity

def visibleTargetComplete :
    ClassClosure.TargetComplete visibleClosureProfile where
  representsNonzero := by
    intro current quotientClass nonzero
    cases quotientClass with
    | false => exact (nonzero rfl).elim
    | true =>
        refine ⟨true, ?_, rfl, rfl⟩
        change true ∈ [true]
        simp

def nextBoolQuotient (current : View)
    (avoids : visibleClosureProfile.AvoidsTargetVisible current) :
    Core.LedgerQuotient
      (visibleClosureProfile.extendedLedger current avoids) where
  Quotient := Bool
  project := id
  null := false
  killsClosed := by
    intro carrier closed
    exact (visibleClosureProfile.extendedLedger current avoids).targetNull
      closed
  universal := boolQuotientUniversal

def visibleClosureRegistration :
    ClassClosure.ExtensionRegistration visibleClosureProfile where
  nextQuotient := nextBoolQuotient
  quotientTransport := fun _current _avoids => id
  quotientTransport_project := by intros; rfl
  quotientTransport_null := by intros; rfl

/-! ## Semantic bridges required by row 5 -/

def fullRankBridge : DirectedExhaustiveness.FullRankToGap focus gradientQuery
    fullRankSpec fullRankCapability where
  fromC4 := fun _view _output => PDEStructuralGradient.identityGap
  fromFullRankLedger := fun _view _output => PDEStructuralGradient.identityGap

def rankDropBridge : DirectedExhaustiveness.FullRankToGap focus gradientQuery
    rankDropSpec rankDropCapability where
  fromC4 := fun _view _output => PDEStructuralGradient.identityGap
  fromFullRankLedger := fun _view _output => PDEStructuralGradient.identityGap

def exactCodeAlignmentFull : DirectedExhaustiveness.CodeClosureAlignment focus
    fullRankSpec fullRankCapability exactSupportSpec exactSupportCapability
    zeroClosureProfile where
  properSupportImpossible := by
    intro current rankDrop proper
    exact proper.residual.absent trivial
  exactCodeAvoids := by
    intro current rankDrop exact index visible
    exact visible
  mismatchVisible := by
    intro current rankDrop mismatch
    exact (mismatch.residual.notEqual mismatch.residual.state.exact).elim

def exactCodeAlignmentDrop : DirectedExhaustiveness.CodeClosureAlignment focus
    rankDropSpec rankDropCapability exactSupportSpec exactSupportCapability
    zeroClosureProfile where
  properSupportImpossible := by
    intro current rankDrop proper
    exact proper.residual.absent trivial
  exactCodeAvoids := by
    intro current rankDrop exact index visible
    exact visible
  mismatchVisible := by
    intro current rankDrop mismatch
    exact (mismatch.residual.notEqual mismatch.residual.state.exact).elim

def mismatchAlignment : DirectedExhaustiveness.CodeClosureAlignment focus
    rankDropSpec rankDropCapability mismatchSupportSpec
    mismatchSupportCapability visibleClosureProfile where
  properSupportImpossible := by
    intro current rankDrop proper
    exact proper.residual.absent trivial
  exactCodeAvoids := by
    intro current rankDrop exact
    have impossible : true = false :=
      exact.certificate.state.exact.symm.trans exact.certificate.equal
    exact Bool.noConfusion impossible
  mismatchVisible := by
    intro current rankDrop mismatch
    rfl

/-! Every semantic law is retrieved from the literal predecessor through the
same active-query anchor.  No law is installed through a free query
constructor or copied into an application state. -/

def zeroTargetCompleteQuery : Focus.ActiveQuery focus fun _previous _proof =>
    ClassClosure.TargetComplete zeroClosureProfile :=
  predecessorActiveQuery.map fun _previous _proof _residual =>
    zeroTargetComplete

def visibleTargetCompleteQuery : Focus.ActiveQuery focus fun _previous _proof =>
    ClassClosure.TargetComplete visibleClosureProfile :=
  predecessorActiveQuery.map fun _previous _proof _residual =>
    visibleTargetComplete

def fullRankBridgeQuery : Focus.ActiveQuery focus fun _previous _proof =>
    DirectedExhaustiveness.FullRankToGap focus gradientQuery
      fullRankSpec fullRankCapability :=
  predecessorActiveQuery.map fun _previous _proof _residual =>
    fullRankBridge

def rankDropBridgeQuery : Focus.ActiveQuery focus fun _previous _proof =>
    DirectedExhaustiveness.FullRankToGap focus gradientQuery
      rankDropSpec rankDropCapability :=
  predecessorActiveQuery.map fun _previous _proof _residual =>
    rankDropBridge

def exactCodeAlignmentFullQuery : Focus.ActiveQuery focus fun _previous _proof =>
    DirectedExhaustiveness.CodeClosureAlignment focus fullRankSpec
      fullRankCapability exactSupportSpec exactSupportCapability
        zeroClosureProfile :=
  predecessorActiveQuery.map fun _previous _proof _residual =>
    exactCodeAlignmentFull

def exactCodeAlignmentDropQuery : Focus.ActiveQuery focus fun _previous _proof =>
    DirectedExhaustiveness.CodeClosureAlignment focus rankDropSpec
      rankDropCapability exactSupportSpec exactSupportCapability
        zeroClosureProfile :=
  predecessorActiveQuery.map fun _previous _proof _residual =>
    exactCodeAlignmentDrop

def mismatchAlignmentQuery : Focus.ActiveQuery focus fun _previous _proof =>
    DirectedExhaustiveness.CodeClosureAlignment focus rankDropSpec
      rankDropCapability mismatchSupportSpec mismatchSupportCapability
        visibleClosureProfile :=
  predecessorActiveQuery.map fun _previous _proof _residual =>
    mismatchAlignment

/-! ## Three complete row-5 registrations -/

def fullRankProfile : DirectedExhaustiveness.Profile Previous focus Real Real where
  gradient := gradientQuery
  closedRangeCriterion := criterionQuery
  rankSpec := fullRankSpec
  rankCapability := fullRankCapability
  supportSpec := exactSupportSpec
  supportCapability := exactSupportCapability
  closureProfile := zeroClosureProfile
  closureRegistration := zeroClosureRegistration
  targetComplete := zeroTargetCompleteQuery
  InWindow := fun _view _carrier => False
  targetCapacity := fun _view _carrier => 0
  targetFlux := fun _view _carrier => 0
  inWindowOfVisible := by intros current carrier visible; exact visible
  positiveCapacityOfVisible := by intros current carrier visible; exact visible.elim
  nonzeroFluxOfVisible := by intros current carrier visible; exact visible.elim
  fullRankToGap := fullRankBridgeQuery
  codeClosureAlignment := exactCodeAlignmentFullQuery

def zeroBoundaryProfile : DirectedExhaustiveness.Profile Previous focus Real Real where
  gradient := gradientQuery
  closedRangeCriterion := criterionQuery
  rankSpec := rankDropSpec
  rankCapability := rankDropCapability
  supportSpec := exactSupportSpec
  supportCapability := exactSupportCapability
  closureProfile := zeroClosureProfile
  closureRegistration := zeroClosureRegistration
  targetComplete := zeroTargetCompleteQuery
  InWindow := fun _view _carrier => False
  targetCapacity := fun _view _carrier => 0
  targetFlux := fun _view _carrier => 0
  inWindowOfVisible := by intros current carrier visible; exact visible
  positiveCapacityOfVisible := by intros current carrier visible; exact visible.elim
  nonzeroFluxOfVisible := by intros current carrier visible; exact visible.elim
  fullRankToGap := rankDropBridgeQuery
  codeClosureAlignment := exactCodeAlignmentDropQuery

def visibleBoundaryProfile : DirectedExhaustiveness.Profile Previous focus Real Real where
  gradient := gradientQuery
  closedRangeCriterion := criterionQuery
  rankSpec := rankDropSpec
  rankCapability := rankDropCapability
  supportSpec := mismatchSupportSpec
  supportCapability := mismatchSupportCapability
  closureProfile := visibleClosureProfile
  closureRegistration := visibleClosureRegistration
  targetComplete := visibleTargetCompleteQuery
  InWindow := fun _view carrier => carrier = true
  targetCapacity := fun _view carrier =>
    match carrier with
    | false => 0
    | true => 2
  targetFlux := fun _view carrier =>
    match carrier with
    | false => 0
    | true => 3
  inWindowOfVisible := by
    intro current carrier visible
    exact visible
  positiveCapacityOfVisible := by
    intro current carrier visible
    change carrier = true at visible
    simp [visible]
  nonzeroFluxOfVisible := by
    intro current carrier visible
    change carrier = true at visible
    simp [visible]
  fullRankToGap := rankDropBridgeQuery
  codeClosureAlignment := mismatchAlignmentQuery

/-! ## Public terminal coverage -/

def fullRankRun :=
  DirectedExhaustiveness.run fullRankProfile previous

def zeroBoundaryRun :=
  DirectedExhaustiveness.run zeroBoundaryProfile previous

def visibleBoundaryRun :=
  DirectedExhaustiveness.run visibleBoundaryProfile previous

def fullRankStageOutput :
    DirectedExhaustiveness.Output fullRankProfile previous active :=
  fullRankProfile.outputQuery.read fullRankRun.value active

def zeroBoundaryStageOutput :
    DirectedExhaustiveness.Output zeroBoundaryProfile previous active :=
  zeroBoundaryProfile.outputQuery.read zeroBoundaryRun.value active

def visibleBoundaryStageOutput :
    DirectedExhaustiveness.Output visibleBoundaryProfile previous active :=
  visibleBoundaryProfile.outputQuery.read visibleBoundaryRun.value active

def fullRankGeneration :=
  DirectedExhaustiveness.generateActiveCounted fullRankProfile view

def zeroBoundaryGeneration :=
  DirectedExhaustiveness.generateActiveCounted zeroBoundaryProfile view

def visibleBoundaryGeneration :=
  DirectedExhaustiveness.generateActiveCounted visibleBoundaryProfile view

theorem fullRank_terminal :
    fullRankStageOutput.terminal = .positiveStructuralGap := by
  decide

theorem zeroBoundary_terminal :
    zeroBoundaryStageOutput.terminal = .zeroBoundaryQuotient := by
  decide

theorem visibleBoundary_terminal :
    visibleBoundaryStageOutput.terminal = .targetVisibleBoundary := by
  decide

def visibleBoundaryRefinedActive :
    visibleBoundaryProfile.TargetVisibleFocus.Active visibleBoundaryRun.value :=
  match _selected : (visibleBoundaryProfile.TargetVisibleFocus.select
      visibleBoundaryRun.value).value with
  | .isTrue proof => proof
  | .isFalse absent =>
      False.elim (absent {
        parent := active
        accepted := visibleBoundary_terminal
      })

def fullRankRefinedInactive : Not
    (fullRankProfile.TargetVisibleFocus.Active fullRankRun.value) := by
  intro selected
  have terminal := selected.accepted
  have parentEq : selected.parent = active := Subsingleton.elim _ _
  cases parentEq
  change fullRankStageOutput.terminal = .targetVisibleBoundary at terminal
  rw [fullRank_terminal] at terminal
  cases terminal

def zeroBoundaryRefinedInactive : Not
    (zeroBoundaryProfile.TargetVisibleFocus.Active zeroBoundaryRun.value) := by
  intro selected
  have terminal := selected.accepted
  have parentEq : selected.parent = active := Subsingleton.elim _ _
  cases parentEq
  change zeroBoundaryStageOutput.terminal = .targetVisibleBoundary at terminal
  rw [zeroBoundary_terminal] at terminal
  cases terminal

def refinedTargetVisibleOutput :=
  visibleBoundaryProfile.targetVisibleBoundaryQuery.read
    visibleBoundaryRun.value visibleBoundaryRefinedActive

theorem target_visible_refinement_costs_one_check :
    (visibleBoundaryProfile.TargetVisibleFocus.select
      visibleBoundaryRun.value).checks = 1 :=
  rfl

theorem target_visible_selector_accepts_actual_branch :
    match (visibleBoundaryProfile.TargetVisibleFocus.select
      visibleBoundaryRun.value).value with
    | .isTrue _proof => True
    | .isFalse _absent => False := by
  change True
  trivial

theorem positive_gap_selector_rejects_actual_child :
    match (fullRankProfile.TargetVisibleFocus.select fullRankRun.value).value with
    | .isTrue _proof => False
    | .isFalse _absent => True := by
  change True
  trivial

theorem zero_quotient_selector_rejects_actual_child :
    match (zeroBoundaryProfile.TargetVisibleFocus.select
      zeroBoundaryRun.value).value with
    | .isTrue _proof => False
    | .isFalse _absent => True := by
  change True
  trivial

theorem closed_row_five_siblings_are_not_row_six_inputs :
    Not (fullRankProfile.TargetVisibleFocus.Active fullRankRun.value) /\
      Not (zeroBoundaryProfile.TargetVisibleFocus.Active
        zeroBoundaryRun.value) :=
  ⟨fullRankRefinedInactive, zeroBoundaryRefinedInactive⟩

theorem refined_target_visible_query_is_literal :
    refinedTargetVisibleOutput =
      visibleBoundaryStageOutput.targetVisibleOutput
        visibleBoundary_terminal := by
  have parentEq : visibleBoundaryRefinedActive.parent = active :=
    Subsingleton.elim _ _
  cases parentEq
  rfl

theorem fullRank_stops_after_ct15 :
    fullRankStageOutput.support = none /\
      fullRankStageOutput.classClosure = none := by
  decide

theorem zeroBoundary_exact_path :
    zeroBoundaryStageOutput.rank.terminal = .rankDrop /\
      zeroBoundaryStageOutput.support.map (fun output => output.terminal) =
        some .exactCode /\
      zeroBoundaryStageOutput.classClosure.map
        (fun output => output.terminal) = some .zeroQuotient := by
  decide

theorem visibleBoundary_mismatch_path :
    visibleBoundaryStageOutput.rank.terminal = .rankDrop /\
      visibleBoundaryStageOutput.support.map (fun output => output.terminal) =
        some .mismatch /\
      visibleBoundaryStageOutput.classClosure.map
        (fun output => output.terminal) = some .targetVisible := by
  decide

theorem fullRank_component_checks_exact :
    fullRankStageOutput.rank.checks = 3 /\
      fullRankStageOutput.checks = 3 := by
  decide

theorem zeroBoundary_component_checks_exact :
    zeroBoundaryStageOutput.rank.checks = 2 /\
      zeroBoundaryStageOutput.support.map (fun output => output.checks) =
        some 4 /\
      zeroBoundaryStageOutput.classClosure.map (fun output => output.checks) =
        some 1 /\
      zeroBoundaryStageOutput.checks = 7 := by
  decide

theorem visibleBoundary_component_checks_exact :
    visibleBoundaryStageOutput.rank.checks = 2 /\
      visibleBoundaryStageOutput.support.map (fun output => output.checks) =
        some 4 /\
      visibleBoundaryStageOutput.classClosure.map (fun output => output.checks) =
        some 1 /\
      visibleBoundaryStageOutput.checks = 7 := by
  decide

def positiveGapOutput : DirectedExhaustiveness.PositiveGapOutput fullRankProfile view :=
  fullRankStageOutput.positiveGapOutput fullRank_terminal

def zeroBoundaryOutput : DirectedExhaustiveness.ZeroBoundaryOutput zeroBoundaryProfile view :=
  zeroBoundaryStageOutput.zeroBoundaryOutput zeroBoundary_terminal

def targetVisibleOutput :
    DirectedExhaustiveness.TargetVisibleBoundaryOutput visibleBoundaryProfile view :=
  visibleBoundaryStageOutput.targetVisibleOutput visibleBoundary_terminal

theorem fullRank_gradient_is_identity :
    fullRankProfile.gradient.read previous active =
      PDEStructuralGradient.identityGradient :=
  rfl

theorem positiveGap_is_genuine :
    0 < positiveGapOutput.gap.gamma :=
  positiveGapOutput.gap.gamma_pos

theorem target_complete_boundary_is_zero :
    ClassClosure.BoundaryZero zeroClosureProfile view :=
  zeroBoundaryOutput.boundaryZero

theorem target_visible_carrier_is_true :
    targetVisibleOutput.closure.residual.hit.value = true :=
  targetVisibleOutput.closure.residual.targetVisible

theorem target_visible_is_in_window :
    visibleBoundaryProfile.InWindow view
      targetVisibleOutput.closure.residual.hit.value :=
  targetVisibleOutput.inWindow

theorem target_visible_capacity_exact :
    visibleBoundaryProfile.targetCapacity view
      targetVisibleOutput.closure.residual.hit.value = 2 := by
  rw [target_visible_carrier_is_true]
  simp [visibleBoundaryProfile]

theorem target_visible_capacity_positive :
    0 < visibleBoundaryProfile.targetCapacity view
      targetVisibleOutput.closure.residual.hit.value :=
  targetVisibleOutput.positiveCapacity

theorem target_visible_flux_exact :
    visibleBoundaryProfile.targetFlux view
      targetVisibleOutput.closure.residual.hit.value = 3 := by
  rw [target_visible_carrier_is_true]
  simp [visibleBoundaryProfile]

theorem target_visible_flux_nonzero :
    visibleBoundaryProfile.targetFlux view
      targetVisibleOutput.closure.residual.hit.value ≠ 0 :=
  targetVisibleOutput.nonzeroFlux

/-! ## Literal predecessor and exact counted work -/

theorem fullRank_previous_is_literal :
    fullRankRun.value.previous = previous :=
  DirectedExhaustiveness.run_previous fullRankProfile previous

theorem zeroBoundary_previous_is_literal :
    zeroBoundaryRun.value.previous = previous :=
  DirectedExhaustiveness.run_previous zeroBoundaryProfile previous

theorem visibleBoundary_previous_is_literal :
    visibleBoundaryRun.value.previous = previous :=
  DirectedExhaustiveness.run_previous visibleBoundaryProfile previous

theorem fullRank_checks_exact :
    fullRankGeneration.checks = 3 /\ fullRankRun.checks = 3 := by
  decide

theorem zeroBoundary_checks_exact :
    zeroBoundaryGeneration.checks = 7 /\ zeroBoundaryRun.checks = 7 := by
  decide

theorem visibleBoundary_checks_exact :
    visibleBoundaryGeneration.checks = 7 /\
      visibleBoundaryRun.checks = 7 := by
  decide

theorem fullRank_run_uses_registered_schedule :
    fullRankRun.checks =
      focus.selectionBudget.checks previous +
        (DirectedExhaustiveness.payloadBudget fullRankProfile).checks previous :=
  DirectedExhaustiveness.run_checks_of_active fullRankProfile previous active

theorem zeroBoundary_run_uses_registered_schedule :
    zeroBoundaryRun.checks =
      focus.selectionBudget.checks previous +
        (DirectedExhaustiveness.payloadBudget zeroBoundaryProfile).checks previous :=
  DirectedExhaustiveness.run_checks_of_active zeroBoundaryProfile previous active

theorem visibleBoundary_run_uses_registered_schedule :
    visibleBoundaryRun.checks =
      focus.selectionBudget.checks previous +
        (DirectedExhaustiveness.payloadBudget visibleBoundaryProfile).checks previous :=
  DirectedExhaustiveness.run_checks_of_active visibleBoundaryProfile previous active

theorem fullRank_work_is_bounded :
    fullRankRun.checks <=
      (focus.selectionBudget.add
        (DirectedExhaustiveness.payloadBudget fullRankProfile)).coefficient *
        ((focus.selectionBudget.add
          (DirectedExhaustiveness.payloadBudget fullRankProfile)).size previous + 1) ^
          (focus.selectionBudget.add
            (DirectedExhaustiveness.payloadBudget fullRankProfile)).degree :=
  DirectedExhaustiveness.run_checks_bounded fullRankProfile previous

theorem zeroBoundary_work_is_bounded :
    zeroBoundaryRun.checks <=
      (focus.selectionBudget.add
        (DirectedExhaustiveness.payloadBudget zeroBoundaryProfile)).coefficient *
        ((focus.selectionBudget.add
          (DirectedExhaustiveness.payloadBudget zeroBoundaryProfile)).size previous + 1) ^
          (focus.selectionBudget.add
            (DirectedExhaustiveness.payloadBudget zeroBoundaryProfile)).degree :=
  DirectedExhaustiveness.run_checks_bounded zeroBoundaryProfile previous

theorem visibleBoundary_work_is_bounded :
    visibleBoundaryRun.checks <=
      (focus.selectionBudget.add
        (DirectedExhaustiveness.payloadBudget visibleBoundaryProfile)).coefficient *
        ((focus.selectionBudget.add
          (DirectedExhaustiveness.payloadBudget visibleBoundaryProfile)).size previous + 1) ^
          (focus.selectionBudget.add
            (DirectedExhaustiveness.payloadBudget visibleBoundaryProfile)).degree :=
  DirectedExhaustiveness.run_checks_bounded visibleBoundaryProfile previous

#print axioms positiveGap_is_genuine
#print axioms target_complete_boundary_is_zero
#print axioms target_visible_carrier_is_true
#print axioms target_visible_capacity_positive
#print axioms target_visible_flux_nonzero
#print axioms fullRank_previous_is_literal
#print axioms fullRank_checks_exact
#print axioms zeroBoundary_checks_exact
#print axioms visibleBoundary_checks_exact
#print axioms fullRank_component_checks_exact
#print axioms zeroBoundary_component_checks_exact
#print axioms visibleBoundary_component_checks_exact
#print axioms target_visible_refinement_costs_one_check
#print axioms target_visible_selector_accepts_actual_branch
#print axioms positive_gap_selector_rejects_actual_child
#print axioms zero_quotient_selector_rejects_actual_child
#print axioms closed_row_five_siblings_are_not_row_six_inputs
#print axioms refined_target_visible_query_is_literal
#print axioms fullRank_work_is_bounded
#print axioms zeroBoundary_work_is_bounded
#print axioms visibleBoundary_work_is_bounded

end

end Hypostructure.Fixtures.PDERow5DirectedExhaustiveness
