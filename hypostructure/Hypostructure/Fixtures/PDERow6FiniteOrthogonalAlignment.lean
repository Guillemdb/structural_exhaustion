import Hypostructure.Fixtures.PDERow6DefectRoutingRaw
import Hypostructure.Fixtures.PDERows1To4
import Hypostructure.PDE.FastTrack.DefectRoutingAlignment

/-!
# Finite orthogonal alignment for PDE row 6

This fixture supplies a concrete one-dimensional Hilbert model for the strict
row-6 defect-routing API.  Row 5 owns a closed real class ledger `x <= 1` and
selects the first target-visible class `2`.  Row 4 computes the identity
intertwining defect.  Three row-6 profiles use the same CT13 and CT7
capabilities but different registered linear boundary coordinates:

* the identity geometry sends the selected class to the routable defect `1`;
* the zero geometry sends it to the nonzero closed harmonic defect `1`;
* the same zero geometry sends it to the target-visible harmonic defect `2`.

No semantic tag or route is supplied by the fixture.  The strict PDE wrapper
derives the decomposition, reads the unchanged ledger and quotient, proves the
unique semantic condition, and delegates the scan and successor construction
to Core.
-/

namespace Hypostructure.Fixtures.PDERow6FiniteOrthogonalAlignment

open Hypostructure
open Hypostructure.Core
open Hypostructure.Core.NormalForm
open Hypostructure.Core.Residual
open Hypostructure.PDE
open Hypostructure.PDE.FastTrack

noncomputable section

abbrev Previous := PDERow5DirectedExhaustiveness.Previous
abbrev ParentFocus := PDERow5DirectedExhaustiveness.focus
abbrev View := DirectedExhaustiveness.ActiveView ParentFocus
abbrev currentView : View :=
  Focus.ActiveView.of PDERow5DirectedExhaustiveness.previous
    PDERow5DirectedExhaustiveness.active

/-! ## A complete two-class real quotient at row 5 -/

def visibleSchedule : Core.Finite.Enumeration Real :=
  Core.Finite.Enumeration.singleton 2

def visibleScheduleQuery : Residual.Query View fun _view =>
    Core.Finite.Enumeration Real :=
  PDERow5DirectedExhaustiveness.viewQuery.map fun _view _root =>
    visibleSchedule

def realClosure : Core.ClosureOperator Real :=
  Core.ClosureOperator.identity Real

def realTargetNull (carrier : Real) : Prop :=
  carrier <= 1

def realLedger : Core.ClosedClassLedger realClosure realTargetNull where
  classes := {carrier | carrier <= 1}
  closed := rfl
  targetNull := fun member => member

def classProject (carrier : Real) : Bool :=
  decide (1 < carrier)

@[simp] theorem classProject_zero : classProject 0 = false := by
  norm_num [classProject]

@[simp] theorem classProject_one : classProject 1 = false := by
  norm_num [classProject]

@[simp] theorem classProject_two : classProject 2 = true := by
  norm_num [classProject]

def realQuotientUniversal :
    Core.QuotientUniversalProperty classProject where
  descend := fun map _compatible quotientClass =>
    if quotientClass then map 2 else map 0
  descend_project := by
    intro Result map compatible carrier
    by_cases visible : 1 < carrier
    · have same : classProject (2 : Real) = classProject carrier := by
        simp [classProject, visible]
      simpa [classProject, visible] using compatible same
    · have same : classProject (0 : Real) = classProject carrier := by
        simp [classProject, visible]
      simpa [classProject, visible] using compatible same
  descend_unique := by
    intro Result map compatible candidate commutes quotientClass
    cases quotientClass
    · simpa using commutes 0
    · simpa using commutes 2

def realQuotient : Core.LedgerQuotient realLedger where
  Quotient := Bool
  project := classProject
  null := false
  killsClosed := by
    intro carrier closed
    change carrier <= 1 at closed
    simp [classProject, not_lt.mpr closed]
  universal := realQuotientUniversal

def realLedgerQuery : Residual.Query View fun _view =>
    Core.ClosedClassLedger realClosure realTargetNull :=
  PDERow5DirectedExhaustiveness.viewQuery.map fun _view _root => realLedger

abbrev closureProfile : ClassClosure.Profile View where
  Carrier := Real
  closure := realClosure
  TargetNull := realTargetNull
  family := visibleScheduleQuery
  ledger := realLedgerQuery
  quotient := fun _view => realQuotient
  TargetVisible := fun _view quotientClass => quotientClass = true
  targetVisibleDecidable := fun _view quotientClass =>
    Bool.decEq quotientClass true
  visibleNonzero := by
    intro current carrier visible equalNull
    change classProject carrier = true at visible
    change classProject carrier = false at equalNull
    simp_all
  nullOfNotVisible := by
    intro current carrier invisible
    change Not (classProject carrier = true) at invisible
    change classProject carrier = false
    cases projected : classProject carrier <;> simp_all
  targetNullOfNull := by
    intro current carrier equalNull
    change classProject carrier = false at equalNull
    change carrier <= 1
    by_contra notClosed
    have visible : 1 < carrier := lt_of_not_ge notClosed
    have projected : classProject carrier = true := by
      simp [classProject, visible]
    simp_all
  closureStable := Core.ClosureStable.identity

def targetComplete : ClassClosure.TargetComplete closureProfile where
  representsNonzero := by
    intro current quotientClass nonzero
    cases quotientClass with
    | false => exact (nonzero rfl).elim
    | true =>
        refine ⟨(2 : Real), ?_, ?_, rfl⟩
        · change (2 : Real) ∈ [2]
          simp
        · exact classProject_two

@[simp] theorem familyAt_eq (current : View) :
    closureProfile.familyAt current = visibleSchedule :=
  rfl

theorem twoVisible (current : View) :
    closureProfile.IsTargetVisible current (2 : Real) := by
  change classProject 2 = true
  exact classProject_two

theorem noAvoids (current : View)
    (avoids : closureProfile.AvoidsTargetVisible current) : False := by
  let index : Fin (closureProfile.familyAt current).card :=
    ⟨0, by
      rw [familyAt_eq]
      change 0 < [(2 : Real)].length
      decide⟩
  have invisible := avoids index
  have selected : (closureProfile.familyAt current).get index = (2 : Real) := by
    simp [familyAt_eq, visibleSchedule, Core.Finite.Enumeration.get,
      Core.Finite.Enumeration.singleton, Core.Finite.Enumeration.ofNodupList]
  apply invisible
  rw [selected]
  exact twoVisible current

theorem hasVisible (current : View) :
    closureProfile.HasTargetVisible current := by
  rcases (closureProfile.scan current).hit_or_avoids with hit | avoids
  · exact hit
  · exact (noAvoids current avoids).elim

def closureRegistration :
    ClassClosure.ExtensionRegistration.{0, 0, 0, 0} closureProfile where
  nextQuotient := fun current avoids => (noAvoids current avoids).elim
  quotientTransport := fun current avoids => (noAvoids current avoids).elim
  quotientTransport_project := by
    intro current avoids
    exact (noAvoids current avoids).elim
  quotientTransport_null := by
    intro current avoids
    exact (noAvoids current avoids).elim

/-! ## One target-visible row-5 predecessor -/

def codeClosureAlignment : DirectedExhaustiveness.CodeClosureAlignment
    ParentFocus PDERow5DirectedExhaustiveness.rankDropSpec
      PDERow5DirectedExhaustiveness.rankDropCapability
      PDERow5DirectedExhaustiveness.mismatchSupportSpec
      PDERow5DirectedExhaustiveness.mismatchSupportCapability
      closureProfile where
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
    exact hasVisible current

def targetCompleteQuery : Focus.ActiveQuery ParentFocus
    fun _previous _proof => ClassClosure.TargetComplete closureProfile :=
  PDERow5DirectedExhaustiveness.predecessorActiveQuery.map
    fun _previous _proof _root => targetComplete

def codeClosureAlignmentQuery : Focus.ActiveQuery ParentFocus
    fun _previous _proof => DirectedExhaustiveness.CodeClosureAlignment
      ParentFocus PDERow5DirectedExhaustiveness.rankDropSpec
        PDERow5DirectedExhaustiveness.rankDropCapability
        PDERow5DirectedExhaustiveness.mismatchSupportSpec
        PDERow5DirectedExhaustiveness.mismatchSupportCapability
        closureProfile :=
  PDERow5DirectedExhaustiveness.predecessorActiveQuery.map
    fun _previous _proof _root => codeClosureAlignment

abbrev rowFiveProfile :
    DirectedExhaustiveness.Profile Previous ParentFocus Real Real where
  gradient := PDERow5DirectedExhaustiveness.gradientQuery
  closedRangeCriterion := PDERow5DirectedExhaustiveness.criterionQuery
  rankSpec := PDERow5DirectedExhaustiveness.rankDropSpec
  rankCapability := PDERow5DirectedExhaustiveness.rankDropCapability
  supportSpec := PDERow5DirectedExhaustiveness.mismatchSupportSpec
  supportCapability := PDERow5DirectedExhaustiveness.mismatchSupportCapability
  closureProfile := closureProfile
  closureRegistration := closureRegistration
  targetComplete := targetCompleteQuery
  InWindow := fun _view _carrier => True
  targetCapacity := fun _view _carrier => 1
  targetFlux := fun _view _carrier => 1
  inWindowOfVisible := by simp
  positiveCapacityOfVisible := by norm_num
  nonzeroFluxOfVisible := by norm_num
  fullRankToGap := PDERow5DirectedExhaustiveness.rankDropBridgeQuery
  codeClosureAlignment := codeClosureAlignmentQuery

def rowFiveRun :=
  DirectedExhaustiveness.run rowFiveProfile
    PDERow5DirectedExhaustiveness.previous

def rowFiveStageOutput :
    DirectedExhaustiveness.Output rowFiveProfile
      PDERow5DirectedExhaustiveness.previous
      PDERow5DirectedExhaustiveness.active :=
  rowFiveProfile.outputQuery.read rowFiveRun.value
    PDERow5DirectedExhaustiveness.active

theorem rank_terminal :
    (CT15.generateCounted PDERow5DirectedExhaustiveness.rankDropCapability
      currentView).value.terminal = .rankDrop := by
  decide

theorem support_terminal :
    (CT16.generateCounted PDERow5DirectedExhaustiveness.mismatchSupportSpec
      PDERow5DirectedExhaustiveness.mismatchSupportCapability
      currentView).value.terminal = .mismatch := by
  decide

theorem closure_terminal (current : View) :
    (ClassClosure.generateCounted closureProfile closureRegistration
      current).value.terminal = .targetVisible := by
  let generated :=
    (ClassClosure.generateCounted closureProfile closureRegistration current).value
  cases terminal : generated.terminal with
  | targetVisible => rfl
  | zeroQuotient =>
      let zero := generated.zeroQuotientPropagation terminal
      let hit := generated.scan.hitOfHasHit (by
        rw [generated.scan_eq]
        exact hasVisible current)
      exact (zero.avoids hit.index hit.sound).elim

theorem rowFive_terminal :
    rowFiveStageOutput.terminal = .targetVisibleBoundary := by
  have outputEq := DirectedExhaustiveness.outputQuery_run_of_active
    rowFiveProfile PDERow5DirectedExhaustiveness.previous
      PDERow5DirectedExhaustiveness.active
  change rowFiveStageOutput =
    DirectedExhaustiveness.generateActive rowFiveProfile
      currentView at outputEq
  rw [outputEq]
  unfold DirectedExhaustiveness.generateActive
  unfold DirectedExhaustiveness.generateActiveCounted
  simp only [Counted.bind, Counted.map, Counted.pure]
  split
  next isRank =>
    have impossible := isRank.symm.trans rank_terminal
    cases impossible
  next isRank =>
    have impossible := isRank.symm.trans rank_terminal
    cases impossible
  next isRank =>
    split
    next isSupport =>
      have impossible := isSupport.symm.trans support_terminal
      cases impossible
    next isSupport =>
      have impossible := isSupport.symm.trans support_terminal
      cases impossible
    next isSupport =>
      split
      next isClosure => rfl
      next isClosure =>
        have impossible :=
          isClosure.symm.trans (closure_terminal currentView)
        cases impossible

def rowFiveActive :
    rowFiveProfile.TargetVisibleFocus.Active rowFiveRun.value :=
  match _selected : (rowFiveProfile.TargetVisibleFocus.select rowFiveRun.value).value with
  | .isTrue proof => proof
  | .isFalse absent =>
      False.elim (absent {
        parent := PDERow5DirectedExhaustiveness.active
        accepted := rowFive_terminal
      })

def rowFiveBoundary :=
  rowFiveProfile.targetVisibleBoundaryQuery.read rowFiveRun.value rowFiveActive

theorem rowFive_selected_carrier :
    rowFiveBoundary.closure.residual.hit.value = (2 : Real) := by
  have member := rowFiveBoundary.closure.residual.hit.member
  have member' : rowFiveBoundary.closure.residual.hit.value ∈
      visibleSchedule.values := by
    simpa [rowFiveProfile, familyAt_eq] using member
  change rowFiveBoundary.closure.residual.hit.value ∈ [(2 : Real)] at member'
  simpa using member'

/-! ## Framework-computed identity defect with two exact geometries -/

abbrev PDEModel := PDERows1To4.FiniteScalar.model

noncomputable def harmonicGeometry : DefectGeometry Real where
  carrier := ⊤
  presentation := .boundedOperator {
    operator := 0
    operator_positive := ContinuousLinearMap.isPositive_zero
    carrier_invariant := by simp
  }

noncomputable def positiveDefectStage :=
  registerDefect PDERows1To4.QuotientDefect.formQuery
    PDERows1To4.QuotientDefect.quotientAt
    PDERows1To4.QuotientDefect.zeroGeneratorAt
    (fun _previous => PDERows1To4.QuotientDefect.topGeometry)
    PDERows1To4.Budgets.natStage

noncomputable def harmonicDefectStage :=
  registerDefect PDERows1To4.QuotientDefect.formQuery
    PDERows1To4.QuotientDefect.quotientAt
    PDERows1To4.QuotientDefect.zeroGeneratorAt
    (fun _previous => harmonicGeometry)
    PDERows1To4.Budgets.natStage

abbrev positiveRegistration : QuotientDefectRegistration PDEModel Real Real :=
  positiveDefectStage.added

abbrev harmonicRegistration : QuotientDefectRegistration PDEModel Real Real :=
  harmonicDefectStage.added

theorem positive_defect_apply (value : Real) :
    positiveRegistration.defect value = value := by
  change intertwiningDefect PDERows1To4.FiniteForm.closedGeneratorForm
    (PDERows1To4.QuotientDefect.representedQuotient
      PDERows1To4.FiniteForm.closedGeneratorForm)
    (PDERows1To4.QuotientDefect.zeroQuotientGenerator
      PDERows1To4.FiniteForm.closedGeneratorForm) value = value
  simp [intertwiningDefect,
    PDERows1To4.QuotientDefect.zeroQuotientGenerator,
    PDERows1To4.QuotientDefect.representedQuotient,
    PDERows1To4.FiniteForm.closedGeneratorForm]

theorem harmonic_defect_apply (value : Real) :
    harmonicRegistration.defect value = value := by
  change intertwiningDefect PDERows1To4.FiniteForm.closedGeneratorForm
    (PDERows1To4.QuotientDefect.representedQuotient
      PDERows1To4.FiniteForm.closedGeneratorForm)
    (PDERows1To4.QuotientDefect.zeroQuotientGenerator
      PDERows1To4.FiniteForm.closedGeneratorForm) value = value
  simp [intertwiningDefect,
    PDERows1To4.QuotientDefect.zeroQuotientGenerator,
    PDERows1To4.QuotientDefect.representedQuotient,
    PDERows1To4.FiniteForm.closedGeneratorForm]

def halfMap : Real →ₗ[Real] Real where
  toFun := fun value => value / 2
  map_add' := by intros; ring
  map_smul' := by intros; simp; ring

abbrev positiveRegistrationQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun _stage _active =>
      QuotientDefectRegistration PDEModel Real Real :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun _stage _active _boundary => positiveRegistration

abbrev harmonicRegistrationQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun _stage _active =>
      QuotientDefectRegistration PDEModel Real Real :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun _stage _active _boundary => harmonicRegistration

abbrev halfCoordinateQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun _stage _active =>
      Real →ₗ[Real] Real :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun _stage _active _boundary => halfMap

abbrev identityCoordinateQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun _stage _active =>
      Real →ₗ[Real] Real :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun _stage _active _boundary => LinearMap.id

theorem selectedCarrier_eq_two
    (stage : DefectRouting.RowFiveStage rowFiveProfile)
    (active : rowFiveProfile.TargetVisibleFocus.Active stage) :
    DefectRoutingAlignment.selectedCarrier rowFiveProfile stage active =
      (2 : Real) := by
  have member :=
    (rowFiveProfile.targetVisibleBoundaryQuery.read stage active).closure.residual.hit.member
  have member' :
      (rowFiveProfile.targetVisibleBoundaryQuery.read stage active).closure.residual.hit.value ∈
        visibleSchedule.values := by
    simpa [rowFiveProfile, familyAt_eq] using member
  change (rowFiveProfile.targetVisibleBoundaryQuery.read stage active).closure.residual.hit.value ∈
    [(2 : Real)] at member'
  simpa [DefectRoutingAlignment.selectedCarrier] using member'

theorem positive_exact_defect
    (stage : DefectRouting.RowFiveStage rowFiveProfile)
    (active : rowFiveProfile.TargetVisibleFocus.Active stage) :
    DefectRoutingAlignment.exactDefect rowFiveProfile
      positiveRegistrationQuery halfCoordinateQuery stage active = (1 : Real) := by
  change positiveRegistration.defect
    (halfMap (DefectRoutingAlignment.selectedCarrier rowFiveProfile stage active)) = 1
  rw [selectedCarrier_eq_two, positive_defect_apply]
  norm_num [halfMap]

theorem closed_exact_defect
    (stage : DefectRouting.RowFiveStage rowFiveProfile)
    (active : rowFiveProfile.TargetVisibleFocus.Active stage) :
    DefectRoutingAlignment.exactDefect rowFiveProfile
      harmonicRegistrationQuery halfCoordinateQuery stage active = (1 : Real) := by
  change harmonicRegistration.defect
    (halfMap (DefectRoutingAlignment.selectedCarrier rowFiveProfile stage active)) = 1
  rw [selectedCarrier_eq_two, harmonic_defect_apply]
  norm_num [halfMap]

theorem visible_exact_defect
    (stage : DefectRouting.RowFiveStage rowFiveProfile)
    (active : rowFiveProfile.TargetVisibleFocus.Active stage) :
    DefectRoutingAlignment.exactDefect rowFiveProfile
      harmonicRegistrationQuery identityCoordinateQuery stage active = (2 : Real) := by
  change harmonicRegistration.defect
    (LinearMap.id (DefectRoutingAlignment.selectedCarrier rowFiveProfile stage active)) = 2
  rw [selectedCarrier_eq_two, harmonic_defect_apply]
  rfl

theorem positive_harmonic_iff (state : Real) :
    positiveRegistration.geometry.IsHarmonic state ↔ state = 0 := by
  change (ContinuousLinearMap.id Real Real) state = 0 ↔ state = 0
  simp

theorem harmonic_is_harmonic (state : Real) :
    harmonicRegistration.geometry.IsHarmonic state := by
  change (0 : Real →L[Real] Real) state = 0
  simp

noncomputable def positiveContract (defect : Real) :
    DirectResistanceContract Real positiveRegistration.geometry defect Real where
  harmonicProjection := 0
  projection_idempotent := by simp
  projection_symmetric := by simp
  harmonic_is_harmonic := (positive_harmonic_iff 0).mpr rfl
  fixes_harmonic := by
    intro state harmonic
    have equal := (positive_harmonic_iff state).mp harmonic
    subst state
    rfl
  routableResistance := ENNReal.ofReal (defect ^ 2)
  finiteDecidable := inferInstance
  action := id
  energy := fun potential => potential ^ 2
  energy_nonnegative := sq_nonneg
  finite_of_compensator := by simp
  compensator := fun _finite => defect
  compensates := by simp
  compensation_energy := by
    intros
    simp [ENNReal.toReal_ofReal, sq_nonneg]
  minimal_energy := by
    intro finite potential compensates
    have equal : potential = defect := by simpa using compensates
    subst potential
    rfl
  nonzero_harmonic_not_routable := by
    intro nonzero
    exact (nonzero rfl).elim
  symmetricEnergy := fun state => ‖state‖ ^ 2
  symmetricEnergy_nonnegative := fun state => sq_nonneg ‖state‖
  drift_bound := by
    intro finite state
    simp [ENNReal.toReal_ofReal, sq_nonneg, Real.sqrt_sq_eq_abs,
      Real.norm_eq_abs, abs_mul, mul_comm]

noncomputable def harmonicContract (defect : Real) :
    DirectResistanceContract Real harmonicRegistration.geometry defect Unit where
  harmonicProjection := ContinuousLinearMap.id Real Real
  projection_idempotent := by simp
  projection_symmetric := by simp
  harmonic_is_harmonic := harmonic_is_harmonic defect
  fixes_harmonic := by simp
  routableResistance := 0
  finiteDecidable := inferInstance
  action := fun _potential => 0
  energy := fun _potential => 0
  energy_nonnegative := by simp
  finite_of_compensator := by norm_num
  compensator := fun _finite => ()
  compensates := by simp
  compensation_energy := by simp
  minimal_energy := by simp
  nonzero_harmonic_not_routable := by
    intro nonzero
    rintro ⟨potential, equal⟩
    exact nonzero equal.symm
  symmetricEnergy := fun _state => 0
  symmetricEnergy_nonnegative := by simp
  drift_bound := by
    intro finite state
    simpa using abs_real_inner_le_norm defect state

abbrev positiveContractQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      DirectResistanceContract Real
        (positiveRegistrationQuery.read stage active).geometry
        (DefectRoutingAlignment.exactDefect rowFiveProfile
          positiveRegistrationQuery halfCoordinateQuery stage active)
        Real :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun stage active _boundary =>
      positiveContract (DefectRoutingAlignment.exactDefect rowFiveProfile
        positiveRegistrationQuery halfCoordinateQuery stage active)

abbrev closedContractQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      DirectResistanceContract Real
        (harmonicRegistrationQuery.read stage active).geometry
        (DefectRoutingAlignment.exactDefect rowFiveProfile
          harmonicRegistrationQuery halfCoordinateQuery stage active)
        Unit :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun stage active _boundary =>
      harmonicContract (DefectRoutingAlignment.exactDefect rowFiveProfile
        harmonicRegistrationQuery halfCoordinateQuery stage active)

abbrev visibleContractQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      DirectResistanceContract Real
        (harmonicRegistrationQuery.read stage active).geometry
        (DefectRoutingAlignment.exactDefect rowFiveProfile
          harmonicRegistrationQuery identityCoordinateQuery stage active)
        Unit :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun stage active _boundary =>
      harmonicContract (DefectRoutingAlignment.exactDefect rowFiveProfile
        harmonicRegistrationQuery identityCoordinateQuery stage active)

def zeroClosedQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      (0 : Real) ∈
        (DefectRoutingAlignment.CurrentLedgerAt rowFiveProfile stage active).classes :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun _stage _active _boundary => by
      change (0 : Real) <= 1
      norm_num

noncomputable def positiveZeroDecision : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      Decidable ((positiveContractQuery.read stage active).harmonic = 0) :=
  rowFiveProfile.targetVisibleBoundaryQuery.map fun stage active _boundary =>
    Classical.propDecidable
      ((positiveContractQuery.read stage active).harmonic = 0)

noncomputable def positiveLedgerDecision : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      Decidable ((positiveContractQuery.read stage active).harmonic ∈
        (DefectRoutingAlignment.CurrentLedgerAt rowFiveProfile stage active).classes) :=
  rowFiveProfile.targetVisibleBoundaryQuery.map fun stage active _boundary =>
    Classical.propDecidable
      ((positiveContractQuery.read stage active).harmonic ∈
        (DefectRoutingAlignment.CurrentLedgerAt rowFiveProfile stage active).classes)

noncomputable def closedZeroDecision : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      Decidable ((closedContractQuery.read stage active).harmonic = 0) :=
  rowFiveProfile.targetVisibleBoundaryQuery.map fun stage active _boundary =>
    Classical.propDecidable
      ((closedContractQuery.read stage active).harmonic = 0)

noncomputable def closedLedgerDecision : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      Decidable ((closedContractQuery.read stage active).harmonic ∈
        (DefectRoutingAlignment.CurrentLedgerAt rowFiveProfile stage active).classes) :=
  rowFiveProfile.targetVisibleBoundaryQuery.map fun stage active _boundary =>
    Classical.propDecidable
      ((closedContractQuery.read stage active).harmonic ∈
        (DefectRoutingAlignment.CurrentLedgerAt rowFiveProfile stage active).classes)

noncomputable def visibleZeroDecision : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      Decidable ((visibleContractQuery.read stage active).harmonic = 0) :=
  rowFiveProfile.targetVisibleBoundaryQuery.map fun stage active _boundary =>
    Classical.propDecidable
      ((visibleContractQuery.read stage active).harmonic = 0)

noncomputable def visibleLedgerDecision : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      Decidable ((visibleContractQuery.read stage active).harmonic ∈
        (DefectRoutingAlignment.CurrentLedgerAt rowFiveProfile stage active).classes) :=
  rowFiveProfile.targetVisibleBoundaryQuery.map fun stage active _boundary =>
    Classical.propDecidable
      ((visibleContractQuery.read stage active).harmonic ∈
        (DefectRoutingAlignment.CurrentLedgerAt rowFiveProfile stage active).classes)

def positiveRoutingComplete : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      DefectRoutingAlignment.RoutingCompleteAt rowFiveProfile
        (positiveContractQuery.read stage active) stage active :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun stage active _boundary => by
      constructor
      left
      constructor
      · simp [DirectResistanceContract.Finite, positiveContract]
      · rfl

def closedRoutingComplete : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      DefectRoutingAlignment.RoutingCompleteAt rowFiveProfile
        (closedContractQuery.read stage active) stage active :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun stage active _boundary => by
      constructor
      right
      left
      refine ⟨?_, ?_, ?_⟩
      · norm_num [DirectResistanceContract.Finite, harmonicContract]
      · change DefectRoutingAlignment.exactDefect rowFiveProfile
          harmonicRegistrationQuery halfCoordinateQuery stage active ≠ 0
        rw [closed_exact_defect]
        norm_num
      · change DefectRoutingAlignment.exactDefect rowFiveProfile
          harmonicRegistrationQuery halfCoordinateQuery stage active <= 1
        rw [closed_exact_defect]

def visibleRoutingComplete : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      DefectRoutingAlignment.RoutingCompleteAt rowFiveProfile
        (visibleContractQuery.read stage active) stage active :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun stage active _boundary => by
      constructor
      right
      right
      change closureProfile.IsTargetVisible
        (DefectRoutingAlignment.parentView rowFiveProfile stage active)
        (DefectRoutingAlignment.exactDefect rowFiveProfile
          harmonicRegistrationQuery identityCoordinateQuery stage active)
      rw [visible_exact_defect]
      exact twoVisible _

/-! ## Three strict row-6 executions over the same row-5 residual -/

abbrev positiveProfile :
    DefectRoutingAlignment.Profile rowFiveProfile PDEModel Real where
  ResistancePotential := Real
  tieredSpec :=
    PDERow6DefectRoutingRaw.tieredSpec rowFiveProfile .tierOne
  tieredCapability :=
    PDERow6DefectRoutingRaw.tieredCapability rowFiveProfile .tierOne
  contextSpec :=
    PDERow6DefectRoutingRaw.contextSpec rowFiveProfile .neutral
  contextCapability :=
    PDERow6DefectRoutingRaw.contextCapability rowFiveProfile .neutral
  defectRegistration := positiveRegistrationQuery
  boundaryCoordinate := halfCoordinateQuery
  resistanceContract := positiveContractQuery
  harmonicZeroDecidable := positiveZeroDecision
  harmonicLedgerDecidable := positiveLedgerDecision
  zeroClosed := zeroClosedQuery
  routingComplete := positiveRoutingComplete

abbrev closedProfile :
    DefectRoutingAlignment.Profile rowFiveProfile PDEModel Real where
  ResistancePotential := Unit
  tieredSpec :=
    PDERow6DefectRoutingRaw.tieredSpec rowFiveProfile .tierOne
  tieredCapability :=
    PDERow6DefectRoutingRaw.tieredCapability rowFiveProfile .tierOne
  contextSpec :=
    PDERow6DefectRoutingRaw.contextSpec rowFiveProfile .neutral
  contextCapability :=
    PDERow6DefectRoutingRaw.contextCapability rowFiveProfile .neutral
  defectRegistration := harmonicRegistrationQuery
  boundaryCoordinate := halfCoordinateQuery
  resistanceContract := closedContractQuery
  harmonicZeroDecidable := closedZeroDecision
  harmonicLedgerDecidable := closedLedgerDecision
  zeroClosed := zeroClosedQuery
  routingComplete := closedRoutingComplete

abbrev visibleProfile :
    DefectRoutingAlignment.Profile rowFiveProfile PDEModel Real where
  ResistancePotential := Unit
  tieredSpec :=
    PDERow6DefectRoutingRaw.tieredSpec rowFiveProfile .tierOne
  tieredCapability :=
    PDERow6DefectRoutingRaw.tieredCapability rowFiveProfile .tierOne
  contextSpec :=
    PDERow6DefectRoutingRaw.contextSpec rowFiveProfile .neutral
  contextCapability :=
    PDERow6DefectRoutingRaw.contextCapability rowFiveProfile .neutral
  defectRegistration := harmonicRegistrationQuery
  boundaryCoordinate := identityCoordinateQuery
  resistanceContract := visibleContractQuery
  harmonicZeroDecidable := visibleZeroDecision
  harmonicLedgerDecidable := visibleLedgerDecision
  zeroClosed := zeroClosedQuery
  routingComplete := visibleRoutingComplete

def positiveRun := positiveProfile.run rowFiveRun.value

def closedRun := closedProfile.run rowFiveRun.value

def visibleRun := visibleProfile.run rowFiveRun.value

def positiveSuccessorActive :
    positiveProfile.SuccessorFocus.Active positiveRun.value := by
  change rowFiveProfile.TargetVisibleFocus.Active positiveRun.value.previous
  have previousEq : positiveRun.value.previous = rowFiveRun.value :=
    DefectRoutingAlignment.Profile.run_previous positiveProfile rowFiveRun.value
  rw [previousEq]
  exact rowFiveActive

def closedSuccessorActive :
    closedProfile.SuccessorFocus.Active closedRun.value := by
  change rowFiveProfile.TargetVisibleFocus.Active closedRun.value.previous
  have previousEq : closedRun.value.previous = rowFiveRun.value :=
    DefectRoutingAlignment.Profile.run_previous closedProfile rowFiveRun.value
  rw [previousEq]
  exact rowFiveActive

def visibleSuccessorActive :
    visibleProfile.SuccessorFocus.Active visibleRun.value := by
  change rowFiveProfile.TargetVisibleFocus.Active visibleRun.value.previous
  have previousEq : visibleRun.value.previous = rowFiveRun.value :=
    DefectRoutingAlignment.Profile.run_previous visibleProfile rowFiveRun.value
  rw [previousEq]
  exact rowFiveActive

def positiveGenerated :=
  positiveProfile.outputQuery.read positiveRun.value positiveSuccessorActive

def closedGenerated :=
  closedProfile.outputQuery.read closedRun.value closedSuccessorActive

def visibleGenerated :=
  visibleProfile.outputQuery.read visibleRun.value visibleSuccessorActive

theorem positiveConditionAt
    (stage : DefectRoutingAlignment.RowFiveStage rowFiveProfile)
    (active : rowFiveProfile.TargetVisibleFocus.Active stage) :
    positiveProfile.Condition (Focus.ActiveView.of stage active)
      .finiteResistanceHarmonicZero := by
  change (positiveContractQuery.read stage active).Finite /\
    (positiveContractQuery.read stage active).harmonic = 0
  constructor
  · simp [DirectResistanceContract.Finite, positiveContract]
  · simp [DirectResistanceContract.harmonic, positiveContract]

theorem closedConditionAt
    (stage : DefectRoutingAlignment.RowFiveStage rowFiveProfile)
    (active : rowFiveProfile.TargetVisibleFocus.Active stage) :
    closedProfile.Condition (Focus.ActiveView.of stage active)
      .finiteResistanceHarmonicClosed := by
  change (closedContractQuery.read stage active).Finite /\
    (closedContractQuery.read stage active).harmonic ≠ 0 /\
      (closedContractQuery.read stage active).harmonic ∈
        (DefectRoutingAlignment.CurrentLedgerAt rowFiveProfile
          stage active).classes
  constructor
  · simp [DirectResistanceContract.Finite, harmonicContract]
  · constructor
    · have harmonicEq :
          (closedContractQuery.read stage active).harmonic =
            (1 : Real) := by
          change DefectRoutingAlignment.exactDefect rowFiveProfile
            harmonicRegistrationQuery halfCoordinateQuery
            stage active = 1
          exact closed_exact_defect stage active
      rw [harmonicEq]
      norm_num
    · have harmonicEq :
          (closedContractQuery.read stage active).harmonic =
            (1 : Real) := by
          change DefectRoutingAlignment.exactDefect rowFiveProfile
            harmonicRegistrationQuery halfCoordinateQuery
            stage active = 1
          exact closed_exact_defect stage active
      rw [harmonicEq]
      change (1 : Real) <= 1
      exact le_rfl

theorem visibleConditionAt
    (stage : DefectRoutingAlignment.RowFiveStage rowFiveProfile)
    (active : rowFiveProfile.TargetVisibleFocus.Active stage) :
    visibleProfile.Condition (Focus.ActiveView.of stage active)
      .targetVisibleHarmonic := by
  change closureProfile.IsTargetVisible
    (DefectRoutingAlignment.parentView rowFiveProfile
      stage active)
    (DefectRoutingAlignment.exactDefect rowFiveProfile
      harmonicRegistrationQuery identityCoordinateQuery
      stage active)
  rw [visible_exact_defect]
  exact twoVisible _

abbrev positiveOutputView : DefectRoutingAlignment.ActiveView rowFiveProfile :=
  Focus.ActiveView.of positiveRun.value.previous positiveSuccessorActive

abbrev closedOutputView : DefectRoutingAlignment.ActiveView rowFiveProfile :=
  Focus.ActiveView.of closedRun.value.previous closedSuccessorActive

abbrev visibleOutputView : DefectRoutingAlignment.ActiveView rowFiveProfile :=
  Focus.ActiveView.of visibleRun.value.previous visibleSuccessorActive

theorem positive_selected_tag :
    positiveGenerated.semanticTag? =
      some .finiteResistanceHarmonicZero :=
  positiveProfile.generated_semanticTag_of_condition positiveOutputView
    positiveGenerated .finiteResistanceHarmonicZero
    (positiveConditionAt positiveRun.value.previous positiveSuccessorActive)

theorem closed_selected_tag :
    closedGenerated.semanticTag? =
      some .finiteResistanceHarmonicClosed :=
  closedProfile.generated_semanticTag_of_condition closedOutputView
    closedGenerated .finiteResistanceHarmonicClosed
    (closedConditionAt closedRun.value.previous closedSuccessorActive)

theorem visible_selected_tag :
    visibleGenerated.semanticTag? = some .targetVisibleHarmonic :=
  visibleProfile.generated_semanticTag_of_condition visibleOutputView
    visibleGenerated .targetVisibleHarmonic
    (visibleConditionAt visibleRun.value.previous visibleSuccessorActive)

theorem positive_disposition :
    positiveGenerated.disposition = .capacityReady := by
  simpa [DefectRouting.SemanticTag.disposition] using
    positiveProfile.generated_disposition_of_condition
    positiveOutputView positiveGenerated .finiteResistanceHarmonicZero
    (positiveConditionAt positiveRun.value.previous positiveSuccessorActive)

theorem closed_disposition :
    closedGenerated.disposition = .capacityReady := by
  simpa [DefectRouting.SemanticTag.disposition] using
    closedProfile.generated_disposition_of_condition
    closedOutputView closedGenerated .finiteResistanceHarmonicClosed
    (closedConditionAt closedRun.value.previous closedSuccessorActive)

theorem visible_disposition :
    visibleGenerated.disposition = .targetVisibleHarmonic := by
  simpa [DefectRouting.SemanticTag.disposition] using
    visibleProfile.generated_disposition_of_condition
    visibleOutputView visibleGenerated .targetVisibleHarmonic
    (visibleConditionAt visibleRun.value.previous visibleSuccessorActive)

theorem exact_relation_prefixes :
    positiveGenerated.interpretation.checks = 1 /\
      closedGenerated.interpretation.checks = 2 /\
      visibleGenerated.interpretation.checks = 3 := by
  constructor
  · simpa using positiveProfile.generated_relation_checks_of_condition
      positiveOutputView positiveGenerated .finiteResistanceHarmonicZero
      (positiveConditionAt positiveRun.value.previous positiveSuccessorActive)
  · constructor
    · simpa using closedProfile.generated_relation_checks_of_condition
        closedOutputView closedGenerated .finiteResistanceHarmonicClosed
        (closedConditionAt closedRun.value.previous closedSuccessorActive)
    · simpa using visibleProfile.generated_relation_checks_of_condition
        visibleOutputView visibleGenerated .targetVisibleHarmonic
        (visibleConditionAt visibleRun.value.previous visibleSuccessorActive)

def positiveSemanticActive :
    (positiveProfile.SemanticTagFocus
      .finiteResistanceHarmonicZero).Active positiveRun.value where
  parent := positiveSuccessorActive
  accepted := positive_selected_tag

def closedSemanticActive :
    (closedProfile.SemanticTagFocus
      .finiteResistanceHarmonicClosed).Active closedRun.value where
  parent := closedSuccessorActive
  accepted := closed_selected_tag

def visibleSemanticActive :
    (visibleProfile.SemanticTagFocus
      .targetVisibleHarmonic).Active visibleRun.value where
  parent := visibleSuccessorActive
  accepted := visible_selected_tag

def positiveSemanticOutput :=
  (positiveProfile.semanticTagOutputQuery
    .finiteResistanceHarmonicZero).read positiveRun.value
      positiveSemanticActive

def closedSemanticOutput :=
  (closedProfile.semanticTagOutputQuery
    .finiteResistanceHarmonicClosed).read closedRun.value
      closedSemanticActive

def visibleSemanticOutput :=
  (visibleProfile.semanticTagOutputQuery
    .targetVisibleHarmonic).read visibleRun.value
      visibleSemanticActive

theorem semantic_queries_read_exact_outputs :
    positiveSemanticOutput.val = positiveGenerated /\
      closedSemanticOutput.val = closedGenerated /\
      visibleSemanticOutput.val = visibleGenerated :=
  ⟨rfl, rfl, rfl⟩

def visibleTargetEvidence :
    DefectRoutingAlignment.Profile.TargetVisibleEvidence
      visibleProfile visibleOutputView :=
  visibleProfile.targetVisibleEvidence visibleOutputView
    (visibleConditionAt visibleRun.value.previous visibleSuccessorActive)

theorem visible_harmonic_is_nonzero :
    visibleProfile.harmonicAt visibleOutputView ≠ 0 :=
  visibleTargetEvidence.nonzero

theorem visible_harmonic_is_not_routable :
    ¬ (Exists fun potential : visibleProfile.ResistancePotential =>
      (visibleProfile.resistanceAt visibleOutputView).action potential =
        visibleProfile.harmonicAt visibleOutputView) :=
  visibleTargetEvidence.notRoutable

theorem exact_run_work :
    positiveRun.checks = 8 /\
      closedRun.checks = 9 /\
      visibleRun.checks = 10 := by
  constructor
  · change (positiveProfile.run rowFiveRun.value).checks = 8
    rw [positiveProfile.run_checks_of_active_condition rowFiveRun.value
      rowFiveActive .finiteResistanceHarmonicZero
      (positiveConditionAt rowFiveRun.value rowFiveActive)]
    decide
  · constructor
    · change (closedProfile.run rowFiveRun.value).checks = 9
      rw [closedProfile.run_checks_of_active_condition rowFiveRun.value
        rowFiveActive .finiteResistanceHarmonicClosed
        (closedConditionAt rowFiveRun.value rowFiveActive)]
      decide
    · change (visibleProfile.run rowFiveRun.value).checks = 10
      rw [visibleProfile.run_checks_of_active_condition rowFiveRun.value
        rowFiveActive .targetVisibleHarmonic
        (visibleConditionAt rowFiveRun.value rowFiveActive)]
      decide

def positiveCapacityReadyActive :
    positiveProfile.CapacityReadyFocus.Active positiveRun.value where
  parent := positiveSuccessorActive
  accepted := positive_disposition

def closedCapacityReadyActive :
    closedProfile.CapacityReadyFocus.Active closedRun.value where
  parent := closedSuccessorActive
  accepted := closed_disposition

def visibleTargetHarmonicActive :
    visibleProfile.TargetVisibleHarmonicFocus.Active visibleRun.value where
  parent := visibleSuccessorActive
  accepted := visible_disposition

theorem positive_target_focus_rejected :
    Not (positiveProfile.TargetVisibleHarmonicFocus.Active positiveRun.value) := by
  intro selected
  have impossible :
      (DefectRouting.Disposition.capacityReady) =
        .targetVisibleHarmonic :=
    positive_disposition.symm.trans selected.accepted
  cases impossible

theorem closed_target_focus_rejected :
    Not (closedProfile.TargetVisibleHarmonicFocus.Active closedRun.value) := by
  intro selected
  have impossible :
      (DefectRouting.Disposition.capacityReady) =
        .targetVisibleHarmonic :=
    closed_disposition.symm.trans selected.accepted
  cases impossible

theorem visible_capacity_focus_rejected :
    Not (visibleProfile.CapacityReadyFocus.Active visibleRun.value) := by
  intro selected
  have impossible :
      (DefectRouting.Disposition.targetVisibleHarmonic) =
        .capacityReady :=
    visible_disposition.symm.trans selected.accepted
  cases impossible

def positiveCapacityOutput :=
  positiveProfile.capacityReadyOutputQuery.read positiveRun.value
    positiveCapacityReadyActive

def closedCapacityOutput :=
  closedProfile.capacityReadyOutputQuery.read closedRun.value
    closedCapacityReadyActive

def visibleTargetOutput :=
  visibleProfile.targetVisibleHarmonicOutputQuery.read visibleRun.value
    visibleTargetHarmonicActive

theorem refined_queries_read_exact_outputs :
    positiveCapacityOutput.val = positiveGenerated /\
      closedCapacityOutput.val = closedGenerated /\
      visibleTargetOutput.val = visibleGenerated := by
  exact ⟨rfl, rfl, rfl⟩

theorem runs_retain_literal_row_five :
    positiveRun.value.previous = rowFiveRun.value /\
      closedRun.value.previous = rowFiveRun.value /\
      visibleRun.value.previous = rowFiveRun.value := by
  exact ⟨positiveProfile.run_previous rowFiveRun.value,
    closedProfile.run_previous rowFiveRun.value,
    visibleProfile.run_previous rowFiveRun.value⟩

theorem runs_retain_root_residual :
    Residual.residualOf positiveRun.value = () /\
      Residual.residualOf closedRun.value = () /\
      Residual.residualOf visibleRun.value = () := by
  exact ⟨rfl, rfl, rfl⟩

def positiveDefectAtSuccessor :=
  positiveProfile.exactDefectQueryAtSuccessor.read positiveRun.value
    positiveSuccessorActive

def closedDefectAtSuccessor :=
  closedProfile.exactDefectQueryAtSuccessor.read closedRun.value
    closedSuccessorActive

def visibleDefectAtSuccessor :=
  visibleProfile.exactDefectQueryAtSuccessor.read visibleRun.value
    visibleSuccessorActive

theorem successor_defects_are_exact :
    positiveDefectAtSuccessor = (1 : Real) /\
      closedDefectAtSuccessor = (1 : Real) /\
      visibleDefectAtSuccessor = (2 : Real) := by
  constructor
  · exact positive_exact_defect _ _
  · constructor
    · exact closed_exact_defect _ _
    · exact visible_exact_defect _ _

def positiveLedgerAtSuccessor :=
  positiveProfile.currentLedgerQueryAtSuccessor.read positiveRun.value
    positiveSuccessorActive

def closedLedgerAtSuccessor :=
  closedProfile.currentLedgerQueryAtSuccessor.read closedRun.value
    closedSuccessorActive

def visibleLedgerAtSuccessor :=
  visibleProfile.currentLedgerQueryAtSuccessor.read visibleRun.value
    visibleSuccessorActive

theorem successor_ledgers_are_unchanged :
    positiveLedgerAtSuccessor = realLedger /\
      closedLedgerAtSuccessor = realLedger /\
      visibleLedgerAtSuccessor = realLedger := by
  exact ⟨rfl, rfl, rfl⟩

def positiveQuotientAtSuccessor :=
  positiveProfile.currentQuotientQueryAtSuccessor.read positiveRun.value
    positiveSuccessorActive

def closedQuotientAtSuccessor :=
  closedProfile.currentQuotientQueryAtSuccessor.read closedRun.value
    closedSuccessorActive

def visibleQuotientAtSuccessor :=
  visibleProfile.currentQuotientQueryAtSuccessor.read visibleRun.value
    visibleSuccessorActive

theorem successor_quotients_are_unchanged :
    positiveQuotientAtSuccessor = realQuotient /\
      closedQuotientAtSuccessor = realQuotient /\
      visibleQuotientAtSuccessor = realQuotient := by
  exact ⟨rfl, rfl, rfl⟩

theorem successor_resistance_reads_are_preserved :
    positiveProfile.resistanceContractQueryAtSuccessor.read positiveRun.value
        positiveSuccessorActive =
      positiveContractQuery.read positiveRun.value.previous
        positiveSuccessorActive /\
    closedProfile.resistanceContractQueryAtSuccessor.read closedRun.value
        closedSuccessorActive =
      closedContractQuery.read closedRun.value.previous
        closedSuccessorActive /\
    visibleProfile.resistanceContractQueryAtSuccessor.read visibleRun.value
        visibleSuccessorActive =
      visibleContractQuery.read visibleRun.value.previous
        visibleSuccessorActive := by
  exact ⟨rfl, rfl, rfl⟩

theorem every_run_is_bounded :
    positiveRun.checks <=
      (rowFiveProfile.TargetVisibleFocus.selectionBudget.add
        (DefectRouting.payloadBudget positiveProfile.toRaw)).coefficient *
      ((rowFiveProfile.TargetVisibleFocus.selectionBudget.add
        (DefectRouting.payloadBudget positiveProfile.toRaw)).size
          rowFiveRun.value + 1) ^
      (rowFiveProfile.TargetVisibleFocus.selectionBudget.add
        (DefectRouting.payloadBudget positiveProfile.toRaw)).degree /\
    closedRun.checks <=
      (rowFiveProfile.TargetVisibleFocus.selectionBudget.add
        (DefectRouting.payloadBudget closedProfile.toRaw)).coefficient *
      ((rowFiveProfile.TargetVisibleFocus.selectionBudget.add
        (DefectRouting.payloadBudget closedProfile.toRaw)).size
          rowFiveRun.value + 1) ^
      (rowFiveProfile.TargetVisibleFocus.selectionBudget.add
        (DefectRouting.payloadBudget closedProfile.toRaw)).degree /\
    visibleRun.checks <=
      (rowFiveProfile.TargetVisibleFocus.selectionBudget.add
        (DefectRouting.payloadBudget visibleProfile.toRaw)).coefficient *
      ((rowFiveProfile.TargetVisibleFocus.selectionBudget.add
        (DefectRouting.payloadBudget visibleProfile.toRaw)).size
          rowFiveRun.value + 1) ^
      (rowFiveProfile.TargetVisibleFocus.selectionBudget.add
        (DefectRouting.payloadBudget visibleProfile.toRaw)).degree := by
  exact ⟨positiveProfile.run_checks_bounded rowFiveRun.value,
    closedProfile.run_checks_bounded rowFiveRun.value,
    visibleProfile.run_checks_bounded rowFiveRun.value⟩

end

end Hypostructure.Fixtures.PDERow6FiniteOrthogonalAlignment

#print axioms Hypostructure.Fixtures.PDERow6FiniteOrthogonalAlignment.exact_run_work
#print axioms Hypostructure.Fixtures.PDERow6FiniteOrthogonalAlignment.visible_harmonic_is_not_routable
#print axioms Hypostructure.Fixtures.PDERow6FiniteOrthogonalAlignment.successor_quotients_are_unchanged
