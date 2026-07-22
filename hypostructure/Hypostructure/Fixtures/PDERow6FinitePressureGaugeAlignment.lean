import Hypostructure.Fixtures.PDERow6DefectRoutingRaw
import Hypostructure.Fixtures.PDERows1To4
import Hypostructure.PDE.FastTrack.DefectRoutingAlignment

/-!
# Finite pressure-gauge alignment for PDE row 6

This fixture models pressure on two spatial samples.  Adding the same scalar
to both samples is a gauge transformation, and the represented quotient is
the pressure oscillation.  Row 5 closes exactly the constant-pressure gauge
classes and selects one nonconstant boundary class.  Row 4 then computes,
from one registered generator form and two quotient generators, either a
constant gauge defect or a non-gauge defect.

Three strict row-6 profiles read those exact predecessor-owned objects:

* the non-gauge defect with trivial harmonic projection is routable;
* the constant defect is a nonzero harmonic class already in the gauge ledger;
* the non-gauge defect with identity harmonic projection remains target-visible.

The fixture supplies no semantic tag, route, row-6 output, or successor.  The
strict alignment executor derives the predicates, scans the fixed semantic
schedule, and installs the focused successor through Core.
-/

namespace Hypostructure.Fixtures.PDERow6FinitePressureGaugeAlignment

open Hypostructure
open Hypostructure.Core
open Hypostructure.Core.NormalForm
open Hypostructure.Core.Residual
open Hypostructure.PDE
open Hypostructure.PDE.FastTrack

noncomputable section

/-! ## A two-point pressure space and its gauge quotient -/

abbrev Pressure := EuclideanSpace Real (Fin 2)

/-- A pressure with prescribed values at the two finite sample points. -/
def pressurePair (first second : Real) : Pressure :=
  EuclideanSpace.single 0 first + EuclideanSpace.single 1 second

@[simp] theorem pressurePair_zero (first second : Real) :
    pressurePair first second 0 = first := by
  simp [pressurePair]

@[simp] theorem pressurePair_one (first second : Real) :
    pressurePair first second 1 = second := by
  simp [pressurePair]

/-- The observable pressure difference, invariant under constant shifts. -/
def oscillation : Pressure →ₗ[Real] Real where
  toFun := fun pressure => pressure 1 - pressure 0
  map_add' := by
    intro left right
    dsimp
    ring
  map_smul' := by
    intro scalar pressure
    dsimp
    ring

/-- Canonical gauge-fixed representative with first component zero. -/
def gaugeLift : Real →ₗ[Real] Pressure where
  toFun := fun value => pressurePair 0 value
  map_add' := by
    intro left right
    ext index
    fin_cases index <;> simp [pressurePair]
  map_smul' := by
    intro scalar value
    ext index
    fin_cases index <;> simp [pressurePair]

/-- Finite pressure-gauge equivalence by a common additive shift. -/
def GaugeEquivalent (left right : Pressure) : Prop :=
  exists gauge : Real,
    right = left + pressurePair gauge gauge

theorem gaugeEquivalent_iff_oscillation_eq {left right : Pressure} :
    GaugeEquivalent left right ↔ oscillation left = oscillation right := by
  constructor
  · rintro ⟨gauge, rfl⟩
    simp [oscillation]
  · intro equal
    refine ⟨right 0 - left 0, ?_⟩
    ext index
    fin_cases index
    · simp [pressurePair]
    · have coordinate :
          right 1 = left 1 + (right 0 - left 0) := by
        change left 1 - left 0 = right 1 - right 0 at equal
        linarith
      simpa [pressurePair] using coordinate

theorem oscillation_gauge_shift (pressure : Pressure) (gauge : Real) :
    oscillation (pressure + pressurePair gauge gauge) =
      oscillation pressure := by
  simp [oscillation]

@[simp] theorem oscillation_gaugeLift (value : Real) :
    oscillation (gaugeLift value) = value := by
  simp [oscillation, gaugeLift]

/-- A finite generator whose quotient defect separates a constant gauge part
from a genuinely oscillatory part. -/
def pressureGenerator : Pressure →ₗ[Real] Pressure where
  toFun := fun pressure => pressurePair (pressure 1) (2 * pressure 1)
  map_add' := by
    intro left right
    ext index
    fin_cases index <;> simp [pressurePair, mul_add]
  map_smul' := by
    intro scalar pressure
    ext index
    fin_cases index <;>
      simp [pressurePair, mul_left_comm]

def zeroForm : BilinearForm Pressure := 0

def pressureEquationState (pressure : Pressure) :
    EquationState PDERows1To4.FiniteScalar.equation () where
  object := oscillation pressure
  data := ()
  valid := trivial

def pressureStatePresentation :
    RepresentedStatePresentation PDERows1To4.FiniteScalar.model Pressure where
  window := ()
  realize := pressureEquationState

def discreteTopology : FormTopology Pressure where
  converges := fun sequence limit => sequence 0 = limit
  scalarCauchy := fun _sequence => True
  scalarConverges := fun sequence limit => sequence 0 = limit

def zeroClosedLaw : ClosedFormLaw Pressure (⊤ : Submodule Real Pressure)
    zeroForm discreteTopology where
  closed := by
    intro sequence limit inDomain converges cauchy
    refine ⟨Submodule.mem_top, ?_⟩
    rfl

/-- Registered finite represented form.  The zero pairing keeps this fixture
algebraic; the nontrivial content exercised below is the computed quotient
defect and its pressure-gauge interpretation. -/
def pressureGeneratorForm :
    GeneratorForm PDERows1To4.FiniteScalar.model Pressure where
  statePresentation := pressureStatePresentation
  domain := ⊤
  generator := pressureGenerator
  pairing := zeroForm
  form := zeroForm
  symmetricPart := zeroForm
  skewPart := zeroForm
  boundaryPart := zeroForm
  topology := discreteTopology
  closure := .closed zeroClosedLaw
  generator_representation := by simp [zeroForm]
  decomposition := by simp [zeroForm]
  symmetric := by simp [zeroForm]
  skew := by simp [zeroForm]
  symmetric_nonnegative := by simp [zeroForm]
  sectorConstant := 0
  sectorConstant_nonnegative := le_rfl
  sector := by simp [zeroForm]

abbrev PressureFormStage :=
  Core.Residual.Ledger.Extension PDERows1To4.FiniteScalar.SignatureStage
    (fun _previous =>
      GeneratorForm PDERows1To4.FiniteScalar.model Pressure)

def pressureFormStage : PressureFormStage :=
  pressureGeneratorForm.register PDERows1To4.FiniteScalar.signatureStage

def pressureFormQuery : Residual.Query PressureFormStage
    (fun _previous =>
      GeneratorForm PDERows1To4.FiniteScalar.model Pressure) :=
  Residual.Query.latest

def representedGaugeQuotient
    (form : GeneratorForm PDERows1To4.FiniteScalar.model Pressure) :
    RepresentedQuotient form Real where
  project := oscillation
  lift := gaugeLift
  project_lift := by
    apply LinearMap.ext
    intro value
    exact oscillation_gaugeLift value

def matchingQuotientGenerator
    (form : GeneratorForm PDERows1To4.FiniteScalar.model Pressure) :
    QuotientGenerator form (representedGaugeQuotient form) where
  generator := LinearMap.id

def zeroQuotientGenerator
    (form : GeneratorForm PDERows1To4.FiniteScalar.model Pressure) :
    QuotientGenerator form (representedGaugeQuotient form) where
  generator := 0

def gaugeQuotientAt (previous : PressureFormStage) :
    RepresentedQuotient (pressureFormQuery.read previous) Real :=
  representedGaugeQuotient (pressureFormQuery.read previous)

def matchingGeneratorAt (previous : PressureFormStage) :
    QuotientGenerator (pressureFormQuery.read previous)
      (gaugeQuotientAt previous) :=
  matchingQuotientGenerator (pressureFormQuery.read previous)

def zeroGeneratorAt (previous : PressureFormStage) :
    QuotientGenerator (pressureFormQuery.read previous)
      (gaugeQuotientAt previous) :=
  zeroQuotientGenerator (pressureFormQuery.read previous)

noncomputable def positiveGeometry : DefectGeometry Pressure where
  carrier := ⊤
  presentation := .boundedOperator {
    operator := ContinuousLinearMap.id Real Pressure
    operator_positive := ContinuousLinearMap.isPositive_id
    carrier_invariant := by simp
  }

noncomputable def harmonicGeometry : DefectGeometry Pressure where
  carrier := ⊤
  presentation := .boundedOperator {
    operator := 0
    operator_positive := ContinuousLinearMap.isPositive_zero
    carrier_invariant := by simp
  }

noncomputable def routableDefectStage :=
  registerDefect pressureFormQuery gaugeQuotientAt zeroGeneratorAt
    (fun _previous => positiveGeometry) pressureFormStage

noncomputable def closedGaugeDefectStage :=
  registerDefect pressureFormQuery gaugeQuotientAt matchingGeneratorAt
    (fun _previous => harmonicGeometry) pressureFormStage

noncomputable def visibleGaugeDefectStage :=
  registerDefect pressureFormQuery gaugeQuotientAt zeroGeneratorAt
    (fun _previous => harmonicGeometry) pressureFormStage

abbrev PDEModel := PDERows1To4.FiniteScalar.model

abbrev routableRegistration :
    QuotientDefectRegistration PDEModel Pressure Real :=
  routableDefectStage.added

abbrev closedGaugeRegistration :
    QuotientDefectRegistration PDEModel Pressure Real :=
  closedGaugeDefectStage.added

abbrev visibleGaugeRegistration :
    QuotientDefectRegistration PDEModel Pressure Real :=
  visibleGaugeDefectStage.added

theorem pressure_form_retains_signature :
    pressureFormStage.previous = PDERows1To4.FiniteScalar.signatureStage := rfl

theorem routable_registration_retains_form :
    routableDefectStage.previous = pressureFormStage := rfl

theorem closed_registration_retains_form :
    closedGaugeDefectStage.previous = pressureFormStage := rfl

theorem zero_generator_defect_apply (value : Real) :
    routableRegistration.defect value = pressurePair value (2 * value) := by
  change intertwiningDefect pressureGeneratorForm
    (representedGaugeQuotient pressureGeneratorForm)
    (zeroQuotientGenerator pressureGeneratorForm) value =
      pressurePair value (2 * value)
  ext index
  fin_cases index <;> simp [intertwiningDefect, pressureGeneratorForm,
    pressureGenerator, representedGaugeQuotient, zeroQuotientGenerator,
    gaugeLift]

theorem matching_generator_defect_apply (value : Real) :
    closedGaugeRegistration.defect value = pressurePair value value := by
  change intertwiningDefect pressureGeneratorForm
    (representedGaugeQuotient pressureGeneratorForm)
    (matchingQuotientGenerator pressureGeneratorForm) value =
      pressurePair value value
  ext index
  fin_cases index
  · simp [intertwiningDefect, pressureGeneratorForm, pressureGenerator,
      representedGaugeQuotient, matchingQuotientGenerator, gaugeLift]
  · simp [intertwiningDefect, pressureGeneratorForm, pressureGenerator,
      representedGaugeQuotient, matchingQuotientGenerator, gaugeLift]
    ring

theorem visible_generator_defect_apply (value : Real) :
    visibleGaugeRegistration.defect value = pressurePair value (2 * value) := by
  exact zero_generator_defect_apply value

theorem matching_defect_is_pure_gauge (value : Real) :
    GaugeEquivalent 0 (closedGaugeRegistration.defect value) := by
  rw [gaugeEquivalent_iff_oscillation_eq,
    matching_generator_defect_apply]
  simp [oscillation]

theorem zero_generator_defect_is_visible {value : Real} (nonzero : value ≠ 0) :
    oscillation (visibleGaugeRegistration.defect value) ≠ 0 := by
  rw [visible_generator_defect_apply]
  have difference : 2 * value - value ≠ 0 := by
    intro equal
    apply nonzero
    linarith
  simpa [oscillation] using difference

/-! ## A target-complete finite row-5 gauge ledger -/

abbrev Previous := PDERow5DirectedExhaustiveness.Previous
abbrev ParentFocus := PDERow5DirectedExhaustiveness.focus
abbrev View := DirectedExhaustiveness.ActiveView ParentFocus
abbrev currentView : View :=
  Focus.ActiveView.of PDERow5DirectedExhaustiveness.previous
    PDERow5DirectedExhaustiveness.active

def IsGauge (pressure : Pressure) : Prop :=
  pressure 0 = pressure 1

def boundaryPressure : Pressure := pressurePair 0 1

theorem boundaryPressure_not_gauge : Not (IsGauge boundaryPressure) := by
  norm_num [IsGauge, boundaryPressure]

def boundarySchedule : Core.Finite.Enumeration Pressure :=
  Core.Finite.Enumeration.singleton boundaryPressure

def boundaryScheduleQuery : Residual.Query View fun _view =>
    Core.Finite.Enumeration Pressure :=
  PDERow5DirectedExhaustiveness.viewQuery.map fun _view _root =>
    boundarySchedule

def gaugeClosure : Core.ClosureOperator Pressure :=
  Core.ClosureOperator.identity Pressure

def gaugeLedger : Core.ClosedClassLedger gaugeClosure IsGauge where
  classes := {pressure | IsGauge pressure}
  closed := rfl
  targetNull := fun member => member

noncomputable def gaugeClassProject (pressure : Pressure) : Bool := by
  classical
  exact if IsGauge pressure then false else true

@[simp] theorem gaugeClassProject_zero :
    gaugeClassProject (0 : Pressure) = false := by
  simp [gaugeClassProject, IsGauge]

@[simp] theorem gaugeClassProject_boundary :
    gaugeClassProject boundaryPressure = true := by
  simp [gaugeClassProject, boundaryPressure_not_gauge]

noncomputable def gaugeQuotientUniversal :
    Core.QuotientUniversalProperty gaugeClassProject where
  descend := fun map _compatible quotientClass =>
    if quotientClass then map boundaryPressure else map 0
  descend_project := by
    intro Result map compatible pressure
    by_cases gauge : IsGauge pressure
    · have same :
          gaugeClassProject (0 : Pressure) = gaugeClassProject pressure := by
        have zeroGauge : IsGauge (0 : Pressure) := by simp [IsGauge]
        simp [gaugeClassProject, gauge, zeroGauge]
      simpa [gaugeClassProject, gauge] using compatible same
    · have same :
          gaugeClassProject boundaryPressure = gaugeClassProject pressure := by
        simp [gaugeClassProject, gauge, boundaryPressure_not_gauge]
      simpa [gaugeClassProject, gauge] using compatible same
  descend_unique := by
    intro Result map compatible candidate commutes quotientClass
    cases quotientClass
    · simpa using commutes 0
    · simpa using commutes boundaryPressure

noncomputable def gaugeLedgerQuotient : Core.LedgerQuotient gaugeLedger where
  Quotient := Bool
  project := gaugeClassProject
  null := false
  killsClosed := by
    intro pressure closed
    change IsGauge pressure at closed
    simp [gaugeClassProject, closed]
  universal := gaugeQuotientUniversal

def gaugeLedgerQuery : Residual.Query View fun _view =>
    Core.ClosedClassLedger gaugeClosure IsGauge :=
  PDERow5DirectedExhaustiveness.viewQuery.map fun _view _root => gaugeLedger

abbrev closureProfile : ClassClosure.Profile View where
  Carrier := Pressure
  closure := gaugeClosure
  TargetNull := IsGauge
  family := boundaryScheduleQuery
  ledger := gaugeLedgerQuery
  quotient := fun _view => gaugeLedgerQuotient
  TargetVisible := fun _view quotientClass => quotientClass = true
  targetVisibleDecidable := fun _view quotientClass =>
    Bool.decEq quotientClass true
  visibleNonzero := by
    intro current carrier visible equalNull
    change gaugeClassProject carrier = true at visible
    change gaugeClassProject carrier = false at equalNull
    simp_all
  nullOfNotVisible := by
    intro current carrier invisible
    change Not (gaugeClassProject carrier = true) at invisible
    change gaugeClassProject carrier = false
    cases projected : gaugeClassProject carrier <;> simp_all
  targetNullOfNull := by
    intro current carrier equalNull
    change gaugeClassProject carrier = false at equalNull
    by_contra notGauge
    simp [gaugeClassProject, notGauge] at equalNull
  closureStable := Core.ClosureStable.identity

def targetComplete : ClassClosure.TargetComplete closureProfile where
  representsNonzero := by
    intro current quotientClass nonzero
    cases quotientClass with
    | false => exact (nonzero rfl).elim
    | true =>
        refine ⟨boundaryPressure, ?_, ?_, rfl⟩
        · change boundaryPressure ∈ [boundaryPressure]
          simp
        · exact gaugeClassProject_boundary

@[simp] theorem familyAt_eq (current : View) :
    closureProfile.familyAt current = boundarySchedule :=
  rfl

theorem boundaryVisible (current : View) :
    closureProfile.IsTargetVisible current boundaryPressure := by
  change gaugeClassProject boundaryPressure = true
  exact gaugeClassProject_boundary

theorem noAvoids (current : View)
    (avoids : closureProfile.AvoidsTargetVisible current) : False := by
  let index : Fin (closureProfile.familyAt current).card :=
    ⟨0, by
      rw [familyAt_eq]
      change 0 < [boundaryPressure].length
      decide⟩
  have invisible := avoids index
  have selected :
      (closureProfile.familyAt current).get index = boundaryPressure := by
    simp [familyAt_eq, boundarySchedule, Core.Finite.Enumeration.get,
      Core.Finite.Enumeration.singleton,
      Core.Finite.Enumeration.ofNodupList]
  apply invisible
  rw [selected]
  exact boundaryVisible current

theorem hasVisible (current : View) :
    closureProfile.HasTargetVisible current := by
  rcases (closureProfile.scan current).hit_or_avoids with hit | avoids
  · exact hit
  · exact (noAvoids current avoids).elim

def closureRegistration :
    ClassClosure.ExtensionRegistration closureProfile where
  nextQuotient := fun current avoids => (noAvoids current avoids).elim
  quotientTransport := fun current avoids => (noAvoids current avoids).elim
  quotientTransport_project := by
    intro current avoids
    exact (noAvoids current avoids).elim
  quotientTransport_null := by
    intro current avoids
    exact (noAvoids current avoids).elim

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
  | targetVisible => simp
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
    DirectedExhaustiveness.generateActive rowFiveProfile currentView at outputEq
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
        have impossible := isClosure.symm.trans (closure_terminal currentView)
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

theorem rowFive_selected_pressure :
    rowFiveBoundary.closure.residual.hit.value = boundaryPressure := by
  have member := rowFiveBoundary.closure.residual.hit.member
  have member' :
      rowFiveBoundary.closure.residual.hit.value ∈ boundarySchedule.values := by
    simpa [rowFiveProfile, familyAt_eq] using member
  change rowFiveBoundary.closure.residual.hit.value ∈ [boundaryPressure] at member'
  simpa using member'

/-! ## Exact row-4 registrations queried on the row-5 residual -/

abbrev routableRegistrationQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun _stage _active =>
      QuotientDefectRegistration PDEModel Pressure Real :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun _stage _active _boundary => routableRegistration

abbrev closedGaugeRegistrationQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun _stage _active =>
      QuotientDefectRegistration PDEModel Pressure Real :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun _stage _active _boundary => closedGaugeRegistration

abbrev visibleGaugeRegistrationQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun _stage _active =>
      QuotientDefectRegistration PDEModel Pressure Real :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun _stage _active _boundary => visibleGaugeRegistration

abbrev boundaryCoordinateQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun _stage _active =>
      Pressure →ₗ[Real] Real :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun _stage _active _boundary => oscillation

theorem selectedCarrier_eq_boundary
    (stage : DefectRouting.RowFiveStage rowFiveProfile)
    (active : rowFiveProfile.TargetVisibleFocus.Active stage) :
    DefectRoutingAlignment.selectedCarrier rowFiveProfile stage active =
      boundaryPressure := by
  have member :=
    (rowFiveProfile.targetVisibleBoundaryQuery.read stage active).closure.residual.hit.member
  have member' :
      (rowFiveProfile.targetVisibleBoundaryQuery.read stage active).closure.residual.hit.value ∈
        boundarySchedule.values := by
    simpa [rowFiveProfile, familyAt_eq] using member
  change
    (rowFiveProfile.targetVisibleBoundaryQuery.read stage active).closure.residual.hit.value ∈
      [boundaryPressure] at member'
  simpa [DefectRoutingAlignment.selectedCarrier] using member'

theorem routable_exact_defect
    (stage : DefectRouting.RowFiveStage rowFiveProfile)
    (active : rowFiveProfile.TargetVisibleFocus.Active stage) :
    DefectRoutingAlignment.exactDefect rowFiveProfile
      routableRegistrationQuery boundaryCoordinateQuery stage active =
        pressurePair 1 2 := by
  change routableRegistration.defect
    (oscillation
      (DefectRoutingAlignment.selectedCarrier rowFiveProfile stage active)) =
        pressurePair 1 2
  rw [selectedCarrier_eq_boundary]
  simp [boundaryPressure, oscillation, zero_generator_defect_apply]

theorem closed_exact_defect
    (stage : DefectRouting.RowFiveStage rowFiveProfile)
    (active : rowFiveProfile.TargetVisibleFocus.Active stage) :
    DefectRoutingAlignment.exactDefect rowFiveProfile
      closedGaugeRegistrationQuery boundaryCoordinateQuery stage active =
        pressurePair 1 1 := by
  change closedGaugeRegistration.defect
    (oscillation
      (DefectRoutingAlignment.selectedCarrier rowFiveProfile stage active)) =
        pressurePair 1 1
  rw [selectedCarrier_eq_boundary]
  simp [boundaryPressure, oscillation, matching_generator_defect_apply]

theorem visible_exact_defect
    (stage : DefectRouting.RowFiveStage rowFiveProfile)
    (active : rowFiveProfile.TargetVisibleFocus.Active stage) :
    DefectRoutingAlignment.exactDefect rowFiveProfile
      visibleGaugeRegistrationQuery boundaryCoordinateQuery stage active =
        pressurePair 1 2 := by
  change visibleGaugeRegistration.defect
    (oscillation
      (DefectRoutingAlignment.selectedCarrier rowFiveProfile stage active)) =
        pressurePair 1 2
  rw [selectedCarrier_eq_boundary]
  simp [boundaryPressure, oscillation, visible_generator_defect_apply]

theorem positive_harmonic_iff (state : Pressure) :
    routableRegistration.geometry.IsHarmonic state ↔ state = 0 := by
  change (ContinuousLinearMap.id Real Pressure) state = 0 ↔ state = 0
  simp

theorem harmonic_is_harmonic (state : Pressure) :
    closedGaugeRegistration.geometry.IsHarmonic state := by
  change (0 : Pressure →L[Real] Pressure) state = 0
  simp

/-! ## Direct resistance contracts on the exact computed defects -/

noncomputable def routableContract (defect : Pressure) :
    DirectResistanceContract Pressure positiveGeometry defect Pressure where
  harmonicProjection := 0
  projection_idempotent := by simp
  projection_symmetric := by simp
  harmonic_is_harmonic := (positive_harmonic_iff 0).mpr rfl
  fixes_harmonic := by
    intro state harmonic
    have equal := (positive_harmonic_iff state).mp harmonic
    subst state
    rfl
  routableResistance := ENNReal.ofReal (‖defect‖ ^ 2)
  finiteDecidable := isTrue (by simp)
  action := id
  energy := fun potential => ‖potential‖ ^ 2
  energy_nonnegative := fun potential => sq_nonneg ‖potential‖
  finite_of_compensator := by simp
  compensator := fun _finite => defect
  compensates := by simp
  compensation_energy := by
    intro finite
    simp
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
    simpa [ENNReal.toReal_ofReal, sq_nonneg, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg defect), abs_of_nonneg (norm_nonneg state)]
      using abs_real_inner_le_norm defect state

noncomputable def harmonicContract (defect : Pressure) :
    DirectResistanceContract Pressure harmonicGeometry defect Unit where
  harmonicProjection := ContinuousLinearMap.id Real Pressure
  projection_idempotent := by simp
  projection_symmetric := by simp
  harmonic_is_harmonic := harmonic_is_harmonic defect
  fixes_harmonic := by simp
  routableResistance := 0
  finiteDecidable := isTrue (by norm_num)
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

abbrev routableContractQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      DirectResistanceContract Pressure
        (routableRegistrationQuery.read stage active).geometry
        (DefectRoutingAlignment.exactDefect rowFiveProfile
          routableRegistrationQuery boundaryCoordinateQuery stage active)
        Pressure :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun stage active _boundary =>
      routableContract (DefectRoutingAlignment.exactDefect rowFiveProfile
        routableRegistrationQuery boundaryCoordinateQuery stage active)

abbrev closedContractQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      DirectResistanceContract Pressure
        (closedGaugeRegistrationQuery.read stage active).geometry
        (DefectRoutingAlignment.exactDefect rowFiveProfile
          closedGaugeRegistrationQuery boundaryCoordinateQuery stage active)
        Unit :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun stage active _boundary =>
      harmonicContract (DefectRoutingAlignment.exactDefect rowFiveProfile
        closedGaugeRegistrationQuery boundaryCoordinateQuery stage active)

abbrev visibleContractQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      DirectResistanceContract Pressure
        (visibleGaugeRegistrationQuery.read stage active).geometry
        (DefectRoutingAlignment.exactDefect rowFiveProfile
          visibleGaugeRegistrationQuery boundaryCoordinateQuery stage active)
        Unit :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun stage active _boundary =>
      harmonicContract (DefectRoutingAlignment.exactDefect rowFiveProfile
        visibleGaugeRegistrationQuery boundaryCoordinateQuery stage active)

def zeroClosedQuery : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      (0 : Pressure) ∈
        (DefectRoutingAlignment.CurrentLedgerAt rowFiveProfile stage active).classes :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun _stage _active _boundary => by
      change IsGauge (0 : Pressure)
      simp [IsGauge]

noncomputable def routableZeroDecision : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      Decidable ((routableContractQuery.read stage active).harmonic = 0) :=
  rowFiveProfile.targetVisibleBoundaryQuery.map fun stage active _boundary =>
    Classical.propDecidable
      ((routableContractQuery.read stage active).harmonic = 0)

noncomputable def routableLedgerDecision : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      Decidable ((routableContractQuery.read stage active).harmonic ∈
        (DefectRoutingAlignment.CurrentLedgerAt rowFiveProfile stage active).classes) :=
  rowFiveProfile.targetVisibleBoundaryQuery.map fun stage active _boundary =>
    Classical.propDecidable
      ((routableContractQuery.read stage active).harmonic ∈
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

def routableRoutingComplete : Focus.ActiveQuery
    rowFiveProfile.TargetVisibleFocus fun stage active =>
      DefectRoutingAlignment.RoutingCompleteAt rowFiveProfile
        (routableContractQuery.read stage active) stage active :=
  rowFiveProfile.targetVisibleBoundaryQuery.map
    fun stage active _boundary => by
      constructor
      left
      constructor
      · simp [DirectResistanceContract.Finite, routableContract]
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
          closedGaugeRegistrationQuery boundaryCoordinateQuery stage active ≠ 0
        rw [closed_exact_defect]
        intro equal
        have first := congrArg (fun pressure : Pressure => pressure 0) equal
        norm_num at first
      · change IsGauge (DefectRoutingAlignment.exactDefect rowFiveProfile
          closedGaugeRegistrationQuery boundaryCoordinateQuery stage active)
        rw [closed_exact_defect]
        simp [IsGauge]

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
          visibleGaugeRegistrationQuery boundaryCoordinateQuery stage active)
      rw [visible_exact_defect]
      change gaugeClassProject (pressurePair 1 2) = true
      have notGauge : Not (IsGauge (pressurePair 1 2)) := by
        norm_num [IsGauge]
      simp [gaugeClassProject, notGauge]

/-! ## Strict framework profiles -/

abbrev routableProfile :
    DefectRoutingAlignment.Profile rowFiveProfile PDEModel Real where
  ResistancePotential := Pressure
  tieredSpec := PDERow6DefectRoutingRaw.tieredSpec rowFiveProfile .tierOne
  tieredCapability :=
    PDERow6DefectRoutingRaw.tieredCapability rowFiveProfile .tierOne
  contextSpec := PDERow6DefectRoutingRaw.contextSpec rowFiveProfile .neutral
  contextCapability :=
    PDERow6DefectRoutingRaw.contextCapability rowFiveProfile .neutral
  defectRegistration := routableRegistrationQuery
  boundaryCoordinate := boundaryCoordinateQuery
  resistanceContract := routableContractQuery
  harmonicZeroDecidable := routableZeroDecision
  harmonicLedgerDecidable := routableLedgerDecision
  zeroClosed := zeroClosedQuery
  routingComplete := routableRoutingComplete

abbrev closedProfile :
    DefectRoutingAlignment.Profile rowFiveProfile PDEModel Real where
  ResistancePotential := Unit
  tieredSpec := PDERow6DefectRoutingRaw.tieredSpec rowFiveProfile .tierOne
  tieredCapability :=
    PDERow6DefectRoutingRaw.tieredCapability rowFiveProfile .tierOne
  contextSpec := PDERow6DefectRoutingRaw.contextSpec rowFiveProfile .neutral
  contextCapability :=
    PDERow6DefectRoutingRaw.contextCapability rowFiveProfile .neutral
  defectRegistration := closedGaugeRegistrationQuery
  boundaryCoordinate := boundaryCoordinateQuery
  resistanceContract := closedContractQuery
  harmonicZeroDecidable := closedZeroDecision
  harmonicLedgerDecidable := closedLedgerDecision
  zeroClosed := zeroClosedQuery
  routingComplete := closedRoutingComplete

abbrev visibleProfile :
    DefectRoutingAlignment.Profile rowFiveProfile PDEModel Real where
  ResistancePotential := Unit
  tieredSpec := PDERow6DefectRoutingRaw.tieredSpec rowFiveProfile .tierOne
  tieredCapability :=
    PDERow6DefectRoutingRaw.tieredCapability rowFiveProfile .tierOne
  contextSpec := PDERow6DefectRoutingRaw.contextSpec rowFiveProfile .neutral
  contextCapability :=
    PDERow6DefectRoutingRaw.contextCapability rowFiveProfile .neutral
  defectRegistration := visibleGaugeRegistrationQuery
  boundaryCoordinate := boundaryCoordinateQuery
  resistanceContract := visibleContractQuery
  harmonicZeroDecidable := visibleZeroDecision
  harmonicLedgerDecidable := visibleLedgerDecision
  zeroClosed := zeroClosedQuery
  routingComplete := visibleRoutingComplete

/-! ## Framework-owned executions and semantic branches -/

def routableRun := routableProfile.run rowFiveRun.value

def closedRun := closedProfile.run rowFiveRun.value

def visibleRun := visibleProfile.run rowFiveRun.value

def routableSuccessorActive :
    routableProfile.SuccessorFocus.Active routableRun.value := by
  change rowFiveProfile.TargetVisibleFocus.Active routableRun.value.previous
  have previousEq : routableRun.value.previous = rowFiveRun.value :=
    routableProfile.run_previous rowFiveRun.value
  rw [previousEq]
  exact rowFiveActive

def closedSuccessorActive :
    closedProfile.SuccessorFocus.Active closedRun.value := by
  change rowFiveProfile.TargetVisibleFocus.Active closedRun.value.previous
  have previousEq : closedRun.value.previous = rowFiveRun.value :=
    closedProfile.run_previous rowFiveRun.value
  rw [previousEq]
  exact rowFiveActive

def visibleSuccessorActive :
    visibleProfile.SuccessorFocus.Active visibleRun.value := by
  change rowFiveProfile.TargetVisibleFocus.Active visibleRun.value.previous
  have previousEq : visibleRun.value.previous = rowFiveRun.value :=
    visibleProfile.run_previous rowFiveRun.value
  rw [previousEq]
  exact rowFiveActive

def routableGenerated :=
  routableProfile.outputQuery.read routableRun.value routableSuccessorActive

def closedGenerated :=
  closedProfile.outputQuery.read closedRun.value closedSuccessorActive

def visibleGenerated :=
  visibleProfile.outputQuery.read visibleRun.value visibleSuccessorActive

theorem routableConditionAt
    (stage : DefectRouting.RowFiveStage rowFiveProfile)
    (active : rowFiveProfile.TargetVisibleFocus.Active stage) :
    routableProfile.Condition (Focus.ActiveView.of stage active)
      .finiteResistanceHarmonicZero := by
  change
    (routableContract
      (DefectRoutingAlignment.exactDefect rowFiveProfile
        routableRegistrationQuery boundaryCoordinateQuery stage active)).Finite ∧
      (routableContract
        (DefectRoutingAlignment.exactDefect rowFiveProfile
          routableRegistrationQuery boundaryCoordinateQuery stage active)).harmonic = 0
  constructor
  · simp [DirectResistanceContract.Finite, routableContract]
  · rfl

theorem closedConditionAt
    (stage : DefectRouting.RowFiveStage rowFiveProfile)
    (active : rowFiveProfile.TargetVisibleFocus.Active stage) :
    closedProfile.Condition (Focus.ActiveView.of stage active)
      .finiteResistanceHarmonicClosed := by
  change
    (harmonicContract
      (DefectRoutingAlignment.exactDefect rowFiveProfile
        closedGaugeRegistrationQuery boundaryCoordinateQuery stage active)).Finite ∧
      (harmonicContract
        (DefectRoutingAlignment.exactDefect rowFiveProfile
          closedGaugeRegistrationQuery boundaryCoordinateQuery stage active)).harmonic ≠ 0 ∧
      DefectRoutingAlignment.exactDefect rowFiveProfile
        closedGaugeRegistrationQuery boundaryCoordinateQuery stage active ∈
        (DefectRoutingAlignment.CurrentLedgerAt rowFiveProfile stage active).classes
  refine ⟨?_, ?_, ?_⟩
  · norm_num [DirectResistanceContract.Finite, harmonicContract]
  · change DefectRoutingAlignment.exactDefect rowFiveProfile
      closedGaugeRegistrationQuery boundaryCoordinateQuery stage active ≠ 0
    rw [closed_exact_defect]
    intro equal
    have first := congrArg (fun pressure : Pressure => pressure 0) equal
    norm_num at first
  · change IsGauge (DefectRoutingAlignment.exactDefect rowFiveProfile
      closedGaugeRegistrationQuery boundaryCoordinateQuery stage active)
    rw [closed_exact_defect]
    simp [IsGauge]

theorem visibleConditionAt
    (stage : DefectRouting.RowFiveStage rowFiveProfile)
    (active : rowFiveProfile.TargetVisibleFocus.Active stage) :
    visibleProfile.Condition (Focus.ActiveView.of stage active)
      .targetVisibleHarmonic := by
  change closureProfile.IsTargetVisible
    (DefectRoutingAlignment.parentView rowFiveProfile stage active)
    (DefectRoutingAlignment.exactDefect rowFiveProfile
      visibleGaugeRegistrationQuery boundaryCoordinateQuery stage active)
  rw [visible_exact_defect]
  change gaugeClassProject (pressurePair 1 2) = true
  have notGauge : Not (IsGauge (pressurePair 1 2)) := by
    norm_num [IsGauge]
  simp [gaugeClassProject, notGauge]

theorem routable_semantic_tag :
    routableGenerated.semanticTag? =
      some .finiteResistanceHarmonicZero :=
  routableProfile.generated_semanticTag_of_condition
    (Focus.ActiveView.of routableRun.value.previous routableSuccessorActive)
    routableGenerated .finiteResistanceHarmonicZero
    (routableConditionAt _ _)

theorem closed_semantic_tag :
    closedGenerated.semanticTag? =
      some .finiteResistanceHarmonicClosed :=
  closedProfile.generated_semanticTag_of_condition
    (Focus.ActiveView.of closedRun.value.previous closedSuccessorActive)
    closedGenerated .finiteResistanceHarmonicClosed
    (closedConditionAt _ _)

theorem visible_semantic_tag :
    visibleGenerated.semanticTag? = some .targetVisibleHarmonic :=
  visibleProfile.generated_semanticTag_of_condition
    (Focus.ActiveView.of visibleRun.value.previous visibleSuccessorActive)
    visibleGenerated .targetVisibleHarmonic
    (visibleConditionAt _ _)

theorem routable_disposition :
    routableGenerated.disposition = .capacityReady := by
  exact routableProfile.generated_disposition_of_condition
    (Focus.ActiveView.of routableRun.value.previous routableSuccessorActive)
    routableGenerated .finiteResistanceHarmonicZero
      (routableConditionAt _ _)

theorem closed_disposition :
    closedGenerated.disposition = .capacityReady := by
  exact closedProfile.generated_disposition_of_condition
    (Focus.ActiveView.of closedRun.value.previous closedSuccessorActive)
    closedGenerated .finiteResistanceHarmonicClosed
      (closedConditionAt _ _)

theorem visible_disposition :
    visibleGenerated.disposition = .targetVisibleHarmonic := by
  exact visibleProfile.generated_disposition_of_condition
    (Focus.ActiveView.of visibleRun.value.previous visibleSuccessorActive)
    visibleGenerated .targetVisibleHarmonic (visibleConditionAt _ _)

def routableCapacityReadyActive :
    routableProfile.CapacityReadyFocus.Active routableRun.value where
  parent := routableSuccessorActive
  accepted := routable_disposition

def closedCapacityReadyActive :
    closedProfile.CapacityReadyFocus.Active closedRun.value where
  parent := closedSuccessorActive
  accepted := closed_disposition

def visibleHarmonicActive :
    visibleProfile.TargetVisibleHarmonicFocus.Active visibleRun.value where
  parent := visibleSuccessorActive
  accepted := visible_disposition

def queriedRoutable :=
  routableProfile.capacityReadyOutputQuery.read
    routableRun.value routableCapacityReadyActive

def queriedClosed :=
  closedProfile.capacityReadyOutputQuery.read
    closedRun.value closedCapacityReadyActive

def queriedVisible :=
  visibleProfile.targetVisibleHarmonicOutputQuery.read
    visibleRun.value visibleHarmonicActive

theorem focused_queries_read_exact_outputs :
    queriedRoutable.val = routableGenerated ∧
      queriedClosed.val = closedGenerated ∧
      queriedVisible.val = visibleGenerated := by
  exact ⟨rfl, rfl, rfl⟩

theorem routable_relation_checks_exact :
    routableGenerated.interpretation.checks = 1 := by
  simpa using routableProfile.generated_relation_checks_of_condition
    (Focus.ActiveView.of routableRun.value.previous routableSuccessorActive)
    routableGenerated .finiteResistanceHarmonicZero
      (routableConditionAt _ _)

theorem closed_relation_checks_exact :
    closedGenerated.interpretation.checks = 2 := by
  simpa using closedProfile.generated_relation_checks_of_condition
    (Focus.ActiveView.of closedRun.value.previous closedSuccessorActive)
    closedGenerated .finiteResistanceHarmonicClosed
      (closedConditionAt _ _)

theorem visible_relation_checks_exact :
    visibleGenerated.interpretation.checks = 3 := by
  simpa using visibleProfile.generated_relation_checks_of_condition
    (Focus.ActiveView.of visibleRun.value.previous visibleSuccessorActive)
    visibleGenerated .targetVisibleHarmonic (visibleConditionAt _ _)

theorem routable_rejects_target_visible_focus :
    Not (routableProfile.TargetVisibleHarmonicFocus.Active routableRun.value) := by
  intro selected
  have impossible := selected.accepted
  change routableGenerated.disposition = .targetVisibleHarmonic at impossible
  rw [routable_disposition] at impossible
  cases impossible

theorem closed_rejects_target_visible_focus :
    Not (closedProfile.TargetVisibleHarmonicFocus.Active closedRun.value) := by
  intro selected
  have impossible := selected.accepted
  change closedGenerated.disposition = .targetVisibleHarmonic at impossible
  rw [closed_disposition] at impossible
  cases impossible

theorem visible_rejects_capacity_ready_focus :
    Not (visibleProfile.CapacityReadyFocus.Active visibleRun.value) := by
  intro selected
  have impossible := selected.accepted
  change visibleGenerated.disposition = .capacityReady at impossible
  rw [visible_disposition] at impossible
  cases impossible

theorem routable_retains_literal_row_five :
    routableRun.value.previous = rowFiveRun.value :=
  routableProfile.run_previous rowFiveRun.value

theorem closed_retains_literal_row_five :
    closedRun.value.previous = rowFiveRun.value :=
  closedProfile.run_previous rowFiveRun.value

theorem visible_retains_literal_row_five :
    visibleRun.value.previous = rowFiveRun.value :=
  visibleProfile.run_previous rowFiveRun.value

theorem runs_retain_root_residual :
    Residual.residualOf routableRun.value = () ∧
      Residual.residualOf closedRun.value = () ∧
      Residual.residualOf visibleRun.value = () := by
  exact ⟨rfl, rfl, rfl⟩

theorem routable_successor_exact_defect :
    routableProfile.exactDefectQueryAtSuccessor.read
      routableRun.value routableSuccessorActive = pressurePair 1 2 := by
  change DefectRoutingAlignment.exactDefect rowFiveProfile
    routableRegistrationQuery boundaryCoordinateQuery
      routableRun.value.previous routableSuccessorActive = pressurePair 1 2
  exact routable_exact_defect _ _

theorem closed_successor_exact_defect :
    closedProfile.exactDefectQueryAtSuccessor.read
      closedRun.value closedSuccessorActive = pressurePair 1 1 := by
  change DefectRoutingAlignment.exactDefect rowFiveProfile
    closedGaugeRegistrationQuery boundaryCoordinateQuery
      closedRun.value.previous closedSuccessorActive = pressurePair 1 1
  exact closed_exact_defect _ _

theorem visible_successor_exact_defect :
    visibleProfile.exactDefectQueryAtSuccessor.read
      visibleRun.value visibleSuccessorActive = pressurePair 1 2 := by
  change DefectRoutingAlignment.exactDefect rowFiveProfile
    visibleGaugeRegistrationQuery boundaryCoordinateQuery
      visibleRun.value.previous visibleSuccessorActive = pressurePair 1 2
  exact visible_exact_defect _ _

theorem successor_quotient_kills_constant_gauge :
    (closedProfile.currentQuotientQueryAtSuccessor.read
      closedRun.value closedSuccessorActive).project (pressurePair 3 3) =
        (closedProfile.currentQuotientQueryAtSuccessor.read
          closedRun.value closedSuccessorActive).null := by
  change gaugeClassProject (pressurePair 3 3) = false
  have gauge : IsGauge (pressurePair 3 3) := by simp [IsGauge]
  simp [gaugeClassProject, gauge]

theorem successor_quotient_preserves_visible_oscillation :
    (visibleProfile.currentQuotientQueryAtSuccessor.read
      visibleRun.value visibleSuccessorActive).project (pressurePair 1 2) ≠
        (visibleProfile.currentQuotientQueryAtSuccessor.read
          visibleRun.value visibleSuccessorActive).null := by
  change gaugeClassProject (pressurePair 1 2) ≠ false
  have notGauge : Not (IsGauge (pressurePair 1 2)) := by
    norm_num [IsGauge]
  simp [gaugeClassProject, notGauge]

abbrev rowSixView : DefectRouting.ActiveView rowFiveProfile :=
  Focus.ActiveView.of rowFiveRun.value rowFiveActive

theorem source_neutral_ct_work_exact :
    (CT13.generateCounted routableProfile.tieredCapability rowSixView).checks = 2 ∧
      (CT7.generateCounted routableProfile.contextCapability rowSixView).checks = 4 := by
  decide

theorem closed_source_neutral_ct_work_exact :
    (CT13.generateCounted closedProfile.tieredCapability rowSixView).checks = 2 ∧
      (CT7.generateCounted closedProfile.contextCapability rowSixView).checks = 4 := by
  decide

theorem visible_source_neutral_ct_work_exact :
    (CT13.generateCounted visibleProfile.tieredCapability rowSixView).checks = 2 ∧
      (CT7.generateCounted visibleProfile.contextCapability rowSixView).checks = 4 := by
  decide

theorem routable_active_generation_checks_exact :
    (DefectRouting.generateActiveCounted routableProfile.toRaw rowSixView).checks = 7 := by
  rw [routableProfile.generateActiveCounted_checks_of_condition rowSixView
    .finiteResistanceHarmonicZero
    (routableConditionAt rowFiveRun.value rowFiveActive)]
  rcases source_neutral_ct_work_exact with ⟨tiered, context⟩
  rw [tiered, context]
  rfl

theorem closed_active_generation_checks_exact :
    (DefectRouting.generateActiveCounted closedProfile.toRaw rowSixView).checks = 8 := by
  rw [closedProfile.generateActiveCounted_checks_of_condition rowSixView
    .finiteResistanceHarmonicClosed
    (closedConditionAt rowFiveRun.value rowFiveActive)]
  rcases closed_source_neutral_ct_work_exact with ⟨tiered, context⟩
  rw [tiered, context]
  rfl

theorem visible_active_generation_checks_exact :
    (DefectRouting.generateActiveCounted visibleProfile.toRaw rowSixView).checks = 9 := by
  rw [visibleProfile.generateActiveCounted_checks_of_condition rowSixView
    .targetVisibleHarmonic
    (visibleConditionAt rowFiveRun.value rowFiveActive)]
  rcases visible_source_neutral_ct_work_exact with ⟨tiered, context⟩
  rw [tiered, context]
  rfl

theorem routable_run_checks_exact : routableRun.checks = 8 := by
  change (routableProfile.run rowFiveRun.value).checks = 8
  rw [routableProfile.run_checks_of_active_condition rowFiveRun.value rowFiveActive
    .finiteResistanceHarmonicZero
    (routableConditionAt rowFiveRun.value rowFiveActive)]
  rcases source_neutral_ct_work_exact with ⟨tiered, context⟩
  rw [tiered, context]
  rfl

theorem closed_run_checks_exact : closedRun.checks = 9 := by
  change (closedProfile.run rowFiveRun.value).checks = 9
  rw [closedProfile.run_checks_of_active_condition rowFiveRun.value rowFiveActive
    .finiteResistanceHarmonicClosed
    (closedConditionAt rowFiveRun.value rowFiveActive)]
  rcases closed_source_neutral_ct_work_exact with ⟨tiered, context⟩
  rw [tiered, context]
  rfl

theorem visible_run_checks_exact : visibleRun.checks = 10 := by
  change (visibleProfile.run rowFiveRun.value).checks = 10
  rw [visibleProfile.run_checks_of_active_condition rowFiveRun.value rowFiveActive
    .targetVisibleHarmonic
    (visibleConditionAt rowFiveRun.value rowFiveActive)]
  rcases visible_source_neutral_ct_work_exact with ⟨tiered, context⟩
  rw [tiered, context]
  rfl

def routable_run_is_bounded :=
  routableProfile.run_checks_bounded rowFiveRun.value

def closed_run_is_bounded :=
  closedProfile.run_checks_bounded rowFiveRun.value

def visible_run_is_bounded :=
  visibleProfile.run_checks_bounded rowFiveRun.value

#print axioms gaugeEquivalent_iff_oscillation_eq
#print axioms zero_generator_defect_apply
#print axioms matching_generator_defect_apply
#print axioms routable_semantic_tag
#print axioms closed_semantic_tag
#print axioms visible_semantic_tag
#print axioms routable_run_checks_exact
#print axioms closed_run_checks_exact
#print axioms visible_run_checks_exact
#print axioms routable_run_is_bounded

end

end Hypostructure.Fixtures.PDERow6FinitePressureGaugeAlignment
