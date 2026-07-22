import Hypostructure.Core.Metadata
import Hypostructure.PDE.DirectResistance
import Hypostructure.PDE.FastTrack.DefectRouting

/-!
# Exact analytic alignment for PDE defect routing

This layer turns row 6's source-neutral CT13/CT7 transcript into the three
source semantic outcomes. It consumes the row-4 represented defect operator
through an active query, evaluates it at the exact row-5 selected boundary
class, reads the unchanged row-5 closed ledger and quotient, and derives every
semantic predicate from one direct-resistance contract.

Applications provide no semantic tag, raw-output table, route, successor, or
ledger mutation. They prove one exhaustive analytic classification for the
exact predecessor-owned objects; the existing framework scan selects the
unique tag and owns the focused extension.
-/

namespace Hypostructure.PDE.FastTrack.DefectRoutingAlignment

open Hypostructure.Core

universe uPrevious uPotential uCurrent uModel uDefectQuotient uCompensator
  uPayer uObstruction uResource uRepresentative uContext uCoordinate uValue

variable {Previous : Type uPrevious}
variable {Potential : Type uPotential} {Current : Type uCurrent}
variable [NormedAddCommGroup Potential] [InnerProductSpace Real Potential]
variable [CompleteSpace Potential]
variable [NormedAddCommGroup Current] [InnerProductSpace Real Current]
variable [CompleteSpace Current]

abbrev RowFiveStage
    {focus : Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current) :=
  DefectRouting.RowFiveStage rowFive

abbrev ActiveView
    {focus : Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current) :=
  DefectRouting.ActiveView rowFive

/-- Recover row 5's original focused view from the exact row-6 focus. -/
def parentView
    {focus : Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current)
    (stage : RowFiveStage rowFive)
    (active : rowFive.TargetVisibleFocus.Active stage) :
    DirectedExhaustiveness.ActiveView focus :=
  Residual.Focus.ActiveView.of stage.previous active.parent

/-- Exact predecessor-owned closed ledger used by row 6. -/
abbrev CurrentLedgerAt
    {focus : Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current)
    (stage : RowFiveStage rowFive)
    (active : rowFive.TargetVisibleFocus.Active stage) :=
  rowFive.closureProfile.ledgerAt (parentView rowFive stage active)

/-- Exact predecessor-owned quotient used by row 6. -/
abbrev CurrentQuotientAt
    {focus : Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current)
    (stage : RowFiveStage rowFive)
    (active : rowFive.TargetVisibleFocus.Active stage) :=
  rowFive.closureProfile.quotientAt (parentView rowFive stage active)

/-- Exact class selected by row 5's target-visible boundary scan. -/
def selectedCarrier
    {focus : Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current)
    (stage : RowFiveStage rowFive)
    (active : rowFive.TargetVisibleFocus.Active stage) :
    rowFive.closureProfile.Carrier :=
  (rowFive.targetVisibleBoundaryQuery.read stage active).closure.residual.hit.value

/-- Evaluate the exact represented row-4 defect operator at the coordinate of
the exact row-5 selected boundary class. -/
def exactDefect
    {focus : Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current)
    {M : LocalModel.{uModel}}
    {DefectQuotient : Type uDefectQuotient}
    [AddCommGroup DefectQuotient] [Module Real DefectQuotient]
    [NormedAddCommGroup rowFive.closureProfile.Carrier]
    [InnerProductSpace Real rowFive.closureProfile.Carrier]
    [CompleteSpace rowFive.closureProfile.Carrier]
    (registration : Residual.Focus.ActiveQuery rowFive.TargetVisibleFocus
      fun _stage _active => QuotientDefectRegistration M
        rowFive.closureProfile.Carrier DefectQuotient)
    (coordinate : Residual.Focus.ActiveQuery rowFive.TargetVisibleFocus
      fun _stage _active =>
        rowFive.closureProfile.Carrier →ₗ[Real] DefectQuotient)
    (stage : RowFiveStage rowFive)
    (active : rowFive.TargetVisibleFocus.Active stage) :
    rowFive.closureProfile.Carrier :=
  let registered := registration.read stage active
  registered.defect
    ((coordinate.read stage active) (selectedCarrier rowFive stage active))

/-- Exact exhaustive source classification at one active predecessor. -/
structure RoutingCompleteAt
    {focus : Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current)
    [NormedAddCommGroup rowFive.closureProfile.Carrier]
    [InnerProductSpace Real rowFive.closureProfile.Carrier]
    [CompleteSpace rowFive.closureProfile.Carrier]
    {geometry : DefectGeometry rowFive.closureProfile.Carrier}
    {defect : rowFive.closureProfile.Carrier}
    {ResistancePotential : Type uCompensator}
    (contract : DirectResistanceContract rowFive.closureProfile.Carrier
      geometry defect ResistancePotential)
    (stage : RowFiveStage rowFive)
    (active : rowFive.TargetVisibleFocus.Active stage) : Prop where
  classify :
    (contract.Finite /\ contract.harmonic = 0) \/
      (contract.Finite /\ contract.harmonic ≠ 0 /\
        contract.harmonic ∈ (CurrentLedgerAt rowFive stage active).classes) \/
      rowFive.closureProfile.IsTargetVisible
        (parentView rowFive stage active) contract.harmonic

/-- Minimal strict row-6 analytic registration. All hard values and proofs are
active queries on the exact row-5 target-visible focus. -/
structure Profile
    {focus : Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current)
    (M : LocalModel.{uModel})
    (DefectQuotient : Type uDefectQuotient)
    [AddCommGroup DefectQuotient] [Module Real DefectQuotient]
    [NormedAddCommGroup rowFive.closureProfile.Carrier]
    [InnerProductSpace Real rowFive.closureProfile.Carrier]
    [CompleteSpace rowFive.closureProfile.Carrier] where
  ResistancePotential : Type uCompensator
  tieredSpec : Hypostructure.CT13.Spec.{_, uPayer, uObstruction, uResource}
    (ActiveView rowFive)
  tieredCapability : Hypostructure.CT13.Capability tieredSpec
  contextSpec : Hypostructure.CT7.Spec.{_, uRepresentative, uContext,
    uCoordinate, uValue} (ActiveView rowFive)
  contextCapability : Hypostructure.CT7.Capability contextSpec
  defectRegistration : Residual.Focus.ActiveQuery rowFive.TargetVisibleFocus
    fun _stage _active => QuotientDefectRegistration M
      rowFive.closureProfile.Carrier DefectQuotient
  boundaryCoordinate : Residual.Focus.ActiveQuery rowFive.TargetVisibleFocus
    fun _stage _active =>
      rowFive.closureProfile.Carrier →ₗ[Real] DefectQuotient
  resistanceContract : Residual.Focus.ActiveQuery rowFive.TargetVisibleFocus
    fun stage active =>
      DirectResistanceContract rowFive.closureProfile.Carrier
        (defectRegistration.read stage active).geometry
        (exactDefect rowFive defectRegistration boundaryCoordinate stage active)
        ResistancePotential
  harmonicZeroDecidable : Residual.Focus.ActiveQuery rowFive.TargetVisibleFocus
    fun stage active =>
      Decidable ((resistanceContract.read stage active).harmonic = 0)
  harmonicLedgerDecidable :
    Residual.Focus.ActiveQuery rowFive.TargetVisibleFocus fun stage active =>
      Decidable ((resistanceContract.read stage active).harmonic ∈
        (CurrentLedgerAt rowFive stage active).classes)
  zeroClosed : Residual.Focus.ActiveQuery rowFive.TargetVisibleFocus
    fun stage active =>
      (0 : rowFive.closureProfile.Carrier) ∈
        (CurrentLedgerAt rowFive stage active).classes
  routingComplete : Residual.Focus.ActiveQuery rowFive.TargetVisibleFocus
    fun stage active =>
      RoutingCompleteAt rowFive (resistanceContract.read stage active)
        stage active

namespace Profile

variable {focus : Residual.Focus.Profile Previous}
variable {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
variable {M : LocalModel.{uModel}}
variable {DefectQuotient : Type uDefectQuotient}
variable [AddCommGroup DefectQuotient] [Module Real DefectQuotient]
variable [NormedAddCommGroup rowFive.closureProfile.Carrier]
variable [InnerProductSpace Real rowFive.closureProfile.Carrier]
variable [CompleteSpace rowFive.closureProfile.Carrier]

/-- Exact resistance contract read at one active view. -/
abbrev resistanceAt
    (profile : Profile rowFive M DefectQuotient)
    (view : ActiveView rowFive) :=
  profile.resistanceContract.read view.previous view.proof

/-- Exact harmonic component read from the predecessor-owned contract. -/
def harmonicAt
    (profile : Profile rowFive M DefectQuotient)
    (view : ActiveView rowFive) : rowFive.closureProfile.Carrier :=
  (profile.resistanceAt view).harmonic

/-- Semantic condition associated with one source tag. -/
def Condition
    (profile : Profile rowFive M DefectQuotient)
    (view : ActiveView rowFive) : DefectRouting.SemanticTag -> Prop
  | .finiteResistanceHarmonicZero =>
      (profile.resistanceAt view).Finite /\ profile.harmonicAt view = 0
  | .finiteResistanceHarmonicClosed =>
      (profile.resistanceAt view).Finite /\ profile.harmonicAt view ≠ 0 /\
        profile.harmonicAt view ∈
          (CurrentLedgerAt rowFive view.previous view.proof).classes
  | .targetVisibleHarmonic =>
      rowFive.closureProfile.IsTargetVisible
        (parentView rowFive view.previous view.proof) (profile.harmonicAt view)

/-- Every source condition is decided from exact predecessor-owned deciders. -/
def conditionDecidable
    (profile : Profile rowFive M DefectQuotient)
    (view : ActiveView rowFive) (tag : DefectRouting.SemanticTag) :
    Decidable (profile.Condition view tag) := by
  letI : Decidable ((profile.resistanceAt view).Finite) :=
    (profile.resistanceAt view).finiteDecidable
  letI : Decidable (profile.harmonicAt view = 0) :=
    profile.harmonicZeroDecidable.read view.previous view.proof
  letI : Decidable (profile.harmonicAt view ∈
      (CurrentLedgerAt rowFive view.previous view.proof).classes) :=
    profile.harmonicLedgerDecidable.read view.previous view.proof
  letI : Decidable (rowFive.closureProfile.IsTargetVisible
      (parentView rowFive view.previous view.proof)
      (profile.harmonicAt view)) :=
    rowFive.closureProfile.targetVisibleDecidable
      (parentView rowFive view.previous view.proof)
      ((CurrentQuotientAt rowFive view.previous view.proof).project
        (profile.harmonicAt view))
  cases tag <;> simp only [Condition] <;> infer_instance

/-- A target-visible class cannot already belong to the exact current ledger. -/
theorem targetVisible_not_closed
    (profile : Profile rowFive M DefectQuotient)
    (view : ActiveView rowFive)
    (visible : rowFive.closureProfile.IsTargetVisible
      (parentView rowFive view.previous view.proof) (profile.harmonicAt view)) :
    profile.harmonicAt view ∉
      (CurrentLedgerAt rowFive view.previous view.proof).classes := by
  intro closed
  exact rowFive.closureProfile.visibleNonzero
    (parentView rowFive view.previous view.proof) visible
    ((CurrentQuotientAt rowFive view.previous view.proof).killsClosed closed)

/-- Full framework-derived evidence attached to the target-visible harmonic
route. The application proves only visibility; the exact unchanged ledger and
the registered resistance contract force nonzero harmonicity and
nonroutability. -/
structure TargetVisibleEvidence
    (profile : Profile rowFive M DefectQuotient)
    (view : ActiveView rowFive) : Prop where
  nonzero : profile.harmonicAt view ≠ 0
  notRoutable : ¬ (Exists fun potential : profile.ResistancePotential =>
    (profile.resistanceAt view).action potential = profile.harmonicAt view)
  visible : rowFive.closureProfile.IsTargetVisible
    (parentView rowFive view.previous view.proof) (profile.harmonicAt view)

/-- Derive complete target-harmonic route evidence without another author
field. -/
theorem targetVisibleEvidence
    (profile : Profile rowFive M DefectQuotient)
    (view : ActiveView rowFive)
    (visible : rowFive.closureProfile.IsTargetVisible
      (parentView rowFive view.previous view.proof) (profile.harmonicAt view)) :
    TargetVisibleEvidence profile view := by
  have nonzero : profile.harmonicAt view ≠ 0 := by
    intro equalZero
    have zeroClosed := profile.zeroClosed.read view.previous view.proof
    exact (profile.targetVisible_not_closed view visible)
      (equalZero ▸ zeroClosed)
  exact {
    nonzero := nonzero
    notRoutable :=
      (profile.resistanceAt view).nonzero_harmonic_not_routable nonzero
    visible := visible
  }

/-- The three exact source conditions are pairwise disjoint. -/
theorem condition_functional
    (profile : Profile rowFive M DefectQuotient)
    (view : ActiveView rowFive)
    {left right : DefectRouting.SemanticTag}
    (leftCondition : profile.Condition view left)
    (rightCondition : profile.Condition view right) : left = right := by
  cases left <;> cases right
  · rfl
  · exact (rightCondition.2.1 leftCondition.2).elim
  · have zeroClosed := profile.zeroClosed.read view.previous view.proof
    exact (profile.targetVisible_not_closed view rightCondition)
      (leftCondition.2 ▸ zeroClosed) |>.elim
  · exact (leftCondition.2.1 rightCondition.2).elim
  · rfl
  · exact (profile.targetVisible_not_closed view rightCondition
      leftCondition.2.2).elim
  · have zeroClosed := profile.zeroClosed.read view.previous view.proof
    exact (profile.targetVisible_not_closed view leftCondition)
      (rightCondition.2 ▸ zeroClosed) |>.elim
  · exact (profile.targetVisible_not_closed view leftCondition
      rightCondition.2.2).elim
  · rfl

/-- Exact source-neutral predicates passed to the lower-level raw executor. -/
def finiteResistancePredicate
    (profile : Profile rowFive M DefectQuotient) :
    DefectRouting.SemanticPredicate rowFive profile.tieredCapability
      profile.contextCapability :=
  fun view _boundary _raw => (profile.resistanceAt view).Finite

def harmonicZeroPredicate
    (profile : Profile rowFive M DefectQuotient) :
    DefectRouting.SemanticPredicate rowFive profile.tieredCapability
      profile.contextCapability :=
  fun view _boundary _raw => profile.harmonicAt view = 0

def harmonicLedgerPredicate
    (profile : Profile rowFive M DefectQuotient) :
    DefectRouting.SemanticPredicate rowFive profile.tieredCapability
      profile.contextCapability :=
  fun view _boundary _raw =>
    profile.harmonicAt view ≠ 0 /\
      profile.harmonicAt view ∈
        (CurrentLedgerAt rowFive view.previous view.proof).classes

def targetVisiblePredicate
    (profile : Profile rowFive M DefectQuotient) :
    DefectRouting.SemanticPredicate rowFive profile.tieredCapability
      profile.contextCapability :=
  fun view _boundary _raw => TargetVisibleEvidence profile view

/-- Framework analytic alignment derived from exact semantic conditions. -/
def alignmentAt
    (profile : Profile rowFive M DefectQuotient)
    (view : ActiveView rowFive)
    (boundary : DefectRouting.BoundaryAt rowFive view)
    (complete : RoutingCompleteAt rowFive (profile.resistanceAt view)
      view.previous view.proof) :
    DefectRouting.AnalyticAlignment rowFive profile.tieredCapability
      profile.contextCapability profile.finiteResistancePredicate
      profile.harmonicZeroPredicate profile.harmonicLedgerPredicate
      profile.targetVisiblePredicate view boundary where
  relates := fun _raw tag => profile.Condition view tag
  decidableRelates := fun _raw tag => profile.conditionDecidable view tag
  sound := by
    intro _raw tag condition
    cases tag with
    | finiteResistanceHarmonicZero => exact condition
    | finiteResistanceHarmonicClosed => exact condition
    | targetVisibleHarmonic =>
        exact profile.targetVisibleEvidence view condition
  complete := fun _raw => by
    rcases complete.classify with zero | closed | visible
    · exact ⟨.finiteResistanceHarmonicZero, zero⟩
    · exact ⟨.finiteResistanceHarmonicClosed, closed⟩
    · exact ⟨.targetVisibleHarmonic, visible⟩
  functional := by
    intro _raw left right leftCondition rightCondition
    exact profile.condition_functional view leftCondition rightCondition

/-- Construct the lower-level row-6 executor profile. The only available
alignment is the one derived above; no caller-supplied relation survives. -/
def toRaw
    (profile : Profile rowFive M DefectQuotient) :
    DefectRouting.Profile rowFive where
  tieredSpec := profile.tieredSpec
  tieredCapability := profile.tieredCapability
  contextSpec := profile.contextSpec
  contextCapability := profile.contextCapability
  FiniteResistance := profile.finiteResistancePredicate
  HarmonicZero := profile.harmonicZeroPredicate
  HarmonicLedgerMember := profile.harmonicLedgerPredicate
  NonroutableTargetVisible := profile.targetVisiblePredicate
  alignmentRegistration := profile.routingComplete.map fun stage active complete =>
    .available (profile.alignmentAt
      (Residual.Focus.ActiveView.of stage active)
      (rowFive.targetVisibleBoundaryQuery.read stage active) complete)

/-- Exact evaluated defect as a typed query on the active row-6 predecessor. -/
def exactDefectQuery
    (profile : Profile rowFive M DefectQuotient) :
    Residual.Focus.ActiveQuery rowFive.TargetVisibleFocus
      fun _stage _active => rowFive.closureProfile.Carrier :=
  (profile.defectRegistration.and
    (profile.boundaryCoordinate.and
      rowFive.targetVisibleBoundaryQuery)).map
        fun _stage _active registered =>
          registered.fst.defect
            (registered.snd.fst registered.snd.snd.closure.residual.hit.value)

/-- Exact current closed ledger as a typed query. It is derived from row 5 and
is not a row-6 author field. -/
def currentLedgerQuery
    (profile : Profile rowFive M DefectQuotient) :
    Residual.Focus.ActiveQuery rowFive.TargetVisibleFocus
      fun _stage _active =>
        ClosedClassLedger rowFive.closureProfile.closure
          rowFive.closureProfile.TargetNull :=
  profile.zeroClosed.map fun stage active _zeroClosed =>
    rowFive.closureProfile.ledgerAt (parentView rowFive stage active)

/-- Exact current ledger quotient as a typed query. -/
def currentQuotientQuery
    (profile : Profile rowFive M DefectQuotient) :
    Residual.Focus.ActiveQuery rowFive.TargetVisibleFocus
      fun stage active =>
        LedgerQuotient (CurrentLedgerAt rowFive stage active) :=
  profile.zeroClosed.map fun stage active _zeroClosed =>
    rowFive.closureProfile.quotientAt (parentView rowFive stage active)

/-- The strict profile always installs the framework-derived available
alignment at the exact predecessor. -/
theorem alignmentRegistration_is_available
    (profile : Profile rowFive M DefectQuotient)
    (view : ActiveView rowFive) :
    (profile.toRaw).alignmentRegistration.read view.previous view.proof =
      .available (profile.alignmentAt view
        (rowFive.targetVisibleBoundaryQuery.read view.previous view.proof)
        (profile.routingComplete.read view.previous view.proof)) :=
  rfl

/-- A proved strict source condition determines the framework-selected
disposition of every generated transcript at the same exact active view.  The
caller does not choose the tag: functionality of the registered alignment
identifies it with Core's canonical first hit. -/
theorem generated_disposition_of_condition
    (profile : Profile rowFive M DefectQuotient)
    (view : ActiveView rowFive)
    (generated : DefectRouting.Generated profile.toRaw view)
    (tag : DefectRouting.SemanticTag)
    (condition : profile.Condition view tag) :
    generated.disposition = tag.disposition := by
  rcases view with ⟨previous, proof⟩
  change generated.interpretation.disposition = tag.disposition
  cases generated.interpretation with
  | aligned selection =>
      change selection.tag.disposition = tag.disposition
      exact congrArg DefectRouting.SemanticTag.disposition
        (selection.unique tag condition).symm

/-- A proved strict source condition identifies the exact semantic tag retained
by the generated interpretation. -/
theorem generated_semanticTag_of_condition
    (profile : Profile rowFive M DefectQuotient)
    (view : ActiveView rowFive)
    (generated : DefectRouting.Generated profile.toRaw view)
    (tag : DefectRouting.SemanticTag)
    (condition : profile.Condition view tag) :
    generated.semanticTag? = some tag := by
  rcases view with ⟨previous, proof⟩
  change generated.interpretation.semanticTag? = some tag
  cases generated.interpretation with
  | aligned selection =>
      simp only [DefectRouting.Interpretation.semanticTag?, Option.some.injEq]
      exact selection.tag_eq_of_relates tag condition

/-- A proved strict source condition determines the exact canonical relation
prefix retained by the generated interpretation. -/
theorem generated_relation_checks_of_condition
    (profile : Profile rowFive M DefectQuotient)
    (view : ActiveView rowFive)
    (generated : DefectRouting.Generated profile.toRaw view)
    (tag : DefectRouting.SemanticTag)
    (condition : profile.Condition view tag) :
    generated.interpretation.checks = tag.prefixChecks := by
  rcases view with ⟨previous, proof⟩
  cases generated.interpretation with
  | aligned selection =>
      exact selection.checks_eq_prefix_of_relates tag condition

/-- Exact active payload work under one strict source condition: both shared CT
executions plus the canonical prefix of the uniquely selected semantic tag. -/
theorem generateActiveCounted_checks_of_condition
    (profile : Profile rowFive M DefectQuotient)
    (view : ActiveView rowFive)
    (tag : DefectRouting.SemanticTag)
    (condition : profile.Condition view tag) :
    (DefectRouting.generateActiveCounted profile.toRaw view).checks =
      ((Hypostructure.CT13.generateCounted
          profile.tieredCapability view).checks +
        (Hypostructure.CT7.generateCounted
          profile.contextCapability view).checks) + tag.prefixChecks := by
  rw [DefectRouting.generateActiveCounted_checks_of_available profile.toRaw view
    (profile.alignmentAt view (rowFive.targetVisibleBoundaryQuery.read
      view.previous view.proof)
      (profile.routingComplete.read view.previous view.proof))
    (profile.alignmentRegistration_is_available view)]
  rw [DefectRouting.scanAlignmentCounted_checks]
  congr 1
  exact
    (DefectRouting.scanAlignmentCounted profile.toRaw view
      (DefectRouting.generateRawCounted profile.toRaw view).value
      (profile.alignmentAt view (rowFive.targetVisibleBoundaryQuery.read
        view.previous view.proof)
        (profile.routingComplete.read view.previous view.proof))).value
      |>.checks_eq_prefix_of_relates tag condition

/-- Literal accumulated stage emitted by the strict row-6 executor. -/
abbrev Stage (profile : Profile rowFive M DefectQuotient) :=
  DefectRouting.Stage profile.toRaw

/-- Framework-owned successor focus for downstream rows. -/
abbrev SuccessorFocus (profile : Profile rowFive M DefectQuotient) :=
  (profile.toRaw).SuccessorFocus

/-- Retrieve the exact strict row-6 generated output. -/
def outputQuery (profile : Profile rowFive M DefectQuotient) :=
  (profile.toRaw).outputQuery

/-- Read the exact successor disposition without exposing a route choice. -/
def dispositionQuery (profile : Profile rowFive M DefectQuotient) :=
  (profile.toRaw).dispositionQuery

/-- Read the exact framework-selected semantic tag. -/
def semanticTagQuery (profile : Profile rowFive M DefectQuotient) :=
  (profile.toRaw).semanticTagQuery

/-- Typed downstream focus for one exact semantic tag. -/
abbrev SemanticTagFocus (profile : Profile rowFive M DefectQuotient)
    (tag : DefectRouting.SemanticTag) :=
  (profile.toRaw).SemanticTagFocus tag

/-- Read one exact generated output together with its selected semantic tag. -/
def semanticTagOutputQuery (profile : Profile rowFive M DefectQuotient)
    (tag : DefectRouting.SemanticTag) :=
  (profile.toRaw).semanticTagOutputQuery tag

/-- Successful finite-resistance focus inherited by row 7. -/
abbrev CapacityReadyFocus (profile : Profile rowFive M DefectQuotient) :=
  (profile.toRaw).CapacityReadyFocus

/-- Exact target-visible harmonic residual focus. -/
abbrev TargetVisibleHarmonicFocus
    (profile : Profile rowFive M DefectQuotient) :=
  (profile.toRaw).TargetVisibleHarmonicFocus

/-- Read one exact successful aligned output. -/
def capacityReadyOutputQuery
    (profile : Profile rowFive M DefectQuotient) :=
  (profile.toRaw).capacityReadyOutputQuery

/-- Read the exact target-visible harmonic residual. -/
def targetVisibleHarmonicOutputQuery
    (profile : Profile rowFive M DefectQuotient) :=
  (profile.toRaw).targetVisibleHarmonicOutputQuery

/-- Preserve the exact evaluated defect through the sole row-6 extension. -/
def exactDefectQueryAtSuccessor
    (profile : Profile rowFive M DefectQuotient) :
    Residual.Focus.ActiveQuery profile.SuccessorFocus
      fun _stage _active => rowFive.closureProfile.Carrier :=
  Residual.Focus.ActiveQuery.preserve
    (Output := DefectRouting.Output profile.toRaw) profile.exactDefectQuery

/-- Preserve the exact resistance contract through row 6. -/
def resistanceContractQueryAtSuccessor
    (profile : Profile rowFive M DefectQuotient) :
    Residual.Focus.ActiveQuery profile.SuccessorFocus fun stage active =>
      DirectResistanceContract rowFive.closureProfile.Carrier
        (profile.defectRegistration.read stage.previous active).geometry
        (exactDefect rowFive profile.defectRegistration
          profile.boundaryCoordinate stage.previous active)
        profile.ResistancePotential :=
  Residual.Focus.ActiveQuery.preserve
    (Output := DefectRouting.Output profile.toRaw) profile.resistanceContract

/-- Preserve the unchanged closed ledger through row 6. -/
def currentLedgerQueryAtSuccessor
    (profile : Profile rowFive M DefectQuotient) :
    Residual.Focus.ActiveQuery profile.SuccessorFocus fun _stage _active =>
      ClosedClassLedger rowFive.closureProfile.closure
        rowFive.closureProfile.TargetNull :=
  Residual.Focus.ActiveQuery.preserve
    (Output := DefectRouting.Output profile.toRaw) profile.currentLedgerQuery

/-- Preserve the unchanged quotient through row 6. -/
def currentQuotientQueryAtSuccessor
    (profile : Profile rowFive M DefectQuotient) :
    Residual.Focus.ActiveQuery profile.SuccessorFocus fun stage active =>
      LedgerQuotient (CurrentLedgerAt rowFive stage.previous active) :=
  Residual.Focus.ActiveQuery.preserve
    (Output := DefectRouting.Output profile.toRaw) profile.currentQuotientQuery

/-- Execute row 6 through the existing focused, counted raw machine. -/
def run
    (profile : Profile rowFive M DefectQuotient)
    (previous : RowFiveStage rowFive) : Counted profile.Stage :=
  DefectRouting.run profile.toRaw previous

/-- The strict executor retains the literal complete row-5 predecessor. -/
@[simp] theorem run_previous
    (profile : Profile rowFive M DefectQuotient)
    (previous : RowFiveStage rowFive) :
    (profile.run previous).value.previous = previous :=
  DefectRouting.run_previous profile.toRaw previous

/-- Exact work on an active predecessor is inherited from the complete raw
execution and the framework semantic scan. -/
theorem run_checks_of_active
    (profile : Profile rowFive M DefectQuotient)
    (previous : RowFiveStage rowFive)
    (active : rowFive.TargetVisibleFocus.Active previous) :
    (profile.run previous).checks =
      rowFive.TargetVisibleFocus.selectionBudget.checks previous +
      (DefectRouting.generateActiveCounted profile.toRaw
          (Residual.Focus.ActiveView.of previous active)).checks :=
  DefectRouting.run_checks_of_active profile.toRaw previous active

/-- Exact complete row-6 work under one strict source condition. -/
theorem run_checks_of_active_condition
    (profile : Profile rowFive M DefectQuotient)
    (previous : RowFiveStage rowFive)
    (active : rowFive.TargetVisibleFocus.Active previous)
    (tag : DefectRouting.SemanticTag)
    (condition : profile.Condition
      (Residual.Focus.ActiveView.of previous active) tag) :
    (profile.run previous).checks =
      rowFive.TargetVisibleFocus.selectionBudget.checks previous +
        (((Hypostructure.CT13.generateCounted profile.tieredCapability
          (Residual.Focus.ActiveView.of previous active)).checks +
        (Hypostructure.CT7.generateCounted profile.contextCapability
          (Residual.Focus.ActiveView.of previous active)).checks) +
        tag.prefixChecks) := by
  rw [profile.run_checks_of_active previous active]
  rw [profile.generateActiveCounted_checks_of_condition
    (Residual.Focus.ActiveView.of previous active) tag condition]

/-- Inactive row-5 siblings pay only the exact inherited selector. -/
theorem run_checks_of_inactive
    (profile : Profile rowFive M DefectQuotient)
    (previous : RowFiveStage rowFive)
    (inactive : Not (rowFive.TargetVisibleFocus.Active previous)) :
    (profile.run previous).checks =
      rowFive.TargetVisibleFocus.selectionBudget.checks previous :=
  DefectRouting.run_checks_of_inactive profile.toRaw previous inactive

/-- Every strict row-6 run satisfies the inherited polynomial work bound. -/
theorem run_checks_bounded
    (profile : Profile rowFive M DefectQuotient)
    (previous : RowFiveStage rowFive) :
    (profile.run previous).checks <=
      (rowFive.TargetVisibleFocus.selectionBudget.add
        (DefectRouting.payloadBudget profile.toRaw)).coefficient *
      ((rowFive.TargetVisibleFocus.selectionBudget.add
        (DefectRouting.payloadBudget profile.toRaw)).size previous + 1) ^
      (rowFive.TargetVisibleFocus.selectionBudget.add
      (DefectRouting.payloadBudget profile.toRaw)).degree :=
  DefectRouting.run_checks_bounded profile.toRaw previous

/-! ## Proof-relevant executor metadata -/

/-- Canonical audit record for one strict row-6 profile. Query declarations are
classified at the provision boundary below; the record carries the exact
composed work budget and generated-output inventory. -/
def metadata
    (profile : Profile rowFive M DefectQuotient) :
    Metadata.DeclarationMetadata (RowFiveStage rowFive)
      (RowFiveStage rowFive) where
  declaration :=
    ⟨"Hypostructure.PDE.FastTrack.DefectRoutingAlignment", "Profile.run"⟩
  primitiveInputs := [
    ⟨⟨"Hypostructure.PDE.Quotient", "QuotientDefectRegistration"⟩,
      .operator⟩,
    ⟨⟨"Hypostructure.PDE.DirectResistance", "DirectResistanceContract"⟩,
      .semanticLaw⟩,
    ⟨⟨"Hypostructure.CT13", "Capability"⟩, .decisionProcedure⟩,
    ⟨⟨"Hypostructure.CT7", "Capability"⟩, .decisionProcedure⟩,
    ⟨⟨"Hypostructure.PDE.FastTrack.DefectRoutingAlignment",
      "RoutingCompleteAt"⟩, .semanticLaw⟩
  ]
  inferredDependencies := [
    ⟨⟨"Hypostructure.Core.Residual.Focus", "ActiveQuery"⟩,
      .predecessorProjection⟩,
    ⟨⟨"Hypostructure.PDE.FastTrack.DefectRoutingAlignment", "exactDefect"⟩,
      .definitionalReduction⟩,
    ⟨⟨"Hypostructure.PDE.FastTrack.DefectRoutingAlignment",
      "Profile.targetVisibleEvidence"⟩, .registeredProfile⟩
  ]
  ledgerQueries := []
  focusedLedgerQueries := []
  frameworkSearch := [
    ⟨"Hypostructure.CT13", "generateCounted"⟩,
    ⟨"Hypostructure.CT7", "generateCounted"⟩,
    ⟨"Hypostructure.PDE.FastTrack.DefectRouting", "scanAlignmentCounted"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.PDE.FastTrack.DefectRouting", "Generated"⟩,
      .typedOutcome⟩,
    ⟨⟨"Hypostructure.Core.Residual.Focus", "runCountedPayload"⟩,
      .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.PDE.FastTrack.DefectRoutingAlignment",
      "Profile.targetVisibleEvidence"⟩,
    ⟨"Hypostructure.PDE.FastTrack.DefectRoutingAlignment",
      "Profile.generated_semanticTag_of_condition"⟩,
    ⟨"Hypostructure.PDE.FastTrack.DefectRoutingAlignment",
      "Profile.run_checks_of_active_condition"⟩,
    ⟨"Hypostructure.PDE.FastTrack.DefectRoutingAlignment",
      "Profile.run_checks_bounded"⟩
  ]
  workBound := rowFive.TargetVisibleFocus.selectionBudget.add
    (DefectRouting.payloadBudget profile.toRaw)
  manualObligations := []

/-- The canonical strict row-6 metadata has no unresolved manual obligation. -/
def metadataComplete
    (profile : Profile rowFive M DefectQuotient) :
    Metadata.Complete profile.metadata :=
  ⟨rfl⟩

end Profile

end Hypostructure.PDE.FastTrack.DefectRoutingAlignment

#print axioms Hypostructure.PDE.FastTrack.DefectRoutingAlignment.Profile.run
#print axioms Hypostructure.PDE.FastTrack.DefectRoutingAlignment.Profile.targetVisibleEvidence
#print axioms Hypostructure.PDE.FastTrack.DefectRoutingAlignment.Profile.generated_semanticTag_of_condition
#print axioms Hypostructure.PDE.FastTrack.DefectRoutingAlignment.Profile.generateActiveCounted_checks_of_condition
#print axioms Hypostructure.PDE.FastTrack.DefectRoutingAlignment.Profile.run_checks_of_active_condition
#print axioms Hypostructure.PDE.FastTrack.DefectRoutingAlignment.Profile.run_checks_bounded
#print axioms Hypostructure.PDE.FastTrack.DefectRoutingAlignment.Profile.metadataComplete
