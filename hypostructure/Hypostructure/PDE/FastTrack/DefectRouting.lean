import Hypostructure.Core.Finite.Accounting
import Hypostructure.CT13.Execution
import Hypostructure.CT7.Execution
import Hypostructure.PDE.FastTrack.DirectedExhaustiveness

/-!
# PDE fast-track row 6: defect routing

Row 6 consumes only row 5's target-visible focus. On an active predecessor it
runs CT13 and then CT7, retaining both exact generated values in a source-neutral
raw transcript. Neither CT terminal has PDE meaning here.

Semantic interpretation is optional predecessor-owned mathematics. When an
analytic alignment is unavailable, the raw transcript remains a typed active
residual. When it is available, Core performs the fixed three-tag first-hit
scan and records its exact prefix work. Exactly one focused payload is appended
to the literal row-5 stage.
-/

namespace Hypostructure.PDE.FastTrack.DefectRouting

open Hypostructure.Core

universe uPrevious uPotential uCurrent
  uPayer uObstruction uResource
  uRepresentative uContext uCoordinate uValue

variable {Previous : Type uPrevious}
variable {Potential : Type uPotential} {Current : Type uCurrent}
variable [NormedAddCommGroup Potential] [InnerProductSpace Real Potential]
variable [CompleteSpace Potential]
variable [NormedAddCommGroup Current] [InnerProductSpace Real Current]
variable [CompleteSpace Current]

/-- Literal row-5 successor stage accepted by row 6. -/
abbrev RowFiveStage
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current) :=
  DirectedExhaustiveness.Stage rowFive

/-- Exact refined active view selected by row 5's target-visible focus. -/
abbrev ActiveView
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current) :=
  Hypostructure.Core.Residual.Focus.ActiveView rowFive.TargetVisibleFocus

/-- Type of the exact row-5 target-visible boundary payload at one active view. -/
abbrev BoundaryAt
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current)
    (view : ActiveView rowFive) :=
  DirectedExhaustiveness.TargetVisibleBoundaryOutput rowFive
    (Hypostructure.Core.Residual.Focus.ActiveView.of
      view.previous.previous view.proof.parent)

/-- Read row 5's target-visible boundary payload from the literal predecessor. -/
def boundaryAt
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current)
    (view : ActiveView rowFive) : BoundaryAt rowFive view :=
  rowFive.targetVisibleBoundaryQuery.read view.previous view.proof

/-- Source-neutral transcript of the two exact output-only CT generations.
CT7 is indexed by the same active row-5 view and runs for every CT13 outcome. -/
structure RawTranscript
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current)
    {tieredSpec : Hypostructure.CT13.Spec (ActiveView rowFive)}
    (tieredCapability : Hypostructure.CT13.Capability tieredSpec)
    {contextSpec : Hypostructure.CT7.Spec (ActiveView rowFive)}
    (contextCapability : Hypostructure.CT7.Capability contextSpec)
    (view : ActiveView rowFive) where
  private mk ::
  ct13 : Hypostructure.CT13.Routed tieredCapability view
  ct7 : Hypostructure.CT7.Generated contextCapability view

namespace RawTranscript

variable {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
variable {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
variable {tieredSpec : Hypostructure.CT13.Spec (ActiveView rowFive)}
variable {tieredCapability : Hypostructure.CT13.Capability tieredSpec}
variable {contextSpec : Hypostructure.CT7.Spec (ActiveView rowFive)}
variable {contextCapability : Hypostructure.CT7.Capability contextSpec}
variable {view : ActiveView rowFive}

/-- Work retained by the two exact generated CT values. -/
def checks
    (raw : RawTranscript rowFive tieredCapability contextCapability view) : Nat :=
  raw.ct13.checks + raw.ct7.checks

end RawTranscript

/-- A semantic proposition over the exact predecessor boundary and exact raw
transcript. -/
abbrev SemanticPredicate
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current)
    {tieredSpec : Hypostructure.CT13.Spec (ActiveView rowFive)}
    (tieredCapability : Hypostructure.CT13.Capability tieredSpec)
    {contextSpec : Hypostructure.CT7.Spec (ActiveView rowFive)}
    (contextCapability : Hypostructure.CT7.Capability contextSpec) :=
  (view : ActiveView rowFive) ->
    BoundaryAt rowFive view ->
      RawTranscript rowFive tieredCapability contextCapability view -> Prop

/-- The exact source-prescribed row-6 semantic schedule. -/
inductive SemanticTag where
  | finiteResistanceHarmonicZero
  | finiteResistanceHarmonicClosed
  | targetVisibleHarmonic
  deriving DecidableEq, Repr

/-- Fixed framework enumeration used for analytic alignment. -/
def semanticTagEnumeration :
    Hypostructure.Core.Finite.Enumeration SemanticTag :=
  Hypostructure.Core.Finite.Enumeration.ofNodupList
    [.finiteResistanceHarmonicZero,
      .finiteResistanceHarmonicClosed,
      .targetVisibleHarmonic]
    (by simp)

@[simp] theorem semanticTag_mem (tag : SemanticTag) :
    tag ∈ semanticTagEnumeration.values := by
  change tag ∈
    [SemanticTag.finiteResistanceHarmonicZero,
      SemanticTag.finiteResistanceHarmonicClosed,
      SemanticTag.targetVisibleHarmonic]
  cases tag <;> simp

@[simp] theorem semanticTagEnumeration_card :
    semanticTagEnumeration.card = 3 := by
  rfl

namespace SemanticTag

/-- Canonical index of each source tag in the framework-owned row-6 scan. -/
def index : SemanticTag -> Fin semanticTagEnumeration.card
  | .finiteResistanceHarmonicZero => ⟨0, by decide⟩
  | .finiteResistanceHarmonicClosed => ⟨1, by decide⟩
  | .targetVisibleHarmonic => ⟨2, by decide⟩

/-- Exact relation-scan prefix paid when this tag is selected. -/
def prefixChecks (tag : SemanticTag) : Nat :=
  tag.index.1 + 1

@[simp] theorem enumeration_get_index (tag : SemanticTag) :
    semanticTagEnumeration.get tag.index = tag := by
  cases tag <;> rfl

@[simp] theorem finiteResistanceHarmonicZero_prefixChecks :
    finiteResistanceHarmonicZero.prefixChecks = 1 := by
  rfl

@[simp] theorem finiteResistanceHarmonicClosed_prefixChecks :
    finiteResistanceHarmonicClosed.prefixChecks = 2 := by
  rfl

@[simp] theorem targetVisibleHarmonic_prefixChecks :
    targetVisibleHarmonic.prefixChecks = 3 := by
  rfl

end SemanticTag

/-- Exact analytic content required for one framework-selected semantic tag.
No CT terminal appears in this definition. -/
def AlignedEvidence
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current)
    {tieredSpec : Hypostructure.CT13.Spec (ActiveView rowFive)}
    (tieredCapability : Hypostructure.CT13.Capability tieredSpec)
    {contextSpec : Hypostructure.CT7.Spec (ActiveView rowFive)}
    (contextCapability : Hypostructure.CT7.Capability contextSpec)
    (FiniteResistance HarmonicZero HarmonicLedgerMember
      NonroutableTargetVisible :
        SemanticPredicate rowFive tieredCapability contextCapability)
    (view : ActiveView rowFive) (boundary : BoundaryAt rowFive view)
    (raw : RawTranscript rowFive tieredCapability contextCapability view) :
    SemanticTag -> Prop
  | .finiteResistanceHarmonicZero =>
      FiniteResistance view boundary raw ∧ HarmonicZero view boundary raw
  | .finiteResistanceHarmonicClosed =>
      FiniteResistance view boundary raw ∧
        HarmonicLedgerMember view boundary raw
  | .targetVisibleHarmonic =>
      NonroutableTargetVisible view boundary raw

/-- Source-backed relation and laws for every raw transcript at one exact
predecessor view. The relation, not a CT constructor, determines semantics. -/
structure AnalyticAlignment
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current)
    {tieredSpec : Hypostructure.CT13.Spec (ActiveView rowFive)}
    (tieredCapability : Hypostructure.CT13.Capability tieredSpec)
    {contextSpec : Hypostructure.CT7.Spec (ActiveView rowFive)}
    (contextCapability : Hypostructure.CT7.Capability contextSpec)
    (FiniteResistance HarmonicZero HarmonicLedgerMember
      NonroutableTargetVisible :
        SemanticPredicate rowFive tieredCapability contextCapability)
    (view : ActiveView rowFive) (boundary : BoundaryAt rowFive view) where
  relates :
    RawTranscript rowFive tieredCapability contextCapability view ->
      SemanticTag -> Prop
  decidableRelates : forall raw tag, Decidable (relates raw tag)
  sound : forall raw tag, relates raw tag ->
    AlignedEvidence rowFive tieredCapability contextCapability
      FiniteResistance HarmonicZero HarmonicLedgerMember
      NonroutableTargetVisible view boundary raw tag
  complete : forall raw, Exists fun tag => relates raw tag
  functional : forall raw left right,
    relates raw left -> relates raw right -> left = right

/-- Typed open status recording that the exact predecessor has no registered
analytic alignment contract. It asserts no semantic outcome. -/
inductive MissingAnalyticAlignment
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current)
    {tieredSpec : Hypostructure.CT13.Spec (ActiveView rowFive)}
    (tieredCapability : Hypostructure.CT13.Capability tieredSpec)
    {contextSpec : Hypostructure.CT7.Spec (ActiveView rowFive)}
    (contextCapability : Hypostructure.CT7.Capability contextSpec)
    (FiniteResistance HarmonicZero HarmonicLedgerMember
      NonroutableTargetVisible :
        SemanticPredicate rowFive tieredCapability contextCapability)
    (view : ActiveView rowFive) (boundary : BoundaryAt rowFive view) where
  | notRegistered

/-- Exact predecessor-owned availability of the analytic alignment. -/
inductive AlignmentRegistration
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current)
    {tieredSpec : Hypostructure.CT13.Spec (ActiveView rowFive)}
    (tieredCapability : Hypostructure.CT13.Capability tieredSpec)
    {contextSpec : Hypostructure.CT7.Spec (ActiveView rowFive)}
    (contextCapability : Hypostructure.CT7.Capability contextSpec)
    (FiniteResistance HarmonicZero HarmonicLedgerMember
      NonroutableTargetVisible :
        SemanticPredicate rowFive tieredCapability contextCapability)
    (view : ActiveView rowFive) (boundary : BoundaryAt rowFive view) where
  | unavailable :
      MissingAnalyticAlignment rowFive tieredCapability contextCapability
        FiniteResistance HarmonicZero HarmonicLedgerMember
        NonroutableTargetVisible view boundary ->
      AlignmentRegistration rowFive tieredCapability contextCapability
        FiniteResistance HarmonicZero HarmonicLedgerMember
        NonroutableTargetVisible view boundary
  | available :
      AnalyticAlignment rowFive tieredCapability contextCapability
        FiniteResistance HarmonicZero HarmonicLedgerMember
        NonroutableTargetVisible view boundary ->
      AlignmentRegistration rowFive tieredCapability contextCapability
        FiniteResistance HarmonicZero HarmonicLedgerMember
        NonroutableTargetVisible view boundary

/-- Minimal row-6 registration. CT capabilities observe the same exact active
view. Every semantic law is supplied only through the active registration
query on the literal row-5 predecessor. -/
structure Profile
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current) where
  tieredSpec : Hypostructure.CT13.Spec.{_, uPayer, uObstruction, uResource}
    (ActiveView rowFive)
  tieredCapability : Hypostructure.CT13.Capability tieredSpec
  contextSpec : Hypostructure.CT7.Spec.{_, uRepresentative, uContext,
    uCoordinate, uValue} (ActiveView rowFive)
  contextCapability : Hypostructure.CT7.Capability contextSpec
  FiniteResistance :
    SemanticPredicate rowFive tieredCapability contextCapability
  HarmonicZero :
    SemanticPredicate rowFive tieredCapability contextCapability
  HarmonicLedgerMember :
    SemanticPredicate rowFive tieredCapability contextCapability
  NonroutableTargetVisible :
    SemanticPredicate rowFive tieredCapability contextCapability
  alignmentRegistration :
    Hypostructure.Core.Residual.Focus.ActiveQuery
      rowFive.TargetVisibleFocus fun stage active =>
        let view :=
          Hypostructure.Core.Residual.Focus.ActiveView.of stage active
        AlignmentRegistration rowFive tieredCapability contextCapability
          FiniteResistance HarmonicZero HarmonicLedgerMember
          NonroutableTargetVisible view
          (rowFive.targetVisibleBoundaryQuery.read stage active)

namespace Profile

variable {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
variable {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}

/-- Raw transcript type registered by one profile. -/
abbrev Raw (profile : Profile rowFive) (view : ActiveView rowFive) :=
  RawTranscript rowFive profile.tieredCapability profile.contextCapability view

/-- Exact tag-indexed evidence type registered by one profile. -/
abbrev Evidence (profile : Profile rowFive) (view : ActiveView rowFive)
    (raw : profile.Raw view) (tag : SemanticTag) :=
  AlignedEvidence rowFive profile.tieredCapability profile.contextCapability
    profile.FiniteResistance profile.HarmonicZero
    profile.HarmonicLedgerMember profile.NonroutableTargetVisible
    view (boundaryAt rowFive view) raw tag

/-- Alignment contract at the exact predecessor view. -/
abbrev AlignmentAt (profile : Profile rowFive) (view : ActiveView rowFive) :=
  AnalyticAlignment rowFive profile.tieredCapability profile.contextCapability
    profile.FiniteResistance profile.HarmonicZero
    profile.HarmonicLedgerMember profile.NonroutableTargetVisible
    view (boundaryAt rowFive view)

/-- Typed missing-alignment residual at the exact predecessor view. -/
abbrev MissingAlignmentAt
    (profile : Profile rowFive) (view : ActiveView rowFive) :=
  MissingAnalyticAlignment rowFive profile.tieredCapability
    profile.contextCapability profile.FiniteResistance profile.HarmonicZero
    profile.HarmonicLedgerMember profile.NonroutableTargetVisible
    view (boundaryAt rowFive view)

/-- Registration type at the exact predecessor view. -/
abbrev RegistrationAt
    (profile : Profile rowFive) (view : ActiveView rowFive) :=
  AlignmentRegistration rowFive profile.tieredCapability
    profile.contextCapability profile.FiniteResistance profile.HarmonicZero
    profile.HarmonicLedgerMember profile.NonroutableTargetVisible
    view (boundaryAt rowFive view)

end Profile

/-- Run both source-neutral CT generators exactly once in the prescribed order. -/
def generateRawCounted
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive) :
    Counted (profile.Raw view) :=
  (Hypostructure.CT13.generateCounted profile.tieredCapability view).bind
    fun ct13 =>
      (Hypostructure.CT7.generateCounted
        profile.contextCapability view).map fun ct7 =>
          RawTranscript.mk ct13 ct7

/-- Raw generation publishes exactly the checks retained by its two outputs. -/
@[simp] theorem generateRawCounted_checks
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive) :
    (generateRawCounted profile view).checks =
      (generateRawCounted profile view).value.checks := by
  unfold generateRawCounted RawTranscript.checks
  simp only [Counted.bind, Counted.map]
  rw [Hypostructure.CT13.generateCounted_checks,
    Hypostructure.CT7.generateCounted_checks_eq_value]

/-- The raw count is the actual CT13 count followed by the actual CT7 count. -/
theorem generateRawCounted_checks_eq_generators
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive) :
    (generateRawCounted profile view).checks =
      (Hypostructure.CT13.generateCounted
          profile.tieredCapability view).checks +
        (Hypostructure.CT7.generateCounted
          profile.contextCapability view).checks := by
  rfl

/-- Framework-owned successful first-match scan for one available alignment. -/
structure AlignmentSelection
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive)
    (raw : profile.Raw view) (alignment : profile.AlignmentAt view) where
  private mk ::
  execution : Hypostructure.Core.Finite.Search.Execution
    semanticTagEnumeration (alignment.relates raw)
  hasHit : execution.HasHit
  evidence : profile.Evidence view raw
    (execution.hitOfHasHit hasHit).value
  unique : forall tag, alignment.relates raw tag ->
    tag = (execution.hitOfHasHit hasHit).value

namespace AlignmentSelection

variable {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
variable {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
variable {profile : Profile rowFive} {view : ActiveView rowFive}
variable {raw : profile.Raw view} {alignment : profile.AlignmentAt view}

/-- Framework-selected semantic tag. -/
def tag (selection : AlignmentSelection profile view raw alignment) : SemanticTag :=
  (selection.execution.hitOfHasHit selection.hasHit).value

/-- Exact visible relation checks retained by the canonical scan execution. -/
def checks (selection : AlignmentSelection profile view raw alignment) : Nat :=
  Hypostructure.Core.Finite.Accounting.executionChecks selection.execution

/-- Any proved registered relation identifies the unique tag selected by the
canonical first-hit execution. -/
theorem tag_eq_of_relates
    (selection : AlignmentSelection profile view raw alignment)
    (tag : SemanticTag) (relates : alignment.relates raw tag) :
    selection.tag = tag :=
  (selection.unique tag relates).symm

/-- The exact relation work is the framework-owned prefix of the unique tag. -/
theorem checks_eq_prefix_of_relates
    (selection : AlignmentSelection profile view raw alignment)
    (tag : SemanticTag) (relates : alignment.relates raw tag) :
    selection.checks = tag.prefixChecks := by
  let hit := selection.execution.hitOfHasHit selection.hasHit
  have found : selection.execution.hit? = some hit :=
    selection.execution.hit?_eq_some_hitOfHasHit selection.hasHit
  have hitValue : hit.value = tag := by
    simpa [AlignmentSelection.tag, hit] using
        selection.tag_eq_of_relates tag relates
  have indexEq : hit.index = tag.index :=
    semanticTagEnumeration.unique_index
      (hitValue.trans tag.enumeration_get_index.symm)
  unfold checks SemanticTag.prefixChecks
  rw [Hypostructure.Core.Finite.Accounting.executionChecks_of_hit
    selection.execution hit found, indexEq]

end AlignmentSelection

/-- Run Core's canonical first-hit search over the fixed three semantic tags.
Completeness removes the miss branch; soundness constructs exact evidence and
functionality proves the selected relation is unique. -/
def scanAlignmentCounted
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive)
    (raw : profile.Raw view) (alignment : profile.AlignmentAt view) :
    Counted (AlignmentSelection profile view raw alignment) :=
  let scan := Hypostructure.Core.Finite.Accounting.countedRun
    semanticTagEnumeration (alignment.relates raw)
    (alignment.decidableRelates raw)
  have hasHit : scan.value.HasHit := by
    rw [Hypostructure.Core.Finite.Accounting.countedRun_value]
    apply Hypostructure.Core.Finite.Search.complete
    obtain ⟨tag, relates⟩ := alignment.complete raw
    exact ⟨tag, semanticTag_mem tag, relates⟩
  scan.map fun _execution =>
    {
      execution := scan.value
      hasHit := hasHit
      evidence := alignment.sound raw _
        (scan.value.hitOfHasHit hasHit).sound
      unique := fun tag relates =>
        alignment.functional raw tag _ relates
          (scan.value.hitOfHasHit hasHit).sound
    }

/-- The counted scan publishes the exact prefix retained in its execution. -/
@[simp] theorem scanAlignmentCounted_checks
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive)
    (raw : profile.Raw view) (alignment : profile.AlignmentAt view) :
    (scanAlignmentCounted profile view raw alignment).checks =
      (scanAlignmentCounted profile view raw alignment).value.checks := by
  rfl

/-- The actual first-match prefix never exceeds the fixed three-tag schedule. -/
theorem scanAlignmentCounted_checks_le_three
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive)
    (raw : profile.Raw view) (alignment : profile.AlignmentAt view) :
    (scanAlignmentCounted profile view raw alignment).checks <= 3 := by
  rw [scanAlignmentCounted_checks]
  change Hypostructure.Core.Finite.Accounting.executionChecks
    (scanAlignmentCounted profile view raw alignment).value.execution <= 3
  have bounded :=
    Hypostructure.Core.Finite.Accounting.executionChecks_le_card
      (scanAlignmentCounted profile view raw alignment).value.execution
  exact bounded.trans_eq semanticTagEnumeration_card

/-- Source-neutral interpretation of one exact raw transcript. The registration
is an index, so an inherited available contract is not copied into the output. -/
inductive Interpretation
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive)
    (raw : profile.Raw view) : profile.RegistrationAt view -> Type _ where
  | unaligned (missing : profile.MissingAlignmentAt view) :
      Interpretation profile view raw (.unavailable missing)
  | aligned {alignment : profile.AlignmentAt view}
      (selection : AlignmentSelection profile view raw alignment) :
      Interpretation profile view raw (.available alignment)

/-- Framework routing status exposed to row-6 successors. The two successful
analytic tags share the capacity-ready route while retaining their distinct
tag-indexed evidence in the interpretation. -/
inductive Disposition where
  | unaligned
  | capacityReady
  | targetVisibleHarmonic
  deriving DecidableEq, Repr

/-- Source semantic tags determine successor disposition only after an
analytic alignment has selected and justified the tag. -/
def SemanticTag.disposition : SemanticTag -> Disposition
  | .finiteResistanceHarmonicZero => .capacityReady
  | .finiteResistanceHarmonicClosed => .capacityReady
  | .targetVisibleHarmonic => .targetVisibleHarmonic

namespace Interpretation

variable {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
variable {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
variable {profile : Profile rowFive} {view : ActiveView rowFive}
variable {raw : profile.Raw view} {registration : profile.RegistrationAt view}

/-- Exact relation-scan prefix. Unavailable registration performs no scan. -/
def checks (interpretation : Interpretation profile view raw registration) : Nat :=
  match interpretation with
  | .unaligned _missing => 0
  | .aligned selection => selection.checks

/-- Unaligned transcripts remain open; aligned transcripts route according to
their framework-selected source semantic tag. -/
def disposition
    (interpretation : Interpretation profile view raw registration) :
    Disposition :=
  match interpretation with
  | .unaligned _missing => .unaligned
  | .aligned selection => selection.tag.disposition

/-- Observable semantic tag selected by an aligned execution. Unavailable
registrations expose `none`; callers cannot construct or choose this value. -/
def semanticTag?
    (interpretation : Interpretation profile view raw registration) :
    Option SemanticTag :=
  match interpretation with
  | .unaligned _missing => none
  | .aligned selection => some selection.tag

end Interpretation

/-- Interpret one raw transcript. Availability is read from the exact
predecessor; no caller supplies a tag, evidence value, or scan result. -/
def interpretCounted
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive)
    (raw : profile.Raw view) :
    Counted (Interpretation profile view raw
      (profile.alignmentRegistration.read view.previous view.proof)) :=
  match profile.alignmentRegistration.read view.previous view.proof with
  | .unavailable missing => Counted.pure (.unaligned missing)
  | .available alignment =>
      (scanAlignmentCounted profile view raw alignment).map fun selection =>
        .aligned selection

/-- Interpretation work is exactly the stored relation-scan prefix. -/
@[simp] theorem interpretCounted_checks
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive)
    (raw : profile.Raw view) :
    (interpretCounted profile view raw).checks =
      (interpretCounted profile view raw).value.checks := by
  unfold interpretCounted
  cases registered :
      profile.alignmentRegistration.read view.previous view.proof with
  | unavailable missing => rfl
  | available alignment =>
      exact scanAlignmentCounted_checks profile view raw alignment

/-- Interpretation performs at most the fixed three relation inspections. -/
theorem interpretCounted_checks_le_three
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive)
    (raw : profile.Raw view) :
    (interpretCounted profile view raw).checks <= 3 := by
  unfold interpretCounted
  cases registered :
      profile.alignmentRegistration.read view.previous view.proof with
  | unavailable missing => simp [Counted.pure]
  | available alignment =>
      simpa [Counted.map] using
        scanAlignmentCounted_checks_le_three profile view raw alignment

/-- An unavailable registration performs no relation checks. -/
theorem interpretCounted_checks_of_unavailable
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive)
    (raw : profile.Raw view) (missing : profile.MissingAlignmentAt view)
    (registered :
      profile.alignmentRegistration.read view.previous view.proof =
        .unavailable missing) :
    (interpretCounted profile view raw).checks = 0 := by
  unfold interpretCounted
  rw [registered]
  rfl

/-- An available registration pays exactly Core's first-match prefix. -/
theorem interpretCounted_checks_of_available
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive)
    (raw : profile.Raw view) (alignment : profile.AlignmentAt view)
    (registered :
      profile.alignmentRegistration.read view.previous view.proof =
        .available alignment) :
    (interpretCounted profile view raw).checks =
      (scanAlignmentCounted profile view raw alignment).checks := by
  unfold interpretCounted
  rw [registered]
  rfl

/-- Constructor-sealed row-6 output. The raw transcript occurs once, and the
interpretation is indexed by that same exact value and queried registration. -/
structure Generated
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive) where
  private mk ::
  raw : profile.Raw view
  interpretation : Interpretation profile view raw
    (profile.alignmentRegistration.read view.previous view.proof)

namespace Generated

variable {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
variable {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
variable {profile : Profile rowFive} {view : ActiveView rowFive}

/-- Exact raw-generation plus optional relation-scan checks retained by row 6. -/
def checks (generated : Generated profile view) : Nat :=
  generated.raw.checks + generated.interpretation.checks

/-- Framework-owned successor disposition of this exact generated output. -/
def disposition (generated : Generated profile view) : Disposition :=
  generated.interpretation.disposition

/-- Framework-selected semantic tag retained by the exact interpretation. -/
def semanticTag? (generated : Generated profile view) : Option SemanticTag :=
  generated.interpretation.semanticTag?

end Generated

/-- Total active execution: raw CT13/CT7 generation followed by optional
framework interpretation of that exact raw transcript. -/
def generateActiveCounted
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive) :
    Counted (Generated profile view) :=
  (generateRawCounted profile view).bind fun raw =>
    (interpretCounted profile view raw).map fun interpretation =>
      Generated.mk raw interpretation

/-- Deterministic active row-6 value. -/
def generateActive
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive) :
    Generated profile view :=
  (generateActiveCounted profile view).value

/-- Active work is exactly the checks retained by the generated output. -/
@[simp] theorem generateActiveCounted_checks
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive) :
    (generateActiveCounted profile view).checks =
      (generateActiveCounted profile view).value.checks := by
  unfold generateActiveCounted Generated.checks
  simp only [Counted.bind, Counted.map]
  rw [generateRawCounted_checks, interpretCounted_checks]

/-- Exact active work when no analytic alignment is registered. -/
theorem generateActiveCounted_checks_of_unavailable
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive)
    (missing : profile.MissingAlignmentAt view)
    (registered :
      profile.alignmentRegistration.read view.previous view.proof =
        .unavailable missing) :
    (generateActiveCounted profile view).checks =
      (Hypostructure.CT13.generateCounted
          profile.tieredCapability view).checks +
        (Hypostructure.CT7.generateCounted
          profile.contextCapability view).checks := by
  unfold generateActiveCounted
  simp only [Counted.bind, Counted.map]
  rw [interpretCounted_checks_of_unavailable profile view
    (generateRawCounted profile view).value missing registered]
  exact generateRawCounted_checks_eq_generators profile view

/-- Exact active work with an alignment is both CT generations plus the actual
Core first-match prefix for the exact generated raw transcript. -/
theorem generateActiveCounted_checks_of_available
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive)
    (alignment : profile.AlignmentAt view)
    (registered :
      profile.alignmentRegistration.read view.previous view.proof =
        .available alignment) :
    (generateActiveCounted profile view).checks =
      ((Hypostructure.CT13.generateCounted
          profile.tieredCapability view).checks +
        (Hypostructure.CT7.generateCounted
          profile.contextCapability view).checks) +
        (scanAlignmentCounted profile view
          (generateRawCounted profile view).value alignment).checks := by
  unfold generateActiveCounted
  simp only [Counted.bind, Counted.map]
  rw [interpretCounted_checks_of_available profile view
    (generateRawCounted profile view).value alignment registered]
  rw [generateRawCounted_checks_eq_generators]

/-- Worst-case active envelope: both exact CT schedules and at most three
alignment relation checks. -/
def activeEnvelope
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) : PolynomialCheckBudget (ActiveView rowFive) :=
  ((Hypostructure.CT13.generationBudget profile.tieredCapability).add
    (Hypostructure.CT7.generationBudget profile.contextCapability)).add
      (PolynomialCheckBudget.constant (fun _view => 0) 3)

/-- Actual active work lies below the complete raw-plus-alignment envelope. -/
theorem generateActiveCounted_checks_le_activeEnvelope
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (view : ActiveView rowFive) :
    (generateActiveCounted profile view).checks <=
      (activeEnvelope profile).checks view := by
  unfold generateActiveCounted
  simp only [Counted.bind, Counted.map]
  calc
    (generateRawCounted profile view).checks +
          (interpretCounted profile
            view (generateRawCounted profile view).value).checks <=
        (generateRawCounted profile view).checks + 3 :=
      Nat.add_le_add_left
        (interpretCounted_checks_le_three profile view
          (generateRawCounted profile view).value) _
    _ = (activeEnvelope profile).checks view := by
      rw [generateRawCounted_checks_eq_generators]
      rfl

/-- Exact dynamic active budget with coefficients inherited from the complete
framework envelope. -/
def activeGenerationBudget
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) : PolynomialCheckBudget (ActiveView rowFive) :=
  let envelope := activeEnvelope profile
  {
    size := envelope.size
    checks := fun view => (generateActiveCounted profile view).checks
    coefficient := envelope.coefficient
    degree := envelope.degree
    bounded := by
      intro view
      exact (generateActiveCounted_checks_le_activeEnvelope profile view).trans
        (envelope.bounded view)
  }

/-- Reindex exact active work to the literal row-5 predecessor. Inactive
predecessors have zero payload work. -/
def payloadBudget
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) : PolynomialCheckBudget (RowFiveStage rowFive) :=
  let activeBudget := activeGenerationBudget profile
  {
    size := fun previous =>
      match (rowFive.TargetVisibleFocus.select previous).value with
      | .isTrue proof =>
          activeBudget.size
            (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof)
      | .isFalse _absent => 0
    checks := fun previous =>
      match (rowFive.TargetVisibleFocus.select previous).value with
      | .isTrue proof =>
          activeBudget.checks
            (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof)
      | .isFalse _absent => 0
    coefficient := activeBudget.coefficient
    degree := activeBudget.degree
    bounded := by
      intro previous
      cases selected : (rowFive.TargetVisibleFocus.select previous).value with
      | isTrue proof =>
          exact activeBudget.bounded
            (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof)
      | isFalse _absent => simp
  }

private theorem generateActiveCounted_checks_eq_payloadBudget
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (previous : RowFiveStage rowFive)
    (proof : rowFive.TargetVisibleFocus.Active previous) :
    (generateActiveCounted profile
      (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof)).checks =
      (payloadBudget profile).checks previous := by
  unfold payloadBudget
  cases selected : (rowFive.TargetVisibleFocus.select previous).value with
  | isTrue selectedProof =>
      have equal : selectedProof = proof := Subsingleton.elim _ _
      cases equal
      simp [selected, activeGenerationBudget]
  | isFalse absent => exact (absent proof).elim

/-- Exact conditional payload appended by row 6. -/
abbrev Output
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (previous : RowFiveStage rowFive)
    (proof : rowFive.TargetVisibleFocus.Active previous) :=
  Generated profile
    (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof)

/-- Literal accumulated stage emitted by row 6. -/
abbrev Stage
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) :=
  Hypostructure.Core.Residual.Focus.Stage rowFive.TargetVisibleFocus
    (Output profile)

/-- Framework-owned focus inherited by row-6 successors. -/
abbrev Profile.SuccessorFocus
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) :=
  Hypostructure.Core.Residual.Focus.successor rowFive.TargetVisibleFocus
    (Output profile)

/-- Retrieve the exact row-6 output from the accumulated successor ledger. -/
def Profile.outputQuery
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) :
    Hypostructure.Core.Residual.Focus.ActiveQuery profile.SuccessorFocus
      fun stage active => Output profile stage.previous active :=
  Hypostructure.Core.Residual.Focus.ActiveQuery.latest

/-- Read only row 6's framework-owned successor disposition. -/
def Profile.dispositionQuery
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) :
    Hypostructure.Core.Residual.Focus.ActiveQuery profile.SuccessorFocus
      fun _stage _active => Disposition :=
  profile.outputQuery.map fun _stage _active generated =>
    generated.disposition

/-- Read the exact framework-selected semantic tag, if an alignment was
available, without inspecting the private interpretation constructors. -/
def Profile.semanticTagQuery
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) :
    Hypostructure.Core.Residual.Focus.ActiveQuery profile.SuccessorFocus
      fun _stage _active => Option SemanticTag :=
  profile.outputQuery.map fun _stage _active generated =>
    generated.semanticTag?

/-- Refine one exact framework-selected semantic tag. -/
def Profile.semanticTagRefinement
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (tag : SemanticTag) :
    Hypostructure.Core.Residual.Focus.Refinement profile.SuccessorFocus :=
  profile.semanticTagQuery.equalTo (some tag)

/-- Typed downstream focus for one exact semantic tag. -/
abbrev Profile.SemanticTagFocus
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (tag : SemanticTag) :=
  Hypostructure.Core.Residual.Focus.refine profile.SuccessorFocus
    (profile.semanticTagRefinement tag)

/-- Read the exact generated output together with its selected semantic tag. -/
def Profile.semanticTagOutputQuery
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (tag : SemanticTag) :
    Hypostructure.Core.Residual.Focus.ActiveQuery
      (profile.SemanticTagFocus tag) fun stage active =>
        { generated : Output profile stage.previous active.parent //
          generated.semanticTag? = some tag } :=
  profile.outputQuery.selectedTag
    (fun _stage _active generated => generated.semanticTag?) (some tag)

/-- Refine exactly the active unaligned residual. -/
def Profile.unalignedRefinement
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) :
    Hypostructure.Core.Residual.Focus.Refinement profile.SuccessorFocus :=
  profile.dispositionQuery.equalTo .unaligned

/-- Refine exactly the two aligned finite-resistance success tags. -/
def Profile.capacityReadyRefinement
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) :
    Hypostructure.Core.Residual.Focus.Refinement profile.SuccessorFocus :=
  profile.dispositionQuery.equalTo .capacityReady

/-- Refine exactly the aligned target-visible harmonic residual. -/
def Profile.targetVisibleHarmonicRefinement
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) :
    Hypostructure.Core.Residual.Focus.Refinement profile.SuccessorFocus :=
  profile.dispositionQuery.equalTo .targetVisibleHarmonic

/-- Typed focus for transcripts that still lack analytic alignment. -/
abbrev Profile.UnalignedFocus
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) :=
  Hypostructure.Core.Residual.Focus.refine profile.SuccessorFocus
    profile.unalignedRefinement

/-- The only row-6 focus admissible as a successful row-7 capacity input. -/
abbrev Profile.CapacityReadyFocus
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) :=
  Hypostructure.Core.Residual.Focus.refine profile.SuccessorFocus
    profile.capacityReadyRefinement

/-- Typed focus for the aligned target-visible harmonic residual. -/
abbrev Profile.TargetVisibleHarmonicFocus
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) :=
  Hypostructure.Core.Residual.Focus.refine profile.SuccessorFocus
    profile.targetVisibleHarmonicRefinement

/-- Read the exact unaligned output once together with its selected status. -/
def Profile.unalignedOutputQuery
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) :
    Hypostructure.Core.Residual.Focus.ActiveQuery profile.UnalignedFocus
      fun stage active =>
        { generated : Output profile stage.previous active.parent //
          generated.disposition = .unaligned } :=
  profile.outputQuery.selectedTag
    (fun _stage _active generated => generated.disposition) .unaligned

/-- Read one exact successful aligned output. Its interpretation retains which
of the two finite-resistance tags supplied the source-backed evidence. -/
def Profile.capacityReadyOutputQuery
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) :
    Hypostructure.Core.Residual.Focus.ActiveQuery profile.CapacityReadyFocus
      fun stage active =>
        { generated : Output profile stage.previous active.parent //
          generated.disposition = .capacityReady } :=
  profile.outputQuery.selectedTag
    (fun _stage _active generated => generated.disposition) .capacityReady

/-- Read the exact target-visible harmonic residual once with its selected
status proof. -/
def Profile.targetVisibleHarmonicOutputQuery
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) :
    Hypostructure.Core.Residual.Focus.ActiveQuery
      profile.TargetVisibleHarmonicFocus fun stage active =>
        { generated : Output profile stage.previous active.parent //
          generated.disposition = .targetVisibleHarmonic } :=
  profile.outputQuery.selectedTag
    (fun _stage _active generated => generated.disposition)
    .targetVisibleHarmonic

/-- The sole row-6 extension. Core owns focus routing and payload installation. -/
def run
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (previous : RowFiveStage rowFive) :
    Counted (Stage profile) :=
  Hypostructure.Core.Residual.Focus.runCountedPayload
    (Output := fun previous proof => Generated profile
      (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    rowFive.TargetVisibleFocus (payloadBudget profile) previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

/-- Row 6 retains the literal complete row-5 predecessor. -/
@[simp] theorem run_previous
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (previous : RowFiveStage rowFive) :
    (run profile previous).value.previous = previous := by
  unfold run
  exact Hypostructure.Core.Residual.Focus.runCountedPayload_previous
    (Output := fun previous proof => Generated profile
      (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    rowFive.TargetVisibleFocus (payloadBudget profile) previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

/-- Exact active work is focus selection plus the actual dynamic row-6 work. -/
theorem run_checks_of_active
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (previous : RowFiveStage rowFive)
    (active : rowFive.TargetVisibleFocus.Active previous) :
    (run profile previous).checks =
      rowFive.TargetVisibleFocus.selectionBudget.checks previous +
        (generateActiveCounted profile
          (Hypostructure.Core.Residual.Focus.ActiveView.of
            previous active)).checks := by
  have coreExact :=
    Hypostructure.Core.Residual.Focus.runCountedPayload_checks_of_active
      (Output := fun previous proof => Generated profile
        (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
      rowFive.TargetVisibleFocus (payloadBudget profile) previous
      (fun proof _selectionChecks _selectionExact =>
        generateActiveCounted profile
          (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
      (fun proof _selectionChecks _selectionExact =>
        generateActiveCounted_checks_eq_payloadBudget profile previous proof)
      active
  unfold run
  rw [coreExact]
  unfold PolynomialCheckBudget.add
  rw [generateActiveCounted_checks_eq_payloadBudget profile previous active]

/-- On an active unaligned predecessor, exact work is focus selection plus the
two CT generations; no relation check is performed. -/
theorem run_checks_of_active_unavailable
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (previous : RowFiveStage rowFive)
    (active : rowFive.TargetVisibleFocus.Active previous)
    (missing : profile.MissingAlignmentAt
      (Hypostructure.Core.Residual.Focus.ActiveView.of previous active))
    (registered :
      profile.alignmentRegistration.read previous active =
        .unavailable missing) :
    (run profile previous).checks =
      rowFive.TargetVisibleFocus.selectionBudget.checks previous +
        ((Hypostructure.CT13.generateCounted profile.tieredCapability
          (Hypostructure.Core.Residual.Focus.ActiveView.of
            previous active)).checks +
        (Hypostructure.CT7.generateCounted profile.contextCapability
        (Hypostructure.Core.Residual.Focus.ActiveView.of
            previous active)).checks) := by
  rw [run_checks_of_active profile previous active]
  rw [generateActiveCounted_checks_of_unavailable profile
    (Hypostructure.Core.Residual.Focus.ActiveView.of previous active)
    missing registered]

/-- On an active aligned predecessor, exact work includes the actual relation
first-match prefix for the exact generated raw transcript. -/
theorem run_checks_of_active_available
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (previous : RowFiveStage rowFive)
    (active : rowFive.TargetVisibleFocus.Active previous)
    (alignment : profile.AlignmentAt
      (Hypostructure.Core.Residual.Focus.ActiveView.of previous active))
    (registered :
      profile.alignmentRegistration.read previous active =
        .available alignment) :
    (run profile previous).checks =
      rowFive.TargetVisibleFocus.selectionBudget.checks previous +
        (((Hypostructure.CT13.generateCounted profile.tieredCapability
          (Hypostructure.Core.Residual.Focus.ActiveView.of
            previous active)).checks +
        (Hypostructure.CT7.generateCounted profile.contextCapability
          (Hypostructure.Core.Residual.Focus.ActiveView.of
            previous active)).checks) +
        (scanAlignmentCounted profile
          (Hypostructure.Core.Residual.Focus.ActiveView.of previous active)
          (generateRawCounted profile
            (Hypostructure.Core.Residual.Focus.ActiveView.of
              previous active)).value alignment).checks) := by
  rw [run_checks_of_active profile previous active]
  rw [generateActiveCounted_checks_of_available profile
    (Hypostructure.Core.Residual.Focus.ActiveView.of previous active)
    alignment registered]

/-- Inactive row-5 siblings pay only the exact target-visible focus selector. -/
theorem run_checks_of_inactive
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (previous : RowFiveStage rowFive)
    (inactive : Not (rowFive.TargetVisibleFocus.Active previous)) :
    (run profile previous).checks =
      rowFive.TargetVisibleFocus.selectionBudget.checks previous := by
  exact Hypostructure.Core.Residual.Focus.runCountedPayload_checks_of_inactive
    (Output := fun previous proof => Generated profile
      (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    rowFive.TargetVisibleFocus (payloadBudget profile) previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)
    inactive

/-- Every row-6 execution satisfies the composed focus-plus-payload bound. -/
theorem run_checks_bounded
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {rowFive : DirectedExhaustiveness.Profile Previous focus Potential Current}
    (profile : Profile rowFive) (previous : RowFiveStage rowFive) :
    (run profile previous).checks <=
      (rowFive.TargetVisibleFocus.selectionBudget.add
        (payloadBudget profile)).coefficient *
      ((rowFive.TargetVisibleFocus.selectionBudget.add
        (payloadBudget profile)).size previous + 1) ^
      (rowFive.TargetVisibleFocus.selectionBudget.add
        (payloadBudget profile)).degree := by
  exact Hypostructure.Core.Residual.Focus.runCountedPayload_checks_bounded
    (Output := fun previous proof => Generated profile
      (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    rowFive.TargetVisibleFocus (payloadBudget profile) previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile
        (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted_checks_eq_payloadBudget profile previous proof)

end Hypostructure.PDE.FastTrack.DefectRouting

#print axioms Hypostructure.PDE.FastTrack.DefectRouting.run
#print axioms Hypostructure.PDE.FastTrack.DefectRouting.run_checks_bounded
