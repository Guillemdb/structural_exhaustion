import Hypostructure.CT1.Certificate
import Hypostructure.Core.Residual.Focus

/-!
# CT1 certificates on a focused proof branch

Applications describe a target and its certificate only where a Core focus is
active. CT1 totalizes that family internally, runs on the focused arm, and
adds no CT1 payload to inactive siblings.
-/

namespace Hypostructure.CT1.FocusedCertificateEncoding

open Hypostructure.Core.Residual

universe uPrevious uCode

/-- Proof-carrying CT1 data defined only on one active proof branch. -/
structure Encoding {Previous : Type uPrevious}
    (profile : Focus.Profile Previous)
    (PublicTarget : (previous : Previous) -> profile.Active previous -> Prop) where
  Code : (previous : Previous) -> profile.Active previous -> Type uCode
  Accepts : (previous : Previous) -> (active : profile.Active previous) ->
    Code previous active -> Prop
  encode : forall {previous active}, PublicTarget previous active ->
    Exists fun code => Accepts previous active code
  decode : forall {previous active code}, Accepts previous active code ->
    PublicTarget previous active
  acceptsDecidable : (previous : Previous) ->
    (active : profile.Active previous) -> (code : Code previous active) ->
    Decidable (Accepts previous active code)

/-- Framework packing of an activity proof and its dependent code. -/
structure PackedCode {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (previous : Previous) where
  active : profile.Active previous
  code : encoding.Code previous active

/-- Internal existential target used to reuse the ordinary CT1 certificate
machine without inventing an application carrier. -/
def TotalTarget {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    (PublicTarget : (previous : Previous) -> profile.Active previous -> Prop)
    (previous : Previous) : Prop :=
  Exists fun active : profile.Active previous => PublicTarget previous active

/-- Totalize a focused encoding inside CT1. -/
def Encoding.total {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget) :
    _root_.Hypostructure.CT1.CertificateEncoding Previous
      (TotalTarget PublicTarget) where
  Code := PackedCode encoding
  Accepts := fun previous code =>
    encoding.Accepts previous code.active code.code
  encode := by
    intro previous target
    obtain ⟨active, target⟩ := target
    obtain ⟨code, accepted⟩ := encoding.encode target
    let packed : PackedCode encoding previous :=
      { active := active, code := code }
    refine ⟨packed, ?_⟩
    exact accepted
  decode := by
    intro previous code accepted
    exact ⟨code.active, encoding.decode accepted⟩
  acceptsDecidable := fun previous code =>
    encoding.acceptsDecidable previous code.active code.code

/-- CT1's generated route on one active predecessor. -/
abbrev Output {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (previous : Previous) (_active : profile.Active previous) :=
  _root_.Hypostructure.CT1.CertificateEncoding.Route encoding.total previous

/-- Exact accumulated stage after focused CT1 execution. -/
abbrev Stage {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget) :=
  Focus.Stage profile (Output encoding)

/-- The inherited focus after CT1 appends its conditional output. -/
abbrev Encoding.SuccessorProfile {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget) :=
  Focus.successor profile (Output encoding)

/-- Retrieve the exact generated CT1 route on the active branch. -/
def Encoding.routeQuery {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget) :
    Focus.ActiveQuery encoding.SuccessorProfile fun stage active =>
      Output encoding stage.previous active :=
  Focus.ActiveQuery.latest

/-- Exact CT1 validation schedule on one predecessor.  The successful route
performs one primitive validation and the avoiding route performs none. -/
noncomputable def Encoding.validationBudget {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    : Core.PolynomialCheckBudget Previous where
  size := fun _previous => 0
  checks := fun previous =>
    (_root_.Hypostructure.CT1.CertificateEncoding.routePublicTarget
      encoding.total previous).checks
  coefficient := 1
  degree := 0
  bounded := by
    intro previous
    rw [(_root_.Hypostructure.CT1.CertificateEncoding.routePublicTarget
      encoding.total previous).checks_eq_terminal]
    cases (_root_.Hypostructure.CT1.CertificateEncoding.routePublicTarget
      encoding.total previous).terminal <;> simp

/-- Complete focused CT1 budget: one inherited branch selection followed, on
the active branch only, by certificate validation. -/
noncomputable def Encoding.workBudget {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget) :
    Core.PolynomialCheckBudget Previous :=
  profile.selectionBudget.add encoding.validationBudget

/-- One CT1 route paired with its exact local validation count. -/
noncomputable def Encoding.routeCounted {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (previous : Previous) :
    Core.Counted
      (_root_.Hypostructure.CT1.CertificateEncoding.Route
        encoding.total previous) :=
  let route :=
    _root_.Hypostructure.CT1.CertificateEncoding.routePublicTarget
      encoding.total previous
  ⟨route, route.checks⟩

@[simp] theorem Encoding.routeCounted_checks {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (previous : Previous) :
    (encoding.routeCounted previous).checks =
      encoding.validationBudget.checks previous :=
  rfl

/-- Dependent active callback used by Core's counted focus executor. -/
noncomputable def Encoding.activeRoute {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (previous : Previous) (active : profile.Active previous)
    (_selectionChecks : Nat)
    (_exact : _selectionChecks = profile.selectionBudget.checks previous) :
    Core.Counted (Output encoding previous active) :=
  encoding.routeCounted previous

@[simp] theorem Encoding.activeRoute_checks {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (previous : Previous) (active : profile.Active previous)
    (selectionChecks : Nat)
    (exact : selectionChecks = profile.selectionBudget.checks previous) :
    (encoding.activeRoute previous active selectionChecks exact).checks =
      encoding.validationBudget.checks previous :=
  encoding.routeCounted_checks previous

/-- Execute proof-carrying CT1 with exact selector-plus-validation work. -/
noncomputable def Encoding.runCounted {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (previous : Previous) : Core.Counted (Stage encoding) :=
  Focus.runCountedPayload profile encoding.validationBudget previous
    (encoding.activeRoute previous) (encoding.activeRoute_checks previous)

/-- Public stage projection of the complete counted CT1 execution. -/
noncomputable def Encoding.run {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (previous : Previous) : Stage encoding :=
  (encoding.runCounted previous).value

theorem Encoding.runCounted_checks_of_active {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (previous : Previous) (active : profile.Active previous) :
    (encoding.runCounted previous).checks =
      encoding.workBudget.checks previous :=
  by
    simpa [Encoding.runCounted, Encoding.workBudget] using
      Focus.runCountedPayload_checks_of_active profile
        encoding.validationBudget previous
        (encoding.activeRoute previous) (encoding.activeRoute_checks previous)
        active

theorem Encoding.runCounted_checks_of_inactive {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (previous : Previous) (inactive : Not (profile.Active previous)) :
    (encoding.runCounted previous).checks =
      profile.selectionBudget.checks previous :=
  by
    simpa [Encoding.runCounted] using
      Focus.runCountedPayload_checks_of_inactive profile
        encoding.validationBudget previous
        (encoding.activeRoute previous) (encoding.activeRoute_checks previous)
        inactive

theorem Encoding.runCounted_checks_bounded {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (previous : Previous) :
    (encoding.runCounted previous).checks <=
      encoding.workBudget.coefficient *
        (encoding.workBudget.size previous + 1) ^
          encoding.workBudget.degree :=
  by
    simpa [Encoding.runCounted, Encoding.workBudget] using
      Focus.runCountedPayload_checks_bounded profile
        encoding.validationBudget previous
        (encoding.activeRoute previous) (encoding.activeRoute_checks previous)

/-- Predicate-form work theorem for focused CT1 execution. -/
theorem Encoding.runCounted_work_within {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (previous : Previous) :
    encoding.workBudget.Within previous
      (encoding.runCounted previous).checks :=
  encoding.runCounted_checks_bounded previous

@[simp] theorem run_previous {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (previous : Previous) : (Encoding.run encoding previous).previous = previous :=
  by
    simp [Encoding.run, Encoding.runCounted,
      Focus.runCountedPayload_previous]

/-- Transport a totalized target to the current activity proof. -/
theorem target_of_total {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    {previous : Previous} {active : profile.Active previous}
    (target : TotalTarget PublicTarget previous) :
    PublicTarget previous active := by
  obtain ⟨selected, target⟩ := target
  have equal : selected = active := Subsingleton.elim _ _
  cases equal
  exact target

/-- One local target realizes CT1's internal totalized target. -/
theorem total_of_target {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    {previous : Previous} {active : profile.Active previous}
    (target : PublicTarget previous active) :
    TotalTarget PublicTarget previous :=
  ⟨active, target⟩

/-- A C1 route yields the exact local target. -/
theorem target_of_c1 {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    {encoding : Encoding.{uPrevious, uCode} profile PublicTarget}
    {previous : Previous} {active : profile.Active previous}
    (route : Output encoding previous active)
    (isC1 : route.terminal = .c1) : PublicTarget previous active := by
  have total : TotalTarget PublicTarget previous := by
    simpa [_root_.Hypostructure.CT1.CertificateEncoding.OutcomeClaim, isC1]
      using route.verified
  exact target_of_total total

/-- An avoiding route excludes the exact local target. -/
theorem avoids_of_avoiding {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    {encoding : Encoding.{uPrevious, uCode} profile PublicTarget}
    {previous : Previous} {active : profile.Active previous}
    (route : Output encoding previous active)
    (isAvoiding : route.terminal = .avoiding) :
    Not (PublicTarget previous active) := by
  intro target
  have avoidsTotal : Not (TotalTarget PublicTarget previous) := by
    simpa [_root_.Hypostructure.CT1.CertificateEncoding.OutcomeClaim,
      isAvoiding] using route.verified
  exact avoidsTotal (total_of_target target)

/-- Framework-owned evidence after the active C1 terminal is contradicted. -/
structure AvoidingEvidence {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (stage : Stage encoding) (active : encoding.SuccessorProfile.Active stage) where
  private mk ::
  terminal_eq : (encoding.routeQuery.read stage active).terminal =
    _root_.Hypostructure.CT1.Terminal.avoiding

namespace AvoidingEvidence

/-- Recover local target avoidance from the retained route. -/
theorem avoids {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    {encoding : Encoding.{uPrevious, uCode} profile PublicTarget}
    {stage : Stage encoding} {active : encoding.SuccessorProfile.Active stage}
    (evidence : AvoidingEvidence encoding stage active) :
    Not (PublicTarget stage.previous active) :=
  avoids_of_avoiding (encoding.routeQuery.read stage active)
    evidence.terminal_eq

/-- The retained avoiding route performs zero certificate checks. -/
theorem checks_eq_zero {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    {encoding : Encoding.{uPrevious, uCode} profile PublicTarget}
    {stage : Stage encoding} {active : encoding.SuccessorProfile.Active stage}
    (evidence : AvoidingEvidence encoding stage active) :
    (encoding.routeQuery.read stage active).checks = 0 := by
  rw [(encoding.routeQuery.read stage active).checks_eq_terminal,
    evidence.terminal_eq]

end AvoidingEvidence

/-- Framework-owned evidence after the avoiding terminal is contradicted. -/
structure C1Evidence {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (stage : Stage encoding) (active : encoding.SuccessorProfile.Active stage) where
  private mk ::
  terminal_eq : (encoding.routeQuery.read stage active).terminal =
    _root_.Hypostructure.CT1.Terminal.c1

namespace C1Evidence

theorem target {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    {encoding : Encoding.{uPrevious, uCode} profile PublicTarget}
    {stage : Stage encoding} {active : encoding.SuccessorProfile.Active stage}
    (evidence : C1Evidence encoding stage active) :
    PublicTarget stage.previous active :=
  target_of_c1 (encoding.routeQuery.read stage active) evidence.terminal_eq

end C1Evidence

/-- Exact focused successor after the avoiding terminal has been closed. -/
abbrev Encoding.C1Stage {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget) :=
  Focus.Stage encoding.SuccessorProfile (C1Evidence encoding)

/-- Focus inherited after CT1 has closed the avoiding branch and retained C1. -/
abbrev Encoding.C1Profile {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget) :=
  Focus.successor encoding.SuccessorProfile (C1Evidence encoding)

/-- Close every avoiding route using a predecessor-owned proof of the public
target. Core owns focus selection and the ledger extension. -/
def Encoding.closeAvoidingContinueC1Counted {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (stage : Stage encoding)
    (targetPossible : Focus.ActiveQuery encoding.SuccessorProfile
      fun current active => PublicTarget current.previous active) :
    Core.Counted encoding.C1Stage :=
  Focus.runCounted encoding.SuccessorProfile
    (Output := C1Evidence encoding) stage fun active _checks _exact =>
    let route := encoding.routeQuery.read stage active
    have notAvoiding : route.terminal ≠ _root_.Hypostructure.CT1.Terminal.avoiding := by
      intro avoiding
      exact (avoids_of_avoiding route avoiding)
        (targetPossible.read stage active)
    { terminal_eq := by
        cases terminal : route.terminal with
        | c1 => rfl
        | avoiding => exact (notAvoiding terminal).elim }

def Encoding.closeAvoidingContinueC1 {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (stage : Stage encoding)
    (targetPossible : Focus.ActiveQuery encoding.SuccessorProfile
      fun current active => PublicTarget current.previous active) :
    encoding.C1Stage :=
  (encoding.closeAvoidingContinueC1Counted stage targetPossible).value

@[simp] theorem Encoding.closeAvoidingContinueC1_previous {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (stage : Stage encoding)
    (targetPossible : Focus.ActiveQuery encoding.SuccessorProfile
      fun current active => PublicTarget current.previous active) :
    (encoding.closeAvoidingContinueC1 stage targetPossible).previous = stage := by
  simp [Encoding.closeAvoidingContinueC1,
    Encoding.closeAvoidingContinueC1Counted,
    Focus.runCounted_previous]

/-- Exact focused successor after C1 has been closed. -/
abbrev Encoding.AvoidingStage {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget) :=
  Focus.Stage encoding.SuccessorProfile (AvoidingEvidence encoding)

/-- Focus inherited after CT1 has closed the C1 outcome and retained the
avoiding residual. -/
abbrev Encoding.AvoidingProfile {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget) :=
  Focus.successor encoding.SuccessorProfile (AvoidingEvidence encoding)

/-- Retrieve CT1's exact avoiding evidence from the newest avoiding
continuation ledger entry. -/
def Encoding.avoidingEvidenceQuery {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget) :
    Focus.ActiveQuery encoding.AvoidingProfile fun stage active =>
      AvoidingEvidence encoding stage.previous active :=
  Focus.ActiveQuery.latest

/-- Counted closure of every active C1 outcome using inherited target
avoidance. Core owns the successor-focus selection and CT1 retains only its
exact avoiding evidence. -/
def Encoding.closeC1ContinueAvoidingCounted {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (stage : Stage encoding)
    (targetImpossible : Focus.ActiveQuery encoding.SuccessorProfile
      fun current active => Not (PublicTarget current.previous active)) :
    Core.Counted encoding.AvoidingStage :=
  Focus.runCounted encoding.SuccessorProfile
    (Output := AvoidingEvidence encoding) stage fun active _checks _exact =>
    let route := encoding.routeQuery.read stage active
    let impossibleTotal : Not (TotalTarget PublicTarget stage.previous) := by
      intro total
      exact targetImpossible.read stage active (target_of_total total)
    { terminal_eq := route.terminal_avoiding_of_not_target impossibleTotal }

/-- Public stage projection of the counted C1 closure. -/
def Encoding.closeC1ContinueAvoiding {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (stage : Stage encoding)
    (targetImpossible : Focus.ActiveQuery encoding.SuccessorProfile
      fun current active => Not (PublicTarget current.previous active)) :
    encoding.AvoidingStage :=
  (encoding.closeC1ContinueAvoidingCounted stage targetImpossible).value

@[simp] theorem Encoding.closeC1ContinueAvoidingCounted_checks
    {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (stage : Stage encoding)
    (targetImpossible : Focus.ActiveQuery encoding.SuccessorProfile
      fun current active => Not (PublicTarget current.previous active)) :
    (encoding.closeC1ContinueAvoidingCounted stage targetImpossible).checks =
      encoding.SuccessorProfile.selectionBudget.checks stage := by
  rw [Encoding.closeC1ContinueAvoidingCounted, Focus.runCounted_checks]

theorem Encoding.closeC1ContinueAvoidingCounted_checks_bounded
    {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (stage : Stage encoding)
    (targetImpossible : Focus.ActiveQuery encoding.SuccessorProfile
      fun current active => Not (PublicTarget current.previous active)) :
    (encoding.closeC1ContinueAvoidingCounted stage targetImpossible).checks <=
      encoding.SuccessorProfile.selectionBudget.coefficient *
        (encoding.SuccessorProfile.selectionBudget.size stage + 1) ^
          encoding.SuccessorProfile.selectionBudget.degree :=
  by
    rw [encoding.closeC1ContinueAvoidingCounted_checks stage targetImpossible]
    exact encoding.SuccessorProfile.selectionBudget.bounded stage

/-- Predicate-form work theorem for the avoiding continuation. -/
theorem Encoding.closeC1ContinueAvoidingCounted_work_within
    {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (stage : Stage encoding)
    (targetImpossible : Focus.ActiveQuery encoding.SuccessorProfile
      fun current active => Not (PublicTarget current.previous active)) :
    encoding.SuccessorProfile.selectionBudget.Within stage
      (encoding.closeC1ContinueAvoidingCounted stage targetImpossible).checks :=
  encoding.closeC1ContinueAvoidingCounted_checks_bounded stage targetImpossible

@[simp] theorem closeC1ContinueAvoiding_previous {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (stage : Stage encoding)
    (targetImpossible : Focus.ActiveQuery encoding.SuccessorProfile
      fun current active => Not (PublicTarget current.previous active)) :
    (Encoding.closeC1ContinueAvoiding encoding stage targetImpossible).previous =
      stage :=
  by
    simp [Encoding.closeC1ContinueAvoiding,
      Encoding.closeC1ContinueAvoidingCounted,
      Focus.runCounted_previous]

end Hypostructure.CT1.FocusedCertificateEncoding
