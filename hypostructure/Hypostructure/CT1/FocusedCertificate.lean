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

/-- Execute proof-carrying CT1 only where the predecessor focus is active. -/
noncomputable def Encoding.run {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (previous : Previous) : Stage encoding :=
  Focus.run profile previous fun _active =>
    _root_.Hypostructure.CT1.CertificateEncoding.routePublicTarget
      encoding.total previous

@[simp] theorem run_previous {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (previous : Previous) : (Encoding.run encoding previous).previous = previous :=
  rfl

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

/-- Exact focused successor after C1 has been closed. -/
abbrev Encoding.AvoidingStage {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget) :=
  Focus.Stage encoding.SuccessorProfile (AvoidingEvidence encoding)

/-- Close every active C1 outcome using inherited target avoidance and retain
only CT1's exact avoiding evidence. -/
def Encoding.closeC1ContinueAvoiding {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (stage : Stage encoding)
    (targetImpossible : Focus.ActiveQuery encoding.SuccessorProfile
      fun current active => Not (PublicTarget current.previous active)) :
    encoding.AvoidingStage :=
  Focus.run encoding.SuccessorProfile stage fun active =>
    let route := encoding.routeQuery.read stage active
    let impossibleTotal : Not (TotalTarget PublicTarget stage.previous) := by
      intro total
      exact targetImpossible.read stage active (target_of_total total)
    { terminal_eq := route.terminal_avoiding_of_not_target impossibleTotal }

@[simp] theorem closeC1ContinueAvoiding_previous {Previous : Type uPrevious}
    {profile : Focus.Profile Previous}
    {PublicTarget : (previous : Previous) -> profile.Active previous -> Prop}
    (encoding : Encoding.{uPrevious, uCode} profile PublicTarget)
    (stage : Stage encoding)
    (targetImpossible : Focus.ActiveQuery encoding.SuccessorProfile
      fun current active => Not (PublicTarget current.previous active)) :
    (Encoding.closeC1ContinueAvoiding encoding stage targetImpossible).previous =
      stage :=
  rfl

end Hypostructure.CT1.FocusedCertificateEncoding
