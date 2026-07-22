import Hypostructure.CT1.Automation
import Hypostructure.Graph.RootedReturn

/-!
# Graph adapter for CT1 cycle certificates

The adapter gives CT1 the existing graph `CycleCertificate` as its candidate
type.  It introduces no graph search and no theorem-specific constants.
-/

namespace Hypostructure.Graph.CT1

universe uPrevious uVertex

/-- CT1 realization semantics for proof-carrying graph cycle certificates. -/
def cycleSpec {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (LengthOK : Nat -> Prop) :
    _root_.Hypostructure.CT1.Spec Previous where
  Candidate := fun previous =>
    CycleCertificate (object.read previous) LengthOK
  Realizes := fun _previous _certificate => True

/-- Build the executable CT1 capability while Graph discharges the trivial
decision for a proof-carrying cycle certificate. -/
def cycleCapability {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (LengthOK : Nat -> Prop)
    (schedule : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration
        (CycleCertificate (object.read previous) LengthOK))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      (schedule.read previous).card <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT1.Capability (cycleSpec object LengthOK) where
  schedule := schedule
  realizesDecidable := by
    intro _previous _certificate
    exact .isTrue trivial
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

/-- A scheduled cycle certificate proves the public graph target. -/
theorem publicTarget_of_target {Previous : Type uPrevious}
    {object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex}}
    {LengthOK : Nat -> Prop} {previous : Previous}
    {schedule : Core.Finite.Enumeration
      (CycleCertificate (object.read previous) LengthOK)}
    (target : _root_.Hypostructure.CT1.Target
      (cycleSpec object LengthOK) previous schedule) :
    HasCycleWithLength LengthOK (object.read previous) := by
  rcases target with ⟨certificate, _member, _realizes⟩
  exact ⟨certificate⟩

/-- Exact schedule completeness upgrades CT1's scheduled target to the public
cycle target in both directions. -/
def cycleTargetBridge {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (LengthOK : Nat -> Prop)
    (capability : _root_.Hypostructure.CT1.Capability
      (cycleSpec object LengthOK))
    (complete : forall previous,
      HasCycleWithLength LengthOK (object.read previous) ->
        Exists fun certificate =>
          certificate ∈ (capability.scheduleAt previous).values) :
    _root_.Hypostructure.CT1.TargetBridge (cycleSpec object LengthOK) capability
      (fun previous => HasCycleWithLength LengthOK (object.read previous)) where
  equivalent := by
    intro previous
    constructor
    · intro target
      obtain ⟨certificate, member⟩ := complete previous target
      exact ⟨certificate, member, trivial⟩
    · exact publicTarget_of_target

/-- The corresponding public graph target uses the existing isomorphism
interface; CT1 does not define another representation semantics. -/
def cycleInterface (LengthOK : Nat -> Prop) :
    TargetInterface (HasCycleWithLength LengthOK) :=
  cycleTargetInterface LengthOK

/-- Certificate-mode CT1 encoding whose code is one accepted rooted return.
The graph layer supplies only the rooted-return/cycle semantic dictionary; CT1
owns target branching, validation, ledger extension, tracing, and work. -/
def rootedReturnEncoding {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (LengthOK : Nat -> Prop)
    (algebra : RootedReturnTargetAlgebra LengthOK) :
    _root_.Hypostructure.CT1.CertificateEncoding Previous
      (fun previous => HasCycleWithLength LengthOK (object.read previous)) where
  Code := fun previous => algebra.RootedReturn (object.read previous)
  Accepts := fun _previous _certificate => True
  encode := by
    intro previous target
    obtain ⟨certificate⟩ :=
      (algebra.target_iff_hasRootedReturn (object.read previous)).mp target
    exact ⟨certificate, trivial⟩
  decode := by
    intro previous certificate _accepted
    exact (algebra.target_iff_hasRootedReturn (object.read previous)).mpr
      ⟨certificate⟩
  acceptsDecidable := fun _previous _certificate => .isTrue trivial

/-- Execute rooted-return CT1 from the literal accumulated predecessor. -/
noncomputable def executeRootedReturn {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (LengthOK : Nat -> Prop)
    (algebra : RootedReturnTargetAlgebra LengthOK) (previous : Previous) :
    _root_.Hypostructure.CT1.CertificateEncoding.ExecutionResult
      (rootedReturnEncoding object LengthOK algebra) :=
  _root_.Hypostructure.CT1.executePublicTarget
    (rootedReturnEncoding object LengthOK algebra) previous

/-! ## Rooted returns on a focused branch -/

/-- Focused rooted-return encoding.  The selected graph is read only under
Core's activity proof, while CT1 owns certificate branching and validation. -/
def focusedRootedReturnEncoding {Previous : Type uPrevious}
    (profile : Core.Residual.Focus.Profile Previous)
    (object : Core.Residual.Focus.ActiveQuery profile fun _previous _active =>
      FiniteObject.{uVertex})
    (LengthOK : Nat -> Prop)
    (algebra : RootedReturnTargetAlgebra LengthOK) :
    _root_.Hypostructure.CT1.FocusedCertificateEncoding.Encoding profile
      (fun previous active =>
        HasCycleWithLength LengthOK (object.read previous active)) where
  Code := fun previous active =>
    algebra.RootedReturn (object.read previous active)
  Accepts := fun _previous _active _certificate => True
  encode := by
    intro previous active target
    obtain ⟨certificate⟩ :=
      (algebra.target_iff_hasRootedReturn
        (object.read previous active)).mp target
    exact ⟨certificate, trivial⟩
  decode := by
    intro previous active certificate _accepted
    exact (algebra.target_iff_hasRootedReturn
      (object.read previous active)).mpr ⟨certificate⟩
  acceptsDecidable := fun _previous _active _certificate => .isTrue trivial

/-- Counted rooted-return CT1 execution on the exact focused graph branch. -/
noncomputable def executeFocusedRootedReturnCounted {Previous : Type uPrevious}
    (profile : Core.Residual.Focus.Profile Previous)
    (object : Core.Residual.Focus.ActiveQuery profile fun _previous _active =>
      FiniteObject.{uVertex})
    (LengthOK : Nat -> Prop)
    (algebra : RootedReturnTargetAlgebra LengthOK) (previous : Previous) :
    Core.Counted
      (_root_.Hypostructure.CT1.FocusedCertificateEncoding.Stage
        (focusedRootedReturnEncoding profile object LengthOK algebra)) :=
  (focusedRootedReturnEncoding profile object LengthOK algebra).runCounted previous

/-- Public stage projection of the counted focused rooted-return execution. -/
noncomputable def executeFocusedRootedReturn {Previous : Type uPrevious}
    (profile : Core.Residual.Focus.Profile Previous)
    (object : Core.Residual.Focus.ActiveQuery profile fun _previous _active =>
      FiniteObject.{uVertex})
    (LengthOK : Nat -> Prop)
    (algebra : RootedReturnTargetAlgebra LengthOK) (previous : Previous) :
    _root_.Hypostructure.CT1.FocusedCertificateEncoding.Stage
      (focusedRootedReturnEncoding profile object LengthOK algebra) :=
  (executeFocusedRootedReturnCounted profile object LengthOK algebra previous).value

end Hypostructure.Graph.CT1
