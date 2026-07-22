import Hypostructure.Core.Metadata
import Hypostructure.PDE.FastTrack.Signature
import Hypostructure.PDE.LocalTail
import Hypostructure.PDE.NavierStokes

/-!
# Represented 2D Navier--Stokes local/tail packet

This standalone packet exercises only declarations already exposed by the PDE
and Core APIs.  It registers the zero classical Navier--Stokes field on a
work/core cylinder, registers a velocity observable and target modulo pressure
gauge, and derives an exact additive split of the pressure into its part on the
work window and its complementary tail.

The pressure split is algebraic.  This file supplies no Calderon--Zygmund
estimate, harmonic-tail theorem, compactness theorem, retained-obstruction
transport, or regularity closure.  No imported analytic contract enters the
packet.
-/

namespace HypostructurePDEExamples.RepresentedNS2DLocalTailPacket

open Hypostructure
open Hypostructure.PDE
open Hypostructure.PDE.NavierStokes

noncomputable section

/-! ## Represented equation registration -/

def origin : Spacetime := (0, 0)

def workWindow : Window where
  center := origin
  radius := 1
  radius_pos := by norm_num

abbrev coreWindow : Window := workWindow.core

theorem core_nested_work : Window.Nested coreWindow workWindow :=
  Window.core_nested workWindow

theorem zero_represented_on_work_window :
    RepresentedClassicalOn (zeroField 1) workWindow.region := by
  refine ⟨zeroField 1, gaugeEquivalent_refl _, ?_⟩
  exact (zeroField_classical 1 (by norm_num)).mono (by
    intro point member
    simp [zeroField])

def zeroEquationState : EquationState representedEquation workWindow where
  object := zeroField 1
  data := .classicalPointwise
  valid := zero_represented_on_work_window

def coreEquationState : EquationState representedEquation coreWindow :=
  zeroEquationState.restrict core_nested_work

theorem core_state_is_literal_restriction :
    coreEquationState.object = atlas.restrict (zeroField 1) coreWindow := by
  rfl

theorem zero_baseline : problem.Baseline (zeroField 1) :=
  zeroField_baseline 1 (by norm_num)

abbrev RootResidual :=
  {state : EquationState representedEquation workWindow //
    problem.Baseline state.object}

def zeroRootResidual : RootResidual := ⟨zeroEquationState, zero_baseline⟩

def rootLedger : Core.Residual.Ledger RootResidual :=
  Core.Residual.Ledger.initial zeroRootResidual

/-! ## Observable target and pressure-gauge transport -/

def velocityObservables : ObservableInterface model where
  Index := Unit
  Value := fun _ => Space
  observe := fun field _ => field.velocity origin
  visible := fun _ window => window.Contains origin
  localObserve := fun _ field _ => field.velocity origin
  localReflect := by
    intro field window index visible
    rfl

def velocityObservableInvariant :
    ObservableInvariant model representationSemantics velocityObservables where
  observe_eq := by
    intro left right equivalent index
    rcases equivalent with ⟨domain, velocity, viscosity, gauge⟩
    exact congrFun velocity origin

def VelocityZeroAtOrigin (field : Field) : Prop :=
  field.velocity origin = 0

def velocityTargetInterface :
    TargetInterface model VelocityZeroAtOrigin velocityObservables where
  accepts := fun values => values () = (0 : Space)
  target_iff := fun _ => Iff.rfl

def signature : PDE.FastTrack.Signature model VelocityZeroAtOrigin where
  semantics := representationSemantics
  observables := velocityObservables
  observableInvariant := velocityObservableInvariant
  targetInterface := velocityTargetInterface

abbrev SignatureStage :=
  Core.Residual.Ledger.Extension (Core.Residual.Ledger RootResidual)
    (fun _ => PDE.FastTrack.Signature model VelocityZeroAtOrigin)

def signatureStage : SignatureStage := signature.register rootLedger

theorem signature_stage_retains_root : signatureStage.previous = rootLedger :=
  PDE.FastTrack.Signature.register_previous signature rootLedger

theorem signature_stage_retains_residual :
    Core.Residual.residualOf signatureStage = zeroRootResidual :=
  rfl

def sampleTimeGauge : Real -> Real := fun time => time

def gaugeShiftedZero : Field :=
  (pressureGauge.coordinate sampleTimeGauge workWindow).realize (zeroField 1)

theorem gauge_shifted_zero_is_equivalent :
    representationSemantics.equivalent gaugeShiftedZero (zeroField 1) :=
  pressureGauge.equivalent_realize sampleTimeGauge workWindow (zeroField 1)

theorem pressure_gauge_preserves_velocity_target :
    VelocityZeroAtOrigin gaugeShiftedZero ↔
      VelocityZeroAtOrigin (zeroField 1) :=
  signature.targetInvariant.target_iff gauge_shifted_zero_is_equivalent

/-! ## Exact pressure local/tail assembly -/

abbrev PressureField := Spacetime -> Real

def pressureProblem : Core.Problem where
  Ambient := PressureField
  Baseline := fun _ => True
  BranchState := fun _ => Unit

local instance : Add pressureProblem.Ambient := by
  change Add PressureField
  infer_instance

def localPressure (window : Window) (pressure : PressureField) : PressureField := by
  classical
  exact fun point => if point ∈ window.region then pressure point else 0

def tailPressure (window : Window) (pressure : PressureField) : PressureField := by
  classical
  exact fun point => if point ∈ window.region then 0 else pressure point

def pressureSplit : LocalTailAssembly pressureProblem where
  Localizer := Window
  localPart := localPressure
  tailPart := tailPressure
  compatible := fun _ _ => True
  exact_reconstruction := by
    classical
    intro window pressure compatible
    funext point
    change localPressure window pressure point +
      tailPressure window pressure point = pressure point
    by_cases inside : point ∈ window.region
    · simp [localPressure, tailPressure, inside]
    · simp [localPressure, tailPressure, inside]

def pressureSemantics : RepresentationSemantics pressureProblem :=
  RepresentationSemantics.equality pressureProblem

def pressureAssembly :
    Core.AtomContextAssembly pressureProblem pressureSemantics :=
  pressureSplit.toCoreAssembly pressureSemantics

def pressureSite (window : Window) (pressure : PressureField) :
    pressureAssembly.Site pressure :=
  ⟨window, trivial⟩

theorem pressure_split_reconstructs (field : Field) :
    pressureAssembly.assemble
        (pressureAssembly.atom field.pressure
          (pressureSite workWindow field.pressure))
        (pressureAssembly.context field.pressure
          (pressureSite workWindow field.pressure)) =
      field.pressure :=
  pressureAssembly.reconstruct field.pressure
    (pressureSite workWindow field.pressure)

theorem local_pressure_agrees_on_work_window (field : Field) (point : Spacetime)
    (inside : point ∈ workWindow.region) :
    pressureAssembly.atom field.pressure
        (pressureSite workWindow field.pressure) point =
      field.pressure point := by
  change localPressure workWindow field.pressure point = field.pressure point
  classical
  simp [localPressure, inside]

theorem tail_pressure_vanishes_on_work_window (field : Field) (point : Spacetime)
    (inside : point ∈ workWindow.region) :
    pressureAssembly.context field.pressure
        (pressureSite workWindow field.pressure) point = 0 := by
  change tailPressure workWindow field.pressure point = 0
  classical
  simp [tailPressure, inside]

theorem represented_root_pressure_reconstructs :
    pressureAssembly.assemble
        (pressureAssembly.atom zeroRootResidual.1.object.pressure
          (pressureSite workWindow zeroRootResidual.1.object.pressure))
        (pressureAssembly.context zeroRootResidual.1.object.pressure
          (pressureSite workWindow zeroRootResidual.1.object.pressure)) =
      zeroRootResidual.1.object.pressure :=
  pressureAssembly.reconstruct _ _

/-! ## Explicit provision boundary -/

/-- There are no imported analytic contracts in this registration packet. -/
def importedAnalyticContracts : List Core.AuthorPrimitiveRef := []

def registrationWork : Core.PolynomialCheckBudget Unit :=
  Core.PolynomialCheckBudget.zero fun _ => 0

def registrationMetadata :
    Core.Metadata.DeclarationMetadata
      (Core.Residual.Ledger RootResidual) Unit where
  declaration :=
    ⟨"HypostructurePDEExamples.RepresentedNS2DLocalTailPacket",
      "signatureStage"⟩
  primitiveInputs := [
    ⟨⟨"HypostructurePDEExamples.RepresentedNS2DLocalTailPacket",
      "VelocityZeroAtOrigin"⟩, .definition⟩,
    ⟨⟨"HypostructurePDEExamples.RepresentedNS2DLocalTailPacket",
      "velocityObservables"⟩, .operator⟩,
    ⟨⟨"HypostructurePDEExamples.RepresentedNS2DLocalTailPacket",
      "velocityObservableInvariant"⟩, .semanticLaw⟩,
    ⟨⟨"HypostructurePDEExamples.RepresentedNS2DLocalTailPacket",
      "velocityTargetInterface"⟩, .semanticLaw⟩
  ]
  inferredDependencies := [
    ⟨⟨"Hypostructure.PDE.NavierStokes.Basic", "model"⟩,
      .registeredProfile⟩,
    ⟨⟨"Hypostructure.PDE.NavierStokes.Basic",
      "representationSemantics"⟩, .registeredProfile⟩
  ]
  ledgerQueries := []
  frameworkSearch := []
  generatedOutputs := [
    ⟨⟨"Hypostructure.PDE.FastTrack.Signature", "register"⟩,
      .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.PDE.FastTrack.Signature", "targetInvariant"⟩
  ]
  workBound := registrationWork
  manualObligations := []

def registrationMetadataComplete :
    Core.Metadata.Complete registrationMetadata :=
  ⟨rfl⟩

def localTailWork : Core.PolynomialCheckBudget PressureField :=
  Core.PolynomialCheckBudget.zero fun _ => 0

def localTailMetadata :
    Core.Metadata.DeclarationMetadata
      (Core.Residual.Ledger RootResidual) PressureField where
  declaration :=
    ⟨"HypostructurePDEExamples.RepresentedNS2DLocalTailPacket",
      "pressure_split_reconstructs"⟩
  primitiveInputs := [
    ⟨⟨"HypostructurePDEExamples.RepresentedNS2DLocalTailPacket",
      "pressureSplit"⟩, .semanticLaw⟩
  ]
  inferredDependencies := [
    ⟨⟨"Hypostructure.PDE.LocalTail", "LocalTailAssembly.toCoreAssembly"⟩,
      .registeredProfile⟩
  ]
  ledgerQueries := []
  frameworkSearch := []
  generatedOutputs := []
  genericTheorems := [
    ⟨"Hypostructure.Core.Assembly.AtomContext",
      "AtomContextAssembly.reconstruct"⟩
  ]
  workBound := localTailWork
  manualObligations := []

def localTailMetadataComplete : Core.Metadata.Complete localTailMetadata :=
  ⟨rfl⟩

def registrationProvisionBoundary : List Core.Provision.Entry :=
  [
    .primitive ⟨⟨"HypostructurePDEExamples.RepresentedNS2DLocalTailPacket",
      "VelocityZeroAtOrigin"⟩, .definition⟩,
    .primitive ⟨⟨"HypostructurePDEExamples.RepresentedNS2DLocalTailPacket",
      "velocityObservables"⟩, .operator⟩,
    .primitive ⟨⟨"HypostructurePDEExamples.RepresentedNS2DLocalTailPacket",
      "velocityObservableInvariant"⟩, .semanticLaw⟩,
    .primitive ⟨⟨"HypostructurePDEExamples.RepresentedNS2DLocalTailPacket",
      "velocityTargetInterface"⟩, .semanticLaw⟩,
    .inferred ⟨⟨"Hypostructure.PDE.NavierStokes.Basic", "model"⟩,
      .registeredProfile⟩,
    .inferred ⟨⟨"Hypostructure.PDE.NavierStokes.Basic",
      "representationSemantics"⟩, .registeredProfile⟩,
    .generated ⟨⟨"Hypostructure.PDE.FastTrack.Signature", "register"⟩,
      .residualStage⟩
  ]

def localTailProvisionBoundary : List Core.Provision.Entry :=
  [
    .primitive ⟨⟨"HypostructurePDEExamples.RepresentedNS2DLocalTailPacket",
      "pressureSplit"⟩, .semanticLaw⟩,
    .inferred ⟨⟨"Hypostructure.PDE.LocalTail",
      "LocalTailAssembly.toCoreAssembly"⟩, .registeredProfile⟩
  ]

theorem imported_analytic_boundary_is_empty : importedAnalyticContracts = [] :=
  rfl

theorem registration_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    ¬ obligation ∈ registrationMetadata.manualObligations :=
  registrationMetadataComplete.no_manual_obligation obligation

theorem local_tail_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    ¬ obligation ∈ localTailMetadata.manualObligations :=
  localTailMetadataComplete.no_manual_obligation obligation

#print axioms signature_stage_retains_root
#print axioms signature_stage_retains_residual
#print axioms pressure_gauge_preserves_velocity_target
#print axioms pressure_split_reconstructs
#print axioms represented_root_pressure_reconstructs
#print axioms imported_analytic_boundary_is_empty
#print axioms registration_has_no_manual_obligation
#print axioms local_tail_has_no_manual_obligation

end

end HypostructurePDEExamples.RepresentedNS2DLocalTailPacket
