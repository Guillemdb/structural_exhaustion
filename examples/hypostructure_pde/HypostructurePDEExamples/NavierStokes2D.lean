import Hypostructure.Core.Coordinate.Path
import Hypostructure.Core.Residual.Ledger
import Hypostructure.PDE.LocalTail
import Hypostructure.PDE.NavierStokes

/-!
# Concrete two-dimensional Navier--Stokes checks

These examples validate the registered representation on the zero solution.
They do not assert a general regularity theorem.
-/

namespace HypostructurePDEExamples.NavierStokes2D

open Hypostructure
open Hypostructure.PDE
open Hypostructure.PDE.NavierStokes

noncomputable section

def unitWindow : Window where
  center := (0, 0)
  radius := 1
  radius_pos := by norm_num

theorem zero_baseline : problem.Baseline (zeroField 1) :=
  zeroField_baseline 1 (by norm_num)

theorem zero_represented_on_unit_window :
    RepresentedClassicalOn (zeroField 1) unitWindow.region := by
  refine Exists.intro (zeroField 1) ?_
  refine And.intro (gaugeEquivalent_refl _) ?_
  exact (zeroField_classical 1 (by norm_num)).mono (by
    intro point member
    simp [zeroField])

def zeroEquationState : EquationState representedEquation unitWindow where
  object := zeroField 1
  data := .classicalPointwise
  valid := zero_represented_on_unit_window

theorem zero_restriction_is_zero :
    atlas.restrict (zeroField 1) unitWindow = zeroField 1 :=
  rfl

def restrictedZeroState : EquationState representedEquation unitWindow.core :=
  zeroEquationState.restrict (Window.core_nested unitWindow)

theorem restricted_zero_state_is_zero :
    restrictedZeroState.object = zeroField 1 :=
  rfl

def linearTimeGauge : Real -> Real := fun time => time

def gaugeShiftedZero : Field :=
  applyTimeGauge linearTimeGauge (zeroField 1)

theorem pressure_time_gauge_is_allowed :
    representationSemantics.equivalent gaugeShiftedZero (zeroField 1) := by
  exact pressureGauge.equivalent_realize linearTimeGauge unitWindow (zeroField 1)

def origin : Spacetime := (0, 0)

theorem regularity_target_is_gauge_invariant :
    RegularAt origin gaugeShiftedZero <-> RegularAt origin (zeroField 1) :=
  (regularAt_invariant origin).target_iff pressure_time_gauge_is_allowed

theorem zero_is_regular_at_origin : RegularAt origin (zeroField 1) :=
  contDiff_const.contDiffAt

def unitShift : Spacetime := (1, 0)

def doubleScale : Scale := Subtype.mk 2 (by norm_num)

inductive FieldCoordinatePrimitive
  | recenter (shift : Spacetime)
  | rescale (scale : Scale)

def fieldCoordinateSystem : Core.CoordinateSystem problem where
  Coordinate := Unit
  Object := fun _ => Field
  realize := fun _ field => field
  Primitive := fun _ _ => FieldCoordinatePrimitive
  act := fun primitive field =>
    match primitive with
    | .recenter shift => recenterField shift field
    | .rescale scale => rescaleField scale field

def recenterStep : fieldCoordinateSystem.Primitive () () :=
  FieldCoordinatePrimitive.recenter unitShift

def rescaleStep : fieldCoordinateSystem.Primitive () () :=
  FieldCoordinatePrimitive.rescale doubleScale

def zeroCoordinatePath :
    Core.CoordinatePath fieldCoordinateSystem () () :=
  .cons recenterStep (.cons rescaleStep .nil)

theorem core_path_preserves_zero :
    zeroCoordinatePath.run (zeroField 1) = zeroField 1 := by
  change rescaleField doubleScale
    (recenterField unitShift (zeroField 1)) = zeroField 1
  simp

abbrev PressureField := Spacetime -> Real

def pressureProblem : Core.Problem where
  Ambient := PressureField
  Baseline := fun _ => True
  BranchState := fun _ => Unit

local instance : Add pressureProblem.Ambient := by
  change Add PressureField
  infer_instance

def zeroPressure : pressureProblem.Ambient := fun _ => 0

def pressureSplit : LocalTailAssembly pressureProblem where
  Localizer := Unit
  localPart := fun _ pressure => pressure
  tailPart := fun _ _ => zeroPressure
  compatible := fun _ _ => True
  exact_reconstruction := by
    intro localizer pressure compatible
    funext point
    change pressure point + 0 = pressure point
    simp

def pressureSemantics : RepresentationSemantics pressureProblem :=
  RepresentationSemantics.equality pressureProblem

def pressureAssembly :
    Core.AtomContextAssembly pressureProblem pressureSemantics :=
  pressureSplit.toCoreAssembly pressureSemantics

def pressureSite (pressure : PressureField) : pressureAssembly.Site pressure :=
  Subtype.mk () trivial

theorem trivial_pressure_split_reconstructs (pressure : PressureField) :
    pressureAssembly.assemble
        (pressureAssembly.atom pressure (pressureSite pressure))
        (pressureAssembly.context pressure (pressureSite pressure)) =
      pressure :=
  pressureAssembly.reconstruct pressure (pressureSite pressure)

structure RootResidual where
  field : Field
  baseline : problem.Baseline field
  window : Window

def zeroRootResidual : RootResidual where
  field := zeroField 1
  baseline := zero_baseline
  window := unitWindow

def rootLedger : Core.Residual.Ledger RootResidual :=
  Core.Residual.Ledger.initial zeroRootResidual

theorem root_ledger_contains_zero :
    rootLedger.residual.field = zeroField 1 :=
  rfl

theorem root_ledger_contains_baseline :
    problem.Baseline rootLedger.residual.field :=
  rootLedger.residual.baseline

#print axioms zero_baseline
#print axioms pressure_time_gauge_is_allowed
#print axioms regularity_target_is_gauge_invariant
#print axioms core_path_preserves_zero
#print axioms trivial_pressure_split_reconstructs
#print axioms root_ledger_contains_baseline

end

end HypostructurePDEExamples.NavierStokes2D
