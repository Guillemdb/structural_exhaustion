import HypostructurePDEExamples.FiniteModel

/-!
# Core-owned coordinate composition

Recentring and rescaling are registered as primitive PDE coordinates. Their
sequence is represented and executed only by `Core.CoordinatePath`.
-/

namespace HypostructurePDEExamples.CoordinatePath

open Hypostructure
open Hypostructure.PDE
open HypostructurePDEExamples.FiniteModel

def recenter (shift : Index) (field : Field) : Field :=
  fun index => field (index + shift)

def rescale (factor : Int) (field : Field) : Field :=
  fun index => factor * field index

def recentering : RecenteringInterface model where
  Shift := Index
  targetWindow := fun _ window => window
  coordinate := fun shift _ => {
    transform := recenter shift
    transformEquation := fun _ => ()
    preservesEquation := fun _ _ => trivial
    realize := recenter shift
    realizes := fun _ => rfl
    preservesBaseline := fun _ => trivial
  }

def rescaling : RescalingInterface model where
  Scale := Int
  targetWindow := fun _ window => window
  coordinate := fun factor _ => {
    transform := rescale factor
    transformEquation := fun _ => ()
    preservesEquation := fun _ _ => trivial
    realize := rescale factor
    realizes := fun _ => rfl
    preservesBaseline := fun _ => trivial
  }

def recenterThenRescale (shift : Index) (factor : Int) :
    Core.CoordinatePath (coordinateSystem model) () () :=
  .cons (recentering.coordinate shift ())
    (.cons (rescaling.coordinate factor ()) .nil)

theorem run_formula (shift : Index) (factor : Int) (field : Field)
    (index : Index) :
    (recenterThenRescale shift factor).run field index =
      factor * field (index + shift) :=
  rfl

theorem path_has_two_primitives (shift : Index) (factor : Int) :
    (recenterThenRescale shift factor).length = 2 :=
  rfl

theorem concrete_execution :
    (recenterThenRescale 1 3).run sample 0 = 3 := by
  decide

#print axioms run_formula
#print axioms path_has_two_primitives
#print axioms concrete_execution

end HypostructurePDEExamples.CoordinatePath
