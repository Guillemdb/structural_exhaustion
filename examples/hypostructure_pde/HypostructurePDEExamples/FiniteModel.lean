import Hypostructure.PDE.Coordinate
import Hypostructure.PDE.LocalTail

/-!
# Finite scalar PDE model

This concrete model supplies finite scalar fields for exercising the generic
PDE and Core APIs. Its equation is deliberately trivial; all interesting
claims in downstream examples concern exact framework behavior.
-/

namespace HypostructurePDEExamples

open Hypostructure
open Hypostructure.PDE

namespace FiniteModel

abbrev Index := Fin 5
abbrev Field := Index -> Int

def problem : Core.Problem where
  Ambient := Field
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def atlas : LocalAtlas problem where
  Point := Index
  Window := Unit
  contains := fun _ _ => True
  nested := fun _ _ => True
  nested_refl := fun _ => trivial
  nested_trans := fun _ _ => trivial
  core := id
  core_nested := fun _ => trivial
  LocalObject := fun _ => Field
  restrict := fun field _ => field
  restrictLocal := fun _ field => field
  restrict_refl := fun _ _ => rfl
  restrict_trans := fun _ _ _ => rfl
  restrict_global := by
    intro field small large nested
    rfl

def equation : RepresentedEquation problem atlas where
  EquationData := fun _ _ => Unit
  satisfies := fun _ => True
  restrictEquation := fun _ _ data => data
  restrict_satisfies := fun _ _ _ valid => valid

def model : LocalModel where
  problem := problem
  atlas := atlas
  equation := equation

def equalitySemantics : RepresentationSemantics problem :=
  RepresentationSemantics.equality problem

def sample : Field := fun index => index.val

#print axioms model

end FiniteModel

end HypostructurePDEExamples
