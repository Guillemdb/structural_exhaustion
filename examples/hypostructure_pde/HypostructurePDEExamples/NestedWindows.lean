import HypostructurePDEExamples.FiniteModel

/-!
# Nested finite-window restriction
-/

namespace HypostructurePDEExamples.NestedWindows

open Hypostructure
open Hypostructure.PDE
open HypostructurePDEExamples.FiniteModel

def windowAtlas : LocalAtlas problem where
  Point := Index
  Window := Finset Index
  contains := fun index window => index ∈ window
  nested := fun small large => small ⊆ large
  nested_refl := fun _ _ member => member
  nested_trans := fun first second _ member => second (first member)
  core := id
  core_nested := fun _ _ member => member
  LocalObject := fun window => window -> Int
  restrict := fun field _ index => field index
  restrictLocal := fun nested object index =>
    object (Subtype.mk index.1 (nested index.2))
  restrict_refl := by
    intro window object
    funext index
    rfl
  restrict_trans := by
    intro small middle large first second object
    funext index
    rfl
  restrict_global := by
    intro field small large nested
    rfl

def windowEquation : RepresentedEquation problem windowAtlas where
  EquationData := fun _ _ => Unit
  satisfies := fun _ => True
  restrictEquation := fun _ _ data => data
  restrict_satisfies := fun _ _ _ valid => valid

def windowModel : LocalModel where
  problem := problem
  atlas := windowAtlas
  equation := windowEquation

def small : Finset Index := {1}
def work : Finset Index := {0, 1, 2}
def large : Finset Index := Finset.univ

theorem small_nested_work : windowAtlas.nested small work := by
  simp [windowAtlas, small, work]

theorem work_nested_large : windowAtlas.nested work large := by
  simp [windowAtlas, large]

theorem nested_restriction_composes (field : Field) :
    windowAtlas.restrictLocal small_nested_work
        (windowAtlas.restrictLocal work_nested_large
          (windowAtlas.restrict field large)) =
      windowAtlas.restrict field small := by
  rw [windowAtlas.restrict_global field work_nested_large]
  rw [windowAtlas.restrict_global field small_nested_work]

theorem core_locality_restriction_is_exact (field : Field) :
    windowAtlas.toCoreLocality.restrictNested small_nested_work
        (windowAtlas.toCoreLocality.restrict field work) =
      windowAtlas.toCoreLocality.restrict field small :=
  windowAtlas.toCoreLocality.restrictNested_eq small_nested_work field

theorem restriction_coordinate_is_exact (field : Field) :
    (restrictionCoordinate windowModel small_nested_work).transform
        (windowAtlas.restrict field work) =
      windowAtlas.restrict field small :=
  windowAtlas.restrict_global field small_nested_work

#print axioms nested_restriction_composes
#print axioms core_locality_restriction_is_exact
#print axioms restriction_coordinate_is_exact

end HypostructurePDEExamples.NestedWindows
