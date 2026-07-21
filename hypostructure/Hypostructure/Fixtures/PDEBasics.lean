import Hypostructure.PDE.Coordinate
import Hypostructure.PDE.LocalTail
import Hypostructure.PDE.NavierStokes

/-!
# Axiom-free fixtures for the first PDE layer

These fixtures use finite scalar fields.  They test local restriction,
coordinate composition, gauge semantics, exact local/tail assembly, finite
budget localization, and pointwise closure without importing Graph or any
legacy module.
-/

namespace Hypostructure.Fixtures.PDEBasics

open Hypostructure.PDE

namespace FiniteRestriction

abbrev Index := Fin 4
abbrev Field := Index -> Int

def problem : Core.Problem where
  Ambient := Field
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def atlas : LocalAtlas problem where
  Point := Index
  Window := Finset Index
  contains := fun x W => x ∈ W
  nested := (· ⊆ ·)
  nested_refl := fun _ _ hx => hx
  nested_trans := fun hUV hVW _ hx => hVW (hUV hx)
  core := fun W => W
  core_nested := fun _ _ hx => hx
  LocalObject := fun W => W -> Int
  restrict := fun G _ x => G x
  restrictLocal := fun h object x => object ⟨x, h x.property⟩
  restrict_refl := by
    intro W object
    funext x
    rfl
  restrict_trans := by
    intro U V W hUV hVW object
    funext x
    rfl
  restrict_global := by
    intro G U V h
    rfl

def equation : RepresentedEquation problem atlas where
  EquationData := fun _ _ => Unit
  satisfies := fun _ => True
  restrictEquation := fun _ _ data => data
  restrict_satisfies := fun _ _ _ hvalid => hvalid

def model : LocalModel where
  problem := problem
  atlas := atlas
  equation := equation

def small : Finset Index := {1}
def work : Finset Index := {0, 1, 2}
def large : Finset Index := Finset.univ

theorem small_nested_work : atlas.nested small work := by
  simp [atlas, small, work]
theorem work_nested_large : atlas.nested work large := by simp [atlas, large]

def sample : Field := fun i => i.val

theorem nested_restriction_composes :
    atlas.restrictLocal small_nested_work
        (atlas.restrictLocal work_nested_large (atlas.restrict sample large)) =
      atlas.restrict sample small := by
  rw [atlas.restrict_global sample work_nested_large]
  rw [atlas.restrict_global sample small_nested_work]

theorem restriction_coordinate_is_exact :
    (restrictionCoordinate model small_nested_work).transform
        (atlas.restrict sample work) = atlas.restrict sample small :=
  atlas.restrict_global sample small_nested_work

theorem core_locality_restriction_is_exact :
    atlas.toCoreLocality.restrictNested small_nested_work
        (atlas.toCoreLocality.restrict sample work) =
      atlas.toCoreLocality.restrict sample small :=
  atlas.toCoreLocality.restrictNested_eq small_nested_work sample

end FiniteRestriction

namespace FiniteCoordinates

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
  restrict := fun G _ => G
  restrictLocal := fun _ object => object
  restrict_refl := fun _ _ => rfl
  restrict_trans := fun _ _ _ => rfl
  restrict_global := by
    intro G U V h
    rfl

def equation : RepresentedEquation problem atlas where
  EquationData := fun _ _ => Unit
  satisfies := fun _ => True
  restrictEquation := fun _ _ data => data
  restrict_satisfies := fun _ _ _ hvalid => hvalid

def model : LocalModel where
  problem := problem
  atlas := atlas
  equation := equation

def translate (shift : Index) (field : Field) : Field :=
  fun i => field (i + shift)

def scale (factor : Int) (field : Field) : Field :=
  fun i => factor * field i

def recentering : RecenteringInterface model where
  Shift := Index
  targetWindow := fun _ W => W
  coordinate := fun shift _ => {
    transform := translate shift
    transformEquation := fun _ => ()
    preservesEquation := fun _ _ => trivial
    realize := translate shift
    realizes := fun _ => rfl
    preservesBaseline := fun _ => trivial
  }

def rescaling : RescalingInterface model where
  Scale := Int
  targetWindow := fun _ W => W
  coordinate := fun factor _ => {
    transform := scale factor
    transformEquation := fun _ => ()
    preservesEquation := fun _ _ => trivial
    realize := scale factor
    realizes := fun _ => rfl
    preservesBaseline := fun _ => trivial
  }

/-- Translation is applied first and scaling second by framework composition. -/
def recenterThenRescale (shift : Index) (factor : Int) :
    Core.CoordinatePath (coordinateSystem model) () () :=
  .cons (recentering.coordinate shift ())
    (.cons (rescaling.coordinate factor ()) .nil)

theorem recenter_rescale_formula (shift : Index) (factor : Int)
    (field : Field) (i : Index) :
    (recenterThenRescale shift factor).run field i =
      factor * field (i + shift) := rfl

theorem recenter_rescale_concrete :
    (recenterThenRescale 1 3).run (fun i => (i.val : Int)) 0 = 3 := by
  decide

end FiniteCoordinates

namespace ConstantGauge

/-- Two scalar fields differ by one spatially constant representative. -/
def Equivalent (f g : FiniteCoordinates.Field) : Prop :=
  Exists fun constant : Int => forall i, g i = f i + constant

def semantics : RepresentationSemantics FiniteCoordinates.problem where
  equivalent := Equivalent
  equivalence := {
    refl := fun f => ⟨0, by simp⟩
    symm := by
      intro f g h
      rcases h with ⟨constant, hconstant⟩
      refine ⟨-constant, ?_⟩
      intro i
      rw [hconstant i]
      simp
    trans := by
      intro f g h hfg hgh
      rcases hfg with ⟨first, hfirst⟩
      rcases hgh with ⟨second, hsecond⟩
      refine ⟨first + second, ?_⟩
      intro i
      rw [hsecond i, hfirst i]
      simp [add_assoc]
  }
  baseline_iff := fun _ => iff_of_true trivial trivial

def target (field : FiniteCoordinates.Field) : Prop := field 0 = field 1

theorem target_invariant : TargetInvariant semantics target := by
  constructor
  intro f g hfg
  rcases hfg with ⟨constant, hconstant⟩
  constructor
  · intro hf
    change f 0 = f 1 at hf
    change g 0 = g 1
    rw [hconstant 0, hconstant 1, hf]
  · intro hg
    change g 0 = g 1 at hg
    change f 0 = f 1
    rw [hconstant 0, hconstant 1] at hg
    exact add_right_cancel hg

def shift (constant : Int) (field : FiniteCoordinates.Field) :
    FiniteCoordinates.Field :=
  fun i => field i + constant

def gauge : GaugeInterface FiniteCoordinates.model semantics where
  Gauge := Int
  coordinate := fun constant _ => {
    transform := shift constant
    transformEquation := fun _ => ()
    preservesEquation := fun _ _ => trivial
    realize := shift constant
    realizes := fun _ => rfl
    preservesBaseline := fun _ => trivial
  }
  equivalent_realize := by
    intro constant W field
    refine ⟨-constant, ?_⟩
    intro i
    simp [shift]

/-- Canonical representative with value zero at the distinguished point. -/
def normalize (field : FiniteCoordinates.Field) : FiniteCoordinates.Field :=
  fun i => field i - field 0

def quotient : RepresentationQuotient FiniteCoordinates.model semantics where
  Quotient := FiniteCoordinates.Field
  project := normalize
  project_eq_iff := by
    intro f g
    constructor
    · intro h
      refine ⟨g 0 - f 0, ?_⟩
      intro i
      have hi := congrFun h i
      simp only [normalize] at hi
      omega
    · rintro ⟨constant, hconstant⟩
      funext i
      have hi := hconstant i
      have hzero := hconstant 0
      simp only [normalize]
      omega

theorem gauge_projects_to_same_class (constant : Int)
    (field : FiniteCoordinates.Field) :
    quotient.project (shift constant field) = quotient.project field :=
  (quotient.project_eq_iff).mpr (gauge.equivalent_realize constant () field)

end ConstantGauge

namespace AdditiveAssembly

local instance : Add FiniteCoordinates.problem.Ambient := by
  change Add FiniteCoordinates.Field
  infer_instance

structure Cutoff where
  support : Finset FiniteCoordinates.Index
  includeTail : Bool

def localPart (cutoff : Cutoff) (field : FiniteCoordinates.Field) :
    FiniteCoordinates.Field :=
  fun i => if i ∈ cutoff.support then field i else 0

def tailPart (cutoff : Cutoff) (field : FiniteCoordinates.Field) :
    FiniteCoordinates.Field :=
  fun i => if cutoff.includeTail then
    if i ∈ cutoff.support then 0 else field i
  else 0

def assembly : LocalTailAssembly FiniteCoordinates.problem where
  Localizer := Cutoff
  localPart := localPart
  tailPart := tailPart
  compatible := fun cutoff _ => cutoff.includeTail = true
  exact_reconstruction := by
    intro cutoff field htail
    funext i
    change (if i ∈ cutoff.support then field i else 0) +
      (if cutoff.includeTail then
        (if i ∈ cutoff.support then 0 else field i)
      else 0) = field i
    by_cases hi : i ∈ cutoff.support
    · simp [hi]
    · simp [hi, htail]

def good : Cutoff := ⟨{0, 1}, true⟩

def equalitySemantics : RepresentationSemantics FiniteCoordinates.problem :=
  RepresentationSemantics.equality FiniteCoordinates.problem

def coreAssembly : Core.AtomContextAssembly FiniteCoordinates.problem
    equalitySemantics :=
  assembly.toCoreAssembly equalitySemantics

def goodSite (field : FiniteCoordinates.Field) : coreAssembly.Site field :=
  ⟨good, rfl⟩

theorem core_assembly_reconstructs (field : FiniteCoordinates.Field) :
    coreAssembly.assemble
        (coreAssembly.atom field (goodSite field))
      (coreAssembly.context field (goodSite field)) = field :=
  coreAssembly.reconstruct field (goodSite field)

end AdditiveAssembly

namespace FiniteBudget

/-- A negative finite total has a negative cell; no continuum is enumerated. -/
theorem exists_negative_cell (weight : Fin 4 -> Int)
    (htotal : (Finset.univ.sum weight) < 0) :
    Exists fun i => weight i < 0 := by
  by_contra h
  push Not at h
  have hnonnegative : 0 <= Finset.univ.sum weight :=
    Finset.sum_nonneg fun i _ => h i
  omega

end FiniteBudget

namespace PointwiseAssembly

/-- Pointwise local closure assembles globally without a finite point schedule. -/
theorem global_zero_of_pointwise {Point : Type} (field : Point -> Int)
    (localClosure : forall x, field x = 0) : field = 0 := by
  funext x
  exact localClosure x

end PointwiseAssembly

namespace NavierStokes2D

open Hypostructure.PDE.NavierStokes

def unitWindow : Window where
  center := (0, 0)
  radius := 1
  radius_pos := by norm_num

theorem zero_represented_on_unit_window :
    RepresentedClassicalOn (zeroField 1) unitWindow.region := by
  refine ⟨zeroField 1, gaugeEquivalent_refl _, ?_⟩
  exact (zeroField_classical 1 (by norm_num)).mono (by
    intro z hz
    simp [zeroField])

def zeroEquationState : EquationState representedEquation unitWindow where
  object := zeroField 1
  data := .classicalPointwise
  valid := zero_represented_on_unit_window

theorem restrict_zero_is_zero :
    atlas.restrict (zeroField 1) unitWindow = zeroField 1 := rfl

def linearTimeGauge : Real -> Real := fun time => time

theorem shifted_pressure_is_equivalent :
    representationSemantics.equivalent
      ((pressureGauge.coordinate linearTimeGauge unitWindow).realize
        (zeroField 1))
      (zeroField 1) :=
  pressureGauge.equivalent_realize linearTimeGauge unitWindow (zeroField 1)

def origin : Spacetime := (0, 0)

theorem local_regularity_target_is_gauge_invariant :
    RegularAt origin
        ((pressureGauge.coordinate linearTimeGauge unitWindow).realize
          (zeroField 1)) ↔
      RegularAt origin (zeroField 1) :=
  (regularAt_invariant origin).target_iff shifted_pressure_is_equivalent

theorem zero_is_regular_at_origin : RegularAt origin (zeroField 1) := by
  exact contDiff_const.contDiffAt

def doubleScale : Scale := ⟨2, by norm_num⟩
def unitShift : Spacetime := (1, 0)

theorem recenter_rescale_zero_composes :
    rescaleField doubleScale
        (recenterField unitShift (zeroField 1)) = zeroField 1 := by
  simp

abbrev PressureField := Spacetime -> Real

abbrev pressureProblem : Core.Problem := {
  Ambient := PressureField
  Baseline := fun _ => True
  BranchState := fun _ => Unit
}

local instance : Add pressureProblem.Ambient := by
  change Add PressureField
  infer_instance

/-- The full pressure is local and the complementary tail is zero. -/
def trivialPressureAssembly : LocalTailAssembly pressureProblem where
  Localizer := Unit
  localPart := fun _ pressure => pressure
  tailPart := fun _ _ => 0
  compatible := fun _ _ => True
  exact_reconstruction := by
    intro localizer pressure hcompatible
    funext z
    change pressure z + 0 = pressure z
    simp

def pressureSemantics : RepresentationSemantics pressureProblem :=
  RepresentationSemantics.equality pressureProblem

def corePressureAssembly :
    Core.AtomContextAssembly pressureProblem pressureSemantics :=
  trivialPressureAssembly.toCoreAssembly pressureSemantics

def pressureSite (pressure : PressureField) :
    corePressureAssembly.Site pressure :=
  ⟨(), trivial⟩

theorem trivial_pressure_split_reconstructs (pressure : PressureField) :
    corePressureAssembly.assemble
        (corePressureAssembly.atom pressure (pressureSite pressure))
        (corePressureAssembly.context pressure (pressureSite pressure)) =
      pressure :=
  corePressureAssembly.reconstruct pressure (pressureSite pressure)

end NavierStokes2D

end Hypostructure.Fixtures.PDEBasics
