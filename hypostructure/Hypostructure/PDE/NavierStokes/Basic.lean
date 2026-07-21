import Hypostructure.PDE.Coordinate

/-!
# A minimal classical two-dimensional Navier--Stokes model

The equation is the unforced incompressible Navier--Stokes equation on subsets
of real space-time.  Derivatives are genuine Frechet derivatives.  Pressure is
represented modulo functions of time; raw classical representatives retain an
explicit domain and regularity class.

This module registers no regularity theorem.
-/

namespace Hypostructure.PDE.NavierStokes

noncomputable section

abbrev SpatialIndex := Fin 2
abbrev Space := EuclideanSpace Real SpatialIndex
abbrev Spacetime := Real × Space

/-- Velocity-pressure data with an explicit physical domain and viscosity. -/
@[ext]
structure Field where
  domain : Set Spacetime
  velocity : Spacetime -> Space
  pressure : Spacetime -> Real
  viscosity : Real

/-- Unit time direction in space-time. -/
def timeDirection : Spacetime := (1, 0)

/-- The `i`th unit spatial direction in space-time. -/
def spatialDirection (i : SpatialIndex) : Spacetime :=
  (0, EuclideanSpace.single i 1)

/-- Classical time derivative of velocity. -/
def timeDerivative (velocity : Spacetime -> Space) (z : Spacetime) : Space :=
  fderiv Real velocity z timeDirection

/-- Classical derivative of velocity in the `i`th spatial direction. -/
def spatialDerivative (velocity : Spacetime -> Space)
    (i : SpatialIndex) (z : Spacetime) : Space :=
  fderiv Real velocity z (spatialDirection i)

/-- Second classical derivative in the `i`th spatial direction. -/
def spatialSecondDerivative (velocity : Spacetime -> Space)
    (i : SpatialIndex) (z : Spacetime) : Space :=
  fderiv Real (fun y => spatialDerivative velocity i y) z (spatialDirection i)

/-- Spatial Laplacian of velocity. -/
def laplacian (velocity : Spacetime -> Space) (z : Spacetime) : Space :=
  Finset.univ.sum fun i => spatialSecondDerivative velocity i z

/-- The nonlinear transport term `(u . grad)u`. -/
def convection (velocity : Spacetime -> Space) (z : Spacetime) : Space :=
  Finset.univ.sum fun i => velocity z i • spatialDerivative velocity i z

/-- Spatial pressure gradient. -/
def pressureGradient (pressure : Spacetime -> Real) (z : Spacetime) : Space :=
  (EuclideanSpace.equiv SpatialIndex Real).symm fun i =>
    fderiv Real pressure z (spatialDirection i)

/-- Spatial divergence of velocity. -/
def divergence (velocity : Spacetime -> Space) (z : Spacetime) : Real :=
  Finset.univ.sum fun i => spatialDerivative velocity i z i

/--
The pointwise classical equation on a declared region.  Regularity,
incompressibility, viscosity, physical domain, and momentum equation are all
explicit fields.
-/
structure ClassicalOn (field : Field) (region : Set Spacetime) : Prop where
  region_in_domain : region ⊆ field.domain
  positive_viscosity : 0 < field.viscosity
  velocity_regular : ContDiff Real 2 field.velocity
  pressure_regular : ContDiff Real 1 field.pressure
  divergence_free : forall z, z ∈ region -> divergence field.velocity z = 0
  momentum : forall z, z ∈ region ->
    timeDerivative field.velocity z + convection field.velocity z +
        pressureGradient field.pressure z =
      field.viscosity • laplacian field.velocity z

namespace ClassicalOn

/-- A classical equation restricts to every smaller region. -/
theorem mono {field : Field} {small large : Set Spacetime}
    (hsmall : small ⊆ large) (h : ClassicalOn field large) :
    ClassicalOn field small where
  region_in_domain := fun _ hz => h.region_in_domain (hsmall hz)
  positive_viscosity := h.positive_viscosity
  velocity_regular := h.velocity_regular
  pressure_regular := h.pressure_regular
  divergence_free := fun z hz => h.divergence_free z (hsmall hz)
  momentum := fun z hz => h.momentum z (hsmall hz)

end ClassicalOn

/-- Pressure gauge equivalence modulo an arbitrary function of time. -/
def GaugeEquivalent (first second : Field) : Prop :=
  first.domain = second.domain ∧
  first.velocity = second.velocity ∧
  first.viscosity = second.viscosity ∧
  Exists fun gauge : Real -> Real => forall z,
    second.pressure z = first.pressure z + gauge z.1

theorem gaugeEquivalent_refl (field : Field) : GaugeEquivalent field field := by
  refine ⟨rfl, rfl, rfl, 0, ?_⟩
  simp

theorem gaugeEquivalent_symm {first second : Field}
    (h : GaugeEquivalent first second) : GaugeEquivalent second first := by
  rcases h with ⟨hdomain, hvelocity, hviscosity, gauge, hpressure⟩
  refine ⟨hdomain.symm, hvelocity.symm, hviscosity.symm, -gauge, ?_⟩
  intro z
  rw [hpressure z]
  simp

theorem gaugeEquivalent_trans {first second third : Field}
    (hfirst : GaugeEquivalent first second)
    (hsecond : GaugeEquivalent second third) : GaugeEquivalent first third := by
  rcases hfirst with ⟨hdomain₁, hvelocity₁, hviscosity₁, gauge₁, hpressure₁⟩
  rcases hsecond with ⟨hdomain₂, hvelocity₂, hviscosity₂, gauge₂, hpressure₂⟩
  refine ⟨hdomain₁.trans hdomain₂, hvelocity₁.trans hvelocity₂,
    hviscosity₁.trans hviscosity₂, gauge₁ + gauge₂, ?_⟩
  intro z
  rw [hpressure₂ z, hpressure₁ z]
  simp [add_assoc]

def gaugeEquivalence : Equivalence GaugeEquivalent :=
  ⟨gaugeEquivalent_refl, @gaugeEquivalent_symm, @gaugeEquivalent_trans⟩

/-- Apply a time-dependent pressure gauge without changing physical data. -/
def applyTimeGauge (gauge : Real -> Real) (field : Field) : Field where
  domain := field.domain
  velocity := field.velocity
  pressure := fun z => field.pressure z + gauge z.1
  viscosity := field.viscosity

theorem gaugeEquivalent_applyTimeGauge (gauge : Real -> Real) (field : Field) :
    GaugeEquivalent field (applyTimeGauge gauge field) := by
  refine ⟨rfl, rfl, rfl, gauge, ?_⟩
  intro z
  rfl

/-- A raw classical representative of the complete declared domain. -/
def RawClassicalSolution (field : Field) : Prop :=
  ClassicalOn field field.domain

/-- The baseline is the gauge saturation of raw classical solutions. -/
def RepresentedSolution (field : Field) : Prop :=
  Exists fun representative =>
    GaugeEquivalent field representative ∧ RawClassicalSolution representative

/-- Local represented equation on a region, also saturated by pressure gauge. -/
def RepresentedClassicalOn (field : Field) (region : Set Spacetime) : Prop :=
  Exists fun representative =>
    GaugeEquivalent field representative ∧ ClassicalOn representative region

theorem representedClassicalOn_mono {field : Field} {small large : Set Spacetime}
    (hsmall : small ⊆ large) (h : RepresentedClassicalOn field large) :
    RepresentedClassicalOn field small := by
  rcases h with ⟨representative, hequivalent, hclassical⟩
  exact ⟨representative, hequivalent, hclassical.mono hsmall⟩

theorem representedClassicalOn_iff {first second : Field} {region : Set Spacetime}
    (h : GaugeEquivalent first second) :
    RepresentedClassicalOn first region ↔ RepresentedClassicalOn second region := by
  constructor
  · rintro ⟨representative, hfirst, hclassical⟩
    exact ⟨representative,
      gaugeEquivalent_trans (gaugeEquivalent_symm h) hfirst, hclassical⟩
  · rintro ⟨representative, hsecond, hclassical⟩
    exact ⟨representative, gaugeEquivalent_trans h hsecond, hclassical⟩

theorem representedSolution_iff {first second : Field}
    (h : GaugeEquivalent first second) :
    RepresentedSolution first ↔ RepresentedSolution second := by
  constructor
  · rintro ⟨representative, hfirst, hclassical⟩
    exact ⟨representative,
      gaugeEquivalent_trans (gaugeEquivalent_symm h) hfirst, hclassical⟩
  · rintro ⟨representative, hsecond, hclassical⟩
    exact ⟨representative, gaugeEquivalent_trans h hsecond, hclassical⟩

def problem : Core.Problem where
  Ambient := Field
  Baseline := RepresentedSolution
  BranchState := fun _ => Unit

/-- Backward parabolic cylinder. -/
structure Window where
  center : Spacetime
  radius : Real
  radius_pos : 0 < radius

namespace Window

def Contains (z : Spacetime) (W : Window) : Prop :=
  W.center.1 - W.radius ^ 2 < z.1 ∧
  z.1 ≤ W.center.1 ∧
  dist z.2 W.center.2 < W.radius

def region (W : Window) : Set Spacetime := {z | Contains z W}

def Nested (small large : Window) : Prop := small.region ⊆ large.region

def core (W : Window) : Window where
  center := W.center
  radius := W.radius / 2
  radius_pos := by linarith [W.radius_pos]

theorem core_nested (W : Window) : Nested W.core W := by
  intro z hz
  rcases hz with ⟨hlower, hupper, hspace⟩
  refine ⟨?_, hupper, ?_⟩
  · dsimp [core] at hlower ⊢
    nlinarith [sq_pos_of_pos W.radius_pos]
  · dsimp [core] at hspace ⊢
    linarith [W.radius_pos]

end Window

def atlas : LocalAtlas problem where
  Point := Spacetime
  Window := Window
  contains := Window.Contains
  nested := Window.Nested
  nested_refl := fun _ _ hz => hz
  nested_trans := fun hsmall hlarge _ hz => hlarge (hsmall hz)
  core := Window.core
  core_nested := Window.core_nested
  LocalObject := fun _ => Field
  restrict := fun field _ => field
  restrictLocal := fun _ field => field
  restrict_refl := fun _ _ => rfl
  restrict_trans := fun _ _ _ => rfl
  restrict_global := by
    intro field small large h
    rfl

/-- The regularity interpretation carried by the represented equation data. -/
inductive EquationInterpretation
  | classicalPointwise
  deriving DecidableEq

def representedEquation : RepresentedEquation problem atlas where
  EquationData := fun _ _ => EquationInterpretation
  satisfies := fun {W} {field} _ =>
    RepresentedClassicalOn field W.region
  restrictEquation := fun _ _ interpretation => interpretation
  restrict_satisfies := by
    intro small large hnested field interpretation hvalid
    exact representedClassicalOn_mono hnested hvalid

def model : LocalModel where
  problem := problem
  atlas := atlas
  equation := representedEquation

def representationSemantics : RepresentationSemantics problem where
  equivalent := GaugeEquivalent
  equivalence := gaugeEquivalence
  baseline_iff := representedSolution_iff

/-- Local smoothness of velocity at a fixed space-time point. -/
def RegularAt (z : Spacetime) (field : Field) : Prop :=
  ContDiffAt Real ⊤ field.velocity z

theorem regularAt_invariant (z : Spacetime) :
    TargetInvariant representationSemantics (RegularAt z) := by
  constructor
  intro first second h
  rcases h with ⟨_, hvelocity, _, _⟩
  change ContDiffAt Real ⊤ first.velocity z ↔
    ContDiffAt Real ⊤ second.velocity z
  rw [hvelocity]

/-- Pressure-gauge coordinates preserve the represented equation by construction. -/
def pressureGauge : GaugeInterface model representationSemantics where
  Gauge := Real -> Real
  coordinate := fun gauge W => {
    transform := applyTimeGauge gauge
    transformEquation := fun interpretation => interpretation
    preservesEquation := by
      intro field interpretation hvalid
      change RepresentedClassicalOn field W.region at hvalid
      change RepresentedClassicalOn (applyTimeGauge gauge field) W.region
      exact (representedClassicalOn_iff
        (gaugeEquivalent_applyTimeGauge gauge field)).mp hvalid
    realize := applyTimeGauge gauge
    realizes := fun _ => rfl
    preservesBaseline := by
      intro field hbaseline
      change RepresentedSolution field at hbaseline
      change RepresentedSolution (applyTimeGauge gauge field)
      exact (representedSolution_iff
        (gaugeEquivalent_applyTimeGauge gauge field)).mp hbaseline
  }
  equivalent_realize := fun gauge W field =>
    gaugeEquivalent_symm (gaugeEquivalent_applyTimeGauge gauge field)

/-- The zero velocity and pressure field on all of space-time. -/
def zeroField (viscosity : Real) : Field where
  domain := Set.univ
  velocity := fun _ => 0
  pressure := fun _ => 0
  viscosity := viscosity

theorem zeroField_classical (viscosity : Real) (hviscosity : 0 < viscosity) :
    RawClassicalSolution (zeroField viscosity) := by
  refine {
    region_in_domain := by simp [zeroField]
    positive_viscosity := hviscosity
    velocity_regular := by exact contDiff_const
    pressure_regular := by exact contDiff_const
    divergence_free := ?_
    momentum := ?_
  }
  · intro z hz
    simp [divergence, spatialDerivative, zeroField]
  · intro z hz
    ext i
    simp [timeDerivative, convection, pressureGradient, laplacian,
      spatialSecondDerivative, spatialDerivative, zeroField]

theorem zeroField_baseline (viscosity : Real) (hviscosity : 0 < viscosity) :
    problem.Baseline (zeroField viscosity) :=
  ⟨zeroField viscosity, gaugeEquivalent_refl _,
    zeroField_classical viscosity hviscosity⟩

/-- Translating coordinates; no general equation-preservation theorem is asserted here. -/
def translatePoint (shift z : Spacetime) : Spacetime :=
  (z.1 + shift.1, z.2 + shift.2)

def recenterField (shift : Spacetime) (field : Field) : Field where
  domain := translatePoint shift ⁻¹' field.domain
  velocity := fun z => field.velocity (translatePoint shift z)
  pressure := fun z => field.pressure (translatePoint shift z)
  viscosity := field.viscosity

/-- Positive parabolic scale. -/
abbrev Scale := {scale : Real // 0 < scale}

def scalePoint (scale : Scale) (z : Spacetime) : Spacetime :=
  (scale.1 ^ 2 * z.1, scale.1 • z.2)

/-- Standard Navier--Stokes parabolic scaling about the origin. -/
def rescaleField (scale : Scale) (field : Field) : Field where
  domain := scalePoint scale ⁻¹' field.domain
  velocity := fun z => scale.1 • field.velocity (scalePoint scale z)
  pressure := fun z => scale.1 ^ 2 * field.pressure (scalePoint scale z)
  viscosity := field.viscosity

@[simp]
theorem recenter_zeroField (shift : Spacetime) (viscosity : Real) :
    recenterField shift (zeroField viscosity) = zeroField viscosity := by
  ext z <;> simp [recenterField, zeroField]

@[simp]
theorem rescale_zeroField (scale : Scale) (viscosity : Real) :
    rescaleField scale (zeroField viscosity) = zeroField viscosity := by
  ext z <;> simp [rescaleField, zeroField]

end

end Hypostructure.PDE.NavierStokes
