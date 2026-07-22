import Mathlib.Topology.Algebra.Module.FiniteDimension
import Hypostructure.PDE.StructuralGradient

/-!
# Finite structural-gradient fixtures

The identity and zero operators on `Real` exercise opposite exact range and
kernel geometries.  Both ranges are closed, as every finite-dimensional range
must be; the examples do not assert that finite rank supplies a continuum
spectral gap.  Their gap witnesses are proved directly from the displayed
Poincare inequalities.
-/

namespace Hypostructure.Fixtures.PDEStructuralGradient

open Hypostructure.PDE
open StructuralGradient

/-- The total identity as a Mathlib partial linear operator. -/
def identityOperator : Real →ₗ.[Real] Real where
  domain := ⊤
  toFun := (⊤ : Submodule Real Real).subtype

@[simp]
theorem identityOperator_apply (potential : identityOperator.domain) :
    identityOperator potential = (potential : Real) :=
  rfl

/-- The total zero map as a Mathlib partial linear operator. -/
def zeroOperator : Real →ₗ.[Real] Real where
  domain := ⊤
  toFun := 0

@[simp]
theorem zeroOperator_apply (potential : zeroOperator.domain) :
    zeroOperator potential = 0 := by
  rfl

/-- Closed, densely defined identity structural gradient. -/
def identityGradient : StructuralGradient Real Real where
  operator := identityOperator
  operator_closed := identityOperator.graph.closed_of_finiteDimensional
  domain_dense := by
    change Dense ((⊤ : Submodule Real Real) : Set Real)
    rw [Submodule.top_coe]
    exact dense_univ

/-- Closed, densely defined zero structural gradient. -/
def zeroGradient : StructuralGradient Real Real where
  operator := zeroOperator
  operator_closed := zeroOperator.graph.closed_of_finiteDimensional
  domain_dense := by
    change Dense ((⊤ : Submodule Real Real) : Set Real)
    rw [Submodule.top_coe]
    exact dense_univ

theorem identity_range : identityGradient.range = ⊤ := by
  ext current
  constructor
  · intro
    trivial
  · intro
    exact (identityGradient.mem_range_iff current).mpr
      ⟨⟨current, Submodule.mem_top⟩, rfl⟩

theorem identity_kernel : identityGradient.kernel = ⊥ := by
  ext potential
  rw [Submodule.mem_bot]
  constructor
  · intro inKernel
    obtain ⟨inDomain, vanishes⟩ :=
      (identityGradient.mem_kernel_iff potential).mp inKernel
    exact vanishes
  · rintro rfl
    simp

theorem zero_range : zeroGradient.range = ⊥ := by
  ext current
  rw [Submodule.mem_bot]
  constructor
  · intro inRange
    obtain ⟨potential, equalsCurrent⟩ :=
      (zeroGradient.mem_range_iff current).mp inRange
    calc
      current = zeroGradient.operator potential := equalsCurrent.symm
      _ = 0 := by rfl
  · rintro rfl
    simp

theorem zero_kernel : zeroGradient.kernel = ⊤ := by
  ext potential
  constructor
  · intro
    trivial
  · intro
    exact (zeroGradient.mem_kernel_iff potential).mpr
      ⟨Submodule.mem_top, rfl⟩

/-- The identity has the explicit structural gap `gamma = 1`. -/
def identityGap : PositiveStructuralGap identityGradient where
  gamma := 1
  gamma_pos := zero_lt_one
  poincare := by
    intro potential _orthogonal
    change ‖(potential : Real)‖ ^ 2 ≤
      (1 : Real)⁻¹ * ‖(potential : Real)‖ ^ 2
    simp

/-- The zero operator also satisfies the kernel-orthogonal formulation: its
kernel complement is trivial, so the Poincare inequality is vacuous there. -/
def zeroGap : PositiveStructuralGap zeroGradient where
  gamma := 1
  gamma_pos := zero_lt_one
  poincare := by
    intro potential orthogonal
    have potential_eq_zero : (potential : Real) = 0 := by
      simpa [zero_kernel] using orthogonal
    change ‖(potential : Real)‖ ^ 2 ≤
      (1 : Real)⁻¹ * ‖(0 : Real)‖ ^ 2
    simp [potential_eq_zero]

def identityClosedRange : ClosedRangeCertificate identityGradient where
  range_isClosed := by
    rw [identity_range]
    exact isClosed_univ

def zeroClosedRange : ClosedRangeCertificate zeroGradient where
  range_isClosed := by
    rw [zero_range]
    exact isClosed_singleton

/-- Finite identity verification of both directions of the registered
closed-range criterion.  The gap itself was proved directly above. -/
def identityCriterion : ClosedRangeCriterion identityGradient where
  closedRange_iff_positiveGap :=
    ⟨fun _ => ⟨identityGap⟩, fun _ => identityClosedRange⟩

/-- Finite zero verification of both directions of the registered
closed-range criterion.  No rank-to-gap theorem is used. -/
def zeroCriterion : ClosedRangeCriterion zeroGradient where
  closedRange_iff_positiveGap :=
    ⟨fun _ => ⟨zeroGap⟩, fun _ => zeroClosedRange⟩

noncomputable def identityDirected :
    DirectedExhaustivenessCertificate identityGradient :=
  DirectedExhaustivenessCertificate.ofClosedRange identityClosedRange

noncomputable def zeroDirected : DirectedExhaustivenessCertificate zeroGradient :=
  DirectedExhaustivenessCertificate.ofClosedRange zeroClosedRange

theorem identity_represented (current : Real) :
    identityDirected.represented current = current := by
  exact identityDirected.represented_unique current current 0
    (by simp [identity_range])
    (by simp [identity_range])
    (by simp)

theorem identity_residual (current : Real) :
    identityDirected.residual current = 0 := by
  exact identityDirected.residual_unique current current 0
    (by simp [identity_range])
    (by simp [identity_range])
    (by simp)

theorem zero_represented (current : Real) :
    zeroDirected.represented current = 0 := by
  exact zeroDirected.represented_unique current 0 current
    (by simp [zero_range])
    (by simp [zero_range])
    (by simp)

theorem zero_residual (current : Real) :
    zeroDirected.residual current = current := by
  exact zeroDirected.residual_unique current 0 current
    (by simp [zero_range])
    (by simp [zero_range])
    (by simp)

theorem identity_has_no_boundary_defect (current : Real) :
    ¬ identityGradient.IsBoundaryDefect current :=
  identityClosedRange.noBoundaryDefect current

theorem zero_has_no_boundary_defect (current : Real) :
    ¬ zeroGradient.IsBoundaryDefect current :=
  zeroClosedRange.noBoundaryDefect current

end Hypostructure.Fixtures.PDEStructuralGradient

#print axioms Hypostructure.Fixtures.PDEStructuralGradient.identityGradient
#print axioms Hypostructure.Fixtures.PDEStructuralGradient.identityGap
#print axioms Hypostructure.Fixtures.PDEStructuralGradient.identity_represented
#print axioms Hypostructure.Fixtures.PDEStructuralGradient.zeroGradient
#print axioms Hypostructure.Fixtures.PDEStructuralGradient.zeroGap
#print axioms Hypostructure.Fixtures.PDEStructuralGradient.zero_residual
