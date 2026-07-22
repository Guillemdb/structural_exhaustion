import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Structural gradients and directed exhaustiveness

This module formalizes the operator vocabulary used by Theorems 4.2--4.3 of
`PDEs/10_continuous_extension.ipynb`.  A structural gradient is a closed,
densely defined partial linear operator between real Hilbert spaces.  Its
domain, range, and kernel are the exact Mathlib `LinearPMap`/`LinearMap`
objects.

A positive structural gap records the literal Poincare inequality on
`D(G) \cap (ker G)^\perp`.  It is deliberately separate from closed range:
this file contains no finite-rank-to-gap implication.  The analytic
closed-range theorem can be registered as a `ClosedRangeCriterion`.

Once closed range is certified, the framework derives the represented and
orthogonal-residual components by Hilbert-space projection.  The constructor
of that derived payload is private.
-/

namespace Hypostructure.PDE

universe uPotential uCurrent

/-- A closed, densely defined structural-gradient operator between real
Hilbert spaces.  Closedness means that the exact Mathlib graph is closed. -/
structure StructuralGradient
    (Potential : Type uPotential) (Current : Type uCurrent)
    [NormedAddCommGroup Potential] [InnerProductSpace Real Potential]
    [CompleteSpace Potential]
    [NormedAddCommGroup Current] [InnerProductSpace Real Current]
    [CompleteSpace Current] where
  operator : Potential →ₗ.[Real] Current
  operator_closed : operator.IsClosed
  domain_dense : Dense (operator.domain : Set Potential)

namespace StructuralGradient

variable {Potential : Type uPotential} {Current : Type uCurrent}
variable [NormedAddCommGroup Potential] [InnerProductSpace Real Potential]
variable [CompleteSpace Potential]
variable [NormedAddCommGroup Current] [InnerProductSpace Real Current]
variable [CompleteSpace Current]

/-- The exact declared operator domain. -/
abbrev Domain (gradient : StructuralGradient Potential Current) :=
  gradient.operator.domain

/-- The exact algebraic image of the operator on its declared domain. -/
def range (gradient : StructuralGradient Potential Current) :
    Submodule Real Current :=
  LinearMap.range gradient.operator.toFun

/-- The exact kernel as a submodule of the declared operator domain. -/
def kernelInDomain (gradient : StructuralGradient Potential Current) :
    Submodule Real gradient.Domain :=
  LinearMap.ker gradient.operator.toFun

/-- The operator kernel embedded back into the ambient potential Hilbert
space.  This is the image of Mathlib's exact domain-level kernel under the
domain subtype map. -/
def kernel (gradient : StructuralGradient Potential Current) :
    Submodule Real Potential :=
  gradient.kernelInDomain.map gradient.operator.domain.subtype

@[simp]
theorem mem_range_iff (gradient : StructuralGradient Potential Current)
    (current : Current) :
    current ∈ gradient.range ↔
      ∃ potential : gradient.Domain, gradient.operator potential = current := by
  simp [range]

@[simp]
theorem mem_kernelInDomain_iff
    (gradient : StructuralGradient Potential Current)
    (potential : gradient.Domain) :
    potential ∈ gradient.kernelInDomain ↔
      gradient.operator potential = 0 := by
  simp [kernelInDomain]

@[simp]
theorem mem_kernel_iff (gradient : StructuralGradient Potential Current)
    (potential : Potential) :
    potential ∈ gradient.kernel ↔
      ∃ inDomain : potential ∈ gradient.operator.domain,
        gradient.operator ⟨potential, inDomain⟩ = 0 := by
  constructor
  · rintro ⟨domainPotential, inKernel, rfl⟩
    exact ⟨domainPotential.property,
      (LinearMap.mem_ker.mp inKernel)⟩
  · rintro ⟨inDomain, vanishes⟩
    refine ⟨⟨potential, inDomain⟩, ?_, rfl⟩
    exact LinearMap.mem_ker.mpr vanishes

/-- Every ambient kernel element lies in the declared operator domain. -/
theorem kernel_le_domain (gradient : StructuralGradient Potential Current) :
    gradient.kernel ≤ gradient.operator.domain := by
  intro potential inKernel
  exact (gradient.mem_kernel_iff potential).mp inKernel |>.choose

/-- A current in the closure of the represented range but not in the range is
the boundary-defect category of Definition 4.1. -/
def IsBoundaryDefect (gradient : StructuralGradient Potential Current)
    (current : Current) : Prop :=
  current ∈ gradient.range.topologicalClosure ∧
    current ∉ gradient.range

/-- The literal positive structural-gap witness from Theorem 4.3.  The
Poincare inequality is required only for domain elements orthogonal to the
ambient operator kernel. -/
structure PositiveStructuralGap
    (gradient : StructuralGradient Potential Current) where
  gamma : Real
  gamma_pos : 0 < gamma
  poincare : forall potential : gradient.Domain,
    (potential : Potential) ∈ (gradient.kernel)ᗮ ->
      ‖(potential : Potential)‖ ^ 2 ≤
        gamma⁻¹ * ‖gradient.operator potential‖ ^ 2

/-- A topological closed-range certificate for the exact operator image. -/
structure ClosedRangeCertificate
    (gradient : StructuralGradient Potential Current) : Prop where
  range_isClosed : IsClosed (gradient.range : Set Current)

namespace ClosedRangeCertificate

/-- Package the exact range as a Mathlib closed submodule. -/
def closedRange {gradient : StructuralGradient Potential Current}
    (certificate : ClosedRangeCertificate gradient) :
    ClosedSubmodule Real Current :=
  ⟨gradient.range, certificate.range_isClosed⟩

/-- A genuinely closed range has no closure-minus-range boundary defect. -/
theorem noBoundaryDefect {gradient : StructuralGradient Potential Current}
    (certificate : ClosedRangeCertificate gradient) (current : Current) :
    ¬ gradient.IsBoundaryDefect current := by
  intro defect
  apply defect.2
  have closure_eq : gradient.range.topologicalClosure = gradient.range :=
    certificate.range_isClosed.submodule_topologicalClosure_eq
  simpa [closure_eq] using defect.1

end ClosedRangeCertificate

/-- An explicit registration of the Hilbert-space closed-range criterion in
Theorem 4.3.  This is an analytic theorem contract: it does not derive a
continuum gap from finite rank or from a finite executable audit. -/
structure ClosedRangeCriterion
    (gradient : StructuralGradient Potential Current) : Prop where
  closedRange_iff_positiveGap :
    ClosedRangeCertificate gradient ↔
      Nonempty (PositiveStructuralGap gradient)

namespace ClosedRangeCriterion

/-- Use a registered closed-range criterion in the gap-to-closed direction. -/
theorem closedRangeOfGap {gradient : StructuralGradient Potential Current}
    (criterion : ClosedRangeCriterion gradient)
    (gap : PositiveStructuralGap gradient) :
    ClosedRangeCertificate gradient :=
  criterion.closedRange_iff_positiveGap.mpr ⟨gap⟩

/-- Use a registered closed-range criterion in the closed-to-gap direction. -/
theorem positiveGapOfClosedRange
    {gradient : StructuralGradient Potential Current}
    (criterion : ClosedRangeCriterion gradient)
    (closedRange : ClosedRangeCertificate gradient) :
    Nonempty (PositiveStructuralGap gradient) :=
  criterion.closedRange_iff_positiveGap.mp closedRange

end ClosedRangeCriterion

/-- Framework-owned directed decomposition generated from a topologically
closed exact range.  Its private constructor prevents applications from
supplying projection outputs or an unrelated represented subspace. -/
structure DirectedExhaustivenessCertificate
    (gradient : StructuralGradient Potential Current) where
  private mk ::
  representedRange : ClosedSubmodule Real Current
  representedRange_eq : representedRange.toSubmodule = gradient.range

namespace DirectedExhaustivenessCertificate

/-- Generate directed exhaustiveness from the exact closed-range proof. -/
def ofClosedRange {gradient : StructuralGradient Potential Current}
    (certificate : ClosedRangeCertificate gradient) :
    DirectedExhaustivenessCertificate gradient :=
  .mk certificate.closedRange rfl

/-- Recover the exact topological closed-range fact from a generated directed
exhaustiveness certificate. -/
theorem toClosedRange {gradient : StructuralGradient Potential Current}
    (certificate : DirectedExhaustivenessCertificate gradient) :
    ClosedRangeCertificate gradient := by
  constructor
  rw [← certificate.representedRange_eq]
  exact certificate.representedRange.isClosed'

/-- The represented structural-gradient component, computed by orthogonal
projection onto the exact closed range. -/
noncomputable def represented
    {gradient : StructuralGradient Potential Current}
    (certificate : DirectedExhaustivenessCertificate gradient)
    (current : Current) : Current :=
  certificate.representedRange.toSubmodule.starProjection current

/-- The orthogonal residual left by the represented projection. -/
noncomputable def residual
    {gradient : StructuralGradient Potential Current}
    (certificate : DirectedExhaustivenessCertificate gradient)
    (current : Current) : Current :=
  current - certificate.represented current

/-- The generated represented component lies in the exact operator range. -/
theorem represented_mem
    {gradient : StructuralGradient Potential Current}
    (certificate : DirectedExhaustivenessCertificate gradient)
    (current : Current) :
    certificate.represented current ∈ gradient.range := by
  rw [← certificate.representedRange_eq]
  exact Submodule.starProjection_apply_mem _ _

/-- The generated residual is orthogonal to every represented structural
gradient. -/
theorem residual_mem_orthogonal
    {gradient : StructuralGradient Potential Current}
    (certificate : DirectedExhaustivenessCertificate gradient)
    (current : Current) :
    certificate.residual current ∈ (gradient.range)ᗮ := by
  rw [← certificate.representedRange_eq]
  exact Submodule.sub_starProjection_mem_orthogonal current

/-- The represented and residual outputs reconstruct the input exactly. -/
theorem reconstruct
    {gradient : StructuralGradient Potential Current}
    (certificate : DirectedExhaustivenessCertificate gradient)
    (current : Current) :
    certificate.represented current + certificate.residual current =
      current := by
  simp [residual]

/-- Uniqueness of the represented component in an exact range/orthogonal
decomposition. -/
theorem represented_unique
    {gradient : StructuralGradient Potential Current}
    (certificate : DirectedExhaustivenessCertificate gradient)
    (current representedPart residualPart : Current)
    (representedPart_mem : representedPart ∈ gradient.range)
    (residualPart_mem : residualPart ∈ (gradient.range)ᗮ)
    (decomposition : current = representedPart + residualPart) :
    certificate.represented current = representedPart := by
  apply Submodule.eq_starProjection_of_mem_orthogonal'
  · rwa [certificate.representedRange_eq]
  · rwa [certificate.representedRange_eq]
  · exact decomposition

/-- Uniqueness of the orthogonal residual in an exact decomposition. -/
theorem residual_unique
    {gradient : StructuralGradient Potential Current}
    (certificate : DirectedExhaustivenessCertificate gradient)
    (current representedPart residualPart : Current)
    (representedPart_mem : representedPart ∈ gradient.range)
    (residualPart_mem : residualPart ∈ (gradient.range)ᗮ)
    (decomposition : current = representedPart + residualPart) :
    certificate.residual current = residualPart := by
  have represented_eq := certificate.represented_unique current
    representedPart residualPart representedPart_mem residualPart_mem
    decomposition
  rw [residual, represented_eq, decomposition]
  simp

end DirectedExhaustivenessCertificate

/-- Certificate form of Theorem 4.2: generated directed exhaustiveness exists
exactly when the represented structural-gradient range is closed. -/
theorem directedExhaustiveness_iff_closedRange
    (gradient : StructuralGradient Potential Current) :
    Nonempty (DirectedExhaustivenessCertificate gradient) ↔
      ClosedRangeCertificate gradient := by
  constructor
  · rintro ⟨certificate⟩
    exact certificate.toClosedRange
  · intro certificate
    exact ⟨DirectedExhaustivenessCertificate.ofClosedRange certificate⟩

end StructuralGradient

end Hypostructure.PDE

#print axioms Hypostructure.PDE.StructuralGradient.mem_kernel_iff
#print axioms Hypostructure.PDE.StructuralGradient.ClosedRangeCertificate.noBoundaryDefect
#print axioms Hypostructure.PDE.StructuralGradient.DirectedExhaustivenessCertificate.reconstruct
#print axioms Hypostructure.PDE.StructuralGradient.directedExhaustiveness_iff_closedRange
