import Erdos64EG.TypeBSupportScope
import StructuralExhaustion.Graph.DegreeFourFanLedger
import StructuralExhaustion.Graph.FiniteCertificateMarking

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Local degree-four Type B accounting and certificate split

This stage follows diagram nodes `[68]`, `[78]`, `[79]`, and `[80]` without
entering the later B1/B2 decision at `[81]`.  It first tests the finite
high-centre schedule of a Type B support for a centre of degree greater than
four.  Only the negative branch is converted into the pointwise equality
`degree = 4`.  CT14 then scans the four incident ports at each such centre and
computes the exact local ledger.

For node `[80]`, the framework independently audits the optional
fan-certificate field already present in the assigned support data.  A marked
centre is routed forward with its `MarkedFan`; an unmarked centre is retained
with the literal absence equation for the fan-mass route at `[84]`.  This is
not the later predicate saying that a verified B1/B2 local entry exists.  No
near-cubic spine or global surplus estimate is an input to this stage.
-/

namespace TypeBSupportScope

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (scope : TypeBSupportScope ctx)

/-- The literal yes-branch at diagram node `[68]`. -/
def HasHigherCenter : Prop :=
  ∃ center : scope.Center, 4 < ctx.G.object.degree center.1

/-- The literal no-branch at diagram node `[68]`. -/
def NoHigherCenter : Prop :=
  ∀ center : scope.Center, ¬4 < ctx.G.object.degree center.1

theorem higher_or_noHigher : scope.HasHigherCenter ∨ scope.NoHigherCenter := by
  classical
  rcases Classical.em scope.HasHigherCenter with higher | noHigher
  · exact Or.inl higher
  · right
    intro center higher
    exact noHigher ⟨center, higher⟩

/-- The no-branch, together with the definition of the high-centre schedule,
is exactly the degree-four branch at node `[78]`. -/
theorem degree_eq_four_of_noHigher (noHigher : scope.NoHigherCenter)
    (center : scope.Center) :
    ctx.G.object.degree center.1 = 4 := by
  have high := scope.center_high center
  have notHigher := noHigher center
  omega

abbrev DegreeFourFanStage (noHigher : scope.NoHigherCenter)
    (center : scope.Center) :=
  Graph.DegreeFourFanLedger.VerifiedStage ctx.G.object center.1
    (scope.center_high center)
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    scope.Assigned scope.assignedDecidable ctx.toBranchContext
    (scope.degree_eq_four_of_noHigher noHigher center)

/-- CT14 executes independently at every centre on the exact degree-four
branch.  Each execution scans only that centre's incident ports. -/
def degreeFourFanStage (noHigher : scope.NoHigherCenter)
    (center : scope.Center) : scope.DegreeFourFanStage noHigher center :=
  Graph.DegreeFourFanLedger.verifiedStage ctx.G.object center.1
    (scope.center_high center)
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    scope.Assigned scope.assignedDecidable ctx.toBranchContext
    (scope.degree_eq_four_of_noHigher noHigher center)

/-- Generic assigned-certificate scan instantiated on the exact derived
high-centre schedule. -/
noncomputable def CertificateMarkingProfile :
    Graph.FiniteCertificateMarking.Profile scope.Center where
  sites := scope.centers
  Certificate := scope.CertificateAt
  assigned := scope.certificateAt

abbrev CertificateMarkingStage :=
  scope.CertificateMarkingProfile.VerifiedStage ctx.toBranchContext

noncomputable def certificateMarkingStage : scope.CertificateMarkingStage :=
  scope.CertificateMarkingProfile.verifiedStage ctx.toBranchContext

/-- The yes-branch of node `[80]`, retaining the exact node `[79]` ledger and
the assigned marked fan consumed by node `[81]`. -/
structure CertificateMarkedDegreeFourCenter (noHigher : scope.NoHigherCenter)
    (center : scope.Center) : Type u where
  ledger : scope.DegreeFourFanStage noHigher center
  marking : scope.CertificateMarkingProfile.Marked ctx.toBranchContext center

namespace CertificateMarkedDegreeFourCenter

variable {scope} {noHigher : scope.NoHigherCenter} {center : scope.Center}

def fan (marked : scope.CertificateMarkedDegreeFourCenter noHigher center) :
    MarkedFan ctx :=
  marked.marking.certificate.1

theorem fan_center
    (marked : scope.CertificateMarkedDegreeFourCenter noHigher center) :
    marked.fan.center = center.1 :=
  marked.marking.certificate.2

end CertificateMarkedDegreeFourCenter

/-- The no-branch of node `[80]`, retaining the same actual degree-four center
and the exact absence of an assigned certificate for the later node `[84]`
fan-mass route. -/
structure FanCertificateResidualCenter (noHigher : scope.NoHigherCenter)
    (center : scope.Center) : Prop where
  ledger : scope.DegreeFourFanStage noHigher center
  residual : scope.CertificateMarkingProfile.Residual ctx.toBranchContext center

namespace FanCertificateResidualCenter

variable {scope} {noHigher : scope.NoHigherCenter} {center : scope.Center}

theorem assignedMarkedFan_eq_none
    (residual : scope.FanCertificateResidualCenter noHigher center) :
    scope.assignedMarkedFan center.1 = none :=
  (scope.certificateAt_eq_none_iff center).mp residual.residual.missing

end FanCertificateResidualCenter

/-- Complete assigned-certificate split at one actual degree-four center. -/
theorem certificateMarked_or_fanCertificateResidual
    (noHigher : scope.NoHigherCenter) (center : scope.Center) :
    Nonempty (scope.CertificateMarkedDegreeFourCenter noHigher center) ∨
      scope.FanCertificateResidualCenter noHigher center := by
  cases scope.CertificateMarkingProfile.decide ctx.toBranchContext center with
  | marked marked =>
      exact Or.inl ⟨⟨scope.degreeFourFanStage noHigher center, marked⟩⟩
  | residual residual =>
      exact Or.inr ⟨scope.degreeFourFanStage noHigher center, residual⟩

/-- The number of primitive checks in the complete degree-four family:
`4n+13` for the port ledger and six for certificate presence at each actual
center. -/
noncomputable def degreeFourCertificateChecks : Nat :=
  scope.highCenters.card * (4 * ctx.G.object.input.vertices.card + 19)

theorem highCenters_card_le_vertexCount :
    scope.highCenters.card ≤ ctx.G.object.input.vertices.card := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : Fintype ctx.G.Vertex :=
    @FinEnum.instFintype _ ctx.G.object.input.vertices
  simpa [FinEnum.card_eq_fintypeCard] using
    Finset.card_le_univ scope.highCenters

theorem degreeFourCertificateChecks_polynomial :
    scope.degreeFourCertificateChecks ≤
      23 * (ctx.G.object.input.vertices.card + 1) ^ 2 := by
  have centerBound := scope.highCenters_card_le_vertexCount
  have localBound :
      4 * ctx.G.object.input.vertices.card + 19 ≤
        23 * (ctx.G.object.input.vertices.card + 1) := by omega
  calc
    scope.degreeFourCertificateChecks ≤
        ctx.G.object.input.vertices.card *
          (23 * (ctx.G.object.input.vertices.card + 1)) := by
      exact Nat.mul_le_mul centerBound localBound
    _ ≤ 23 * (ctx.G.object.input.vertices.card + 1) ^ 2 := by nlinarith

/-- Exact local flow through nodes `[68]`, `[78]`, `[79]`, and `[80]`.  The
first disjunct is the degree-greater-than-four branch.  On the degree-four
branch, every actual center keeps its independent CT14 port ledger and then
takes the assigned-certificate yes/no split. -/
theorem higher_or_degreeFour_certificateFlow :
    scope.HasHigherCenter ∨
      ∃ noHigher : scope.NoHigherCenter,
        (∀ center : scope.Center,
          scope.DegreeFourFanStage noHigher center) ∧
        scope.CertificateMarkingStage ∧
        (∀ center : scope.Center,
          Nonempty (scope.CertificateMarkedDegreeFourCenter noHigher center) ∨
            scope.FanCertificateResidualCenter noHigher center) := by
  rcases scope.higher_or_noHigher with higher | noHigher
  · exact Or.inl higher
  · exact Or.inr ⟨noHigher,
      fun center => scope.degreeFourFanStage noHigher center,
      scope.certificateMarkingStage,
      scope.certificateMarked_or_fanCertificateResidual noHigher⟩

end TypeBSupportScope

/-- Verified node `[80]` endpoint.  It depends only on the earlier conditional
fan-certificate interface and the same minimal-counterexample graph; it does
not consume the later B1/B2 resolution theorem. -/
structure VerifiedDegreeFourTypeBLedgerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedFanLabelPackingPrefix ctx
  localFlow : ∀ scope : TypeBSupportScope ctx,
    scope.HasHigherCenter ∨
      ∃ noHigher : scope.NoHigherCenter,
        (∀ center : scope.Center,
          scope.DegreeFourFanStage noHigher center) ∧
        scope.CertificateMarkingStage ∧
        (∀ center : scope.Center,
          Nonempty (scope.CertificateMarkedDegreeFourCenter noHigher center) ∨
            scope.FanCertificateResidualCenter noHigher center)
  polynomial : ∀ scope : TypeBSupportScope ctx,
    scope.degreeFourCertificateChecks ≤
      23 * (ctx.G.object.input.vertices.card + 1) ^ 2

noncomputable def verifiedDegreeFourTypeBLedgerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedFanLabelPackingPrefix ctx) :
    VerifiedDegreeFourTypeBLedgerPrefix ctx where
  previous := previous
  localFlow := fun scope => scope.higher_or_degreeFour_certificateFlow
  polynomial := fun scope => scope.degreeFourCertificateChecks_polynomial

theorem exists_verifiedDegreeFourTypeBLedgerPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedDegreeFourTypeBLedgerPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedFanLabelPackingPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedDegreeFourTypeBLedgerPrefix ctx previous⟩

end Erdos64EG.Internal
