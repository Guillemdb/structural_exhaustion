import Erdos64EG.TypeBSupportScope
import StructuralExhaustion.Graph.DegreeFourFanLedger
import StructuralExhaustion.Graph.FiniteCertificateMarking
import StructuralExhaustion.Routes.Accumulated

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
  Graph.DegreeFourFanLedger.VerifiedExecutionStage ctx.G.object center.1
    (scope.center_high center)
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    scope.Assigned scope.assignedDecidable ctx.toBranchContext
    (scope.degree_eq_four_of_noHigher noHigher center)
    ((Graph.DegreeFourFanLedger.profile ctx.G.object center.1
      (scope.center_high center)
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      scope.Assigned scope.assignedDecidable).run ctx.toBranchContext)

/-- CT14 executes independently at every centre on the exact degree-four
branch.  Each execution scans only that centre's incident ports. -/
def degreeFourFanFacts (noHigher : scope.NoHigherCenter)
    (center : scope.Center) : scope.DegreeFourFanStage noHigher center :=
  Graph.DegreeFourFanLedger.verifiedExecutionStage ctx.G.object center.1
    (scope.center_high center)
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    scope.Assigned scope.assignedDecidable ctx.toBranchContext
    (scope.degree_eq_four_of_noHigher noHigher center) _ rfl

/-- Generic assigned-certificate scan instantiated on the exact derived
high-centre schedule. -/
noncomputable def CertificateMarkingProfile :
    Graph.FiniteCertificateMarking.Profile scope.Center where
  sites := scope.centers
  Certificate := scope.CertificateAt
  assigned := scope.certificateAt

abbrev CertificateMarkingStage :=
  scope.CertificateMarkingProfile.VerifiedExecutionStage ctx.toBranchContext
    (fun center => CT14.run
      (scope.CertificateMarkingProfile.capability PackedProblem.{u} center)
      ctx.toBranchContext
      (scope.CertificateMarkingProfile.input ctx.toBranchContext center))

noncomputable def certificateMarkingFacts : scope.CertificateMarkingStage :=
  scope.CertificateMarkingProfile.verifiedExecutionStage ctx.toBranchContext
    (fun center => CT14.run
      (scope.CertificateMarkingProfile.capability PackedProblem.{u} center)
      ctx.toBranchContext
      (scope.CertificateMarkingProfile.input ctx.toBranchContext center))
    (fun _center => rfl)

/-- The yes-branch of node `[80]`, retaining the exact node `[79]` ledger and
the assigned marked fan consumed by node `[81]`. -/
structure CertificateMarkedDegreeFourCenter (noHigher : scope.NoHigherCenter)
    (center : scope.Center) : Type u where
  ledger : scope.DegreeFourFanStage noHigher center
  marking : scope.CertificateMarkingProfile.Marked ctx.toBranchContext center
    (CT14.run
      (scope.CertificateMarkingProfile.capability PackedProblem.{u} center)
      ctx.toBranchContext
      (scope.CertificateMarkingProfile.input ctx.toBranchContext center))

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
    (CT14.run
      (scope.CertificateMarkingProfile.capability PackedProblem.{u} center)
      ctx.toBranchContext
      (scope.CertificateMarkingProfile.input ctx.toBranchContext center))

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
  cases scope.CertificateMarkingProfile.decideExecution ctx.toBranchContext
      center _ rfl with
  | marked marked =>
      exact Or.inl ⟨⟨scope.degreeFourFanFacts noHigher center, marked⟩⟩
  | residual residual =>
      exact Or.inr ⟨scope.degreeFourFanFacts noHigher center, residual⟩

/-- The number of primitive checks in the complete degree-four family:
`4n+13` for the port ledger and six for certificate presence at each actual
center. -/
noncomputable def degreeFourCertificateChecks : Nat :=
  scope.highCenters.card * (4 * ctx.G.object.input.vertices.card + 19)

theorem highCenters_card_le_vertexCount :
    scope.highCenters.card ≤ ctx.G.object.input.vertices.card := by
  exact Core.Enumeration.finset_card_le
    ctx.G.object.input.vertices scope.highCenters

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
      fun center => scope.degreeFourFanFacts noHigher center,
      scope.certificateMarkingFacts,
      scope.certificateMarked_or_fanCertificateResidual noHigher⟩

end TypeBSupportScope

/-- One proof-indexed local request on the degree-four branch. -/
structure DegreeFourFanRequest
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    where
  scope : TypeBSupportScope ctx
  noHigher : scope.NoHigherCenter
  center : scope.Center

namespace DegreeFourFanRequest

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (request : DegreeFourFanRequest ctx)

noncomputable def fanProfile :=
  Graph.DegreeFourFanLedger.profile ctx.G.object request.center.1
    (request.scope.center_high request.center)
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    request.scope.Assigned request.scope.assignedDecidable

end DegreeFourFanRequest

noncomputable def degreeFourFanTarget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (request : DegreeFourFanRequest ctx) :=
  (request.fanProfile.capability PackedProblem.{u}).executableInterface

noncomputable def degreeFourFanAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (request : DegreeFourFanRequest ctx) :
    Routes.Accumulated.Adapter Unit (degreeFourFanTarget ctx request) where
  targetContext := fun _source => ctx.toBranchContext
  trigger := fun _source => ⟨⟩

noncomputable def degreeFourFanPointwiseAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Routes.Accumulated.PointwiseAdapter .ct9 .ct14
      (DegreeFourFanRequest ctx) (VerifiedFanLabelPackingPrefix ctx) where
  Source := fun _request => Unit
  target := degreeFourFanTarget ctx
  adapter := degreeFourFanAdapter ctx
  current := fun _request _ledger => ()

noncomputable def degreeFourFanTransitionFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Routes.Accumulated.pointwiseFamily (degreeFourFanPointwiseAdapter ctx)

abbrev DegreeFourFanTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx)) :=
  Routes.Accumulated.PointwiseOutputLedger
    (degreeFourFanPointwiseAdapter ctx) source

noncomputable def degreeFourFanTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx)) :=
  Routes.Accumulated.advancePointwise (degreeFourFanPointwiseAdapter ctx) source

noncomputable def degreeFourFanLocalResult
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx)}
    (execution : DegreeFourFanTransitionLedger ctx source)
    (request : DegreeFourFanRequest ctx) :=
  (execution.localStage request).targetResult

@[simp] theorem degreeFourFanLocalResult_transition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx))
    (request : DegreeFourFanRequest ctx) :
    degreeFourFanLocalResult ctx (degreeFourFanTransitionStage ctx source).output
        request =
      request.fanProfile.run ctx.toBranchContext :=
  rfl

structure DegreeFourFanExecutionFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx)}
    (execution : DegreeFourFanTransitionLedger ctx source) : Prop where
  exactRun : ∀ request : DegreeFourFanRequest ctx,
    degreeFourFanLocalResult ctx execution request =
      request.fanProfile.run ctx.toBranchContext
  verified : ∀ request : DegreeFourFanRequest ctx,
    request.scope.DegreeFourFanStage request.noHigher request.center

abbrev DegreeFourFanLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx)) :=
  Core.Routing.LedgerExtension (DegreeFourFanTransitionLedger ctx source)
    (DegreeFourFanExecutionFacts ctx)

noncomputable def degreeFourFanLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx)) :
    Core.Routing.ResidualStage .ct14 (DegreeFourFanLedger ctx source) := by
  let execution := degreeFourFanTransitionStage ctx source
  let executionStage : Core.Routing.ResidualStage .ct14
      (DegreeFourFanTransitionLedger ctx source) :=
    execution
  exact executionStage.extend {
    exactRun := fun request => by
      change degreeFourFanLocalResult ctx executionStage.output request = _
      rw [degreeFourFanLocalResult_transition]
    verified := fun request =>
      request.scope.degreeFourFanFacts request.noHigher request.center
  }

noncomputable def certificateMarkingTarget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (request : DegreeFourFanRequest ctx) :=
  (request.scope.CertificateMarkingProfile.capability PackedProblem.{u}
    request.center).executableInterface

noncomputable def certificateMarkingAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (request : DegreeFourFanRequest ctx) :
    Routes.Accumulated.Adapter
      (request.scope.DegreeFourFanStage request.noHigher request.center)
      (certificateMarkingTarget ctx request) where
  targetContext := fun _source => ctx.toBranchContext
  trigger := fun _source => ⟨⟩

noncomputable def certificateMarkingPointwiseAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx)) :
    Routes.Accumulated.PointwiseAdapter .ct14 .ct14
      (DegreeFourFanRequest ctx) (DegreeFourFanLedger ctx source) where
  Source := fun request =>
    request.scope.DegreeFourFanStage request.noHigher request.center
  target := certificateMarkingTarget ctx
  adapter := certificateMarkingAdapter ctx
  current := fun request ledger => ledger.added.verified request

noncomputable def certificateMarkingTransitionFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx)) :=
  Routes.Accumulated.pointwiseFamily
    (certificateMarkingPointwiseAdapter ctx source)

abbrev CertificateMarkingTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx))
    (fanStage : Core.Routing.ResidualStage .ct14
      (DegreeFourFanLedger ctx source)) :=
  Routes.Accumulated.PointwiseOutputLedger
    (certificateMarkingPointwiseAdapter ctx source) fanStage

noncomputable def certificateMarkingTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx))
    (fanStage : Core.Routing.ResidualStage .ct14
      (DegreeFourFanLedger ctx source)) :=
  Routes.Accumulated.advancePointwise
    (certificateMarkingPointwiseAdapter ctx source) fanStage

noncomputable def certificateMarkingLocalResult
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx)}
    {fanStage : Core.Routing.ResidualStage .ct14
      (DegreeFourFanLedger ctx source)}
    (execution : CertificateMarkingTransitionLedger ctx source fanStage)
    (request : DegreeFourFanRequest ctx) :=
  (execution.localStage request).targetResult

@[simp] theorem certificateMarkingLocalResult_transition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx))
    (fanStage : Core.Routing.ResidualStage .ct14
      (DegreeFourFanLedger ctx source))
    (request : DegreeFourFanRequest ctx) :
    certificateMarkingLocalResult ctx
        (certificateMarkingTransitionStage ctx source fanStage).output request =
      CT14.run
        (request.scope.CertificateMarkingProfile.capability PackedProblem.{u}
          request.center)
        ctx.toBranchContext
        (request.scope.CertificateMarkingProfile.input ctx.toBranchContext
          request.center) :=
  rfl

structure DegreeFourCertificateFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx)}
    {fanStage : Core.Routing.ResidualStage .ct14
      (DegreeFourFanLedger ctx source)}
    (execution : CertificateMarkingTransitionLedger ctx source fanStage) : Prop where
  exactRun : ∀ request : DegreeFourFanRequest ctx,
    certificateMarkingLocalResult ctx execution request =
      CT14.run
        (request.scope.CertificateMarkingProfile.capability PackedProblem.{u}
          request.center)
        ctx.toBranchContext
        (request.scope.CertificateMarkingProfile.input ctx.toBranchContext
          request.center)
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

abbrev DegreeFourTypeBLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx))
    (fanStage : Core.Routing.ResidualStage .ct14
      (DegreeFourFanLedger ctx source)) :=
  Core.Routing.LedgerExtension
    (CertificateMarkingTransitionLedger ctx source fanStage)
    (DegreeFourCertificateFacts ctx)

noncomputable def degreeFourTypeBLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : Core.Routing.ResidualStage .ct9
      (VerifiedFanLabelPackingPrefix ctx)) :
    let fanStage := degreeFourFanLedgerStage ctx source
    Core.Routing.ResidualStage .ct14
      (DegreeFourTypeBLedger ctx source fanStage) := by
  let fanStage := degreeFourFanLedgerStage ctx source
  let execution := certificateMarkingTransitionStage ctx source fanStage
  let executionStage : Core.Routing.ResidualStage .ct14
      (CertificateMarkingTransitionLedger ctx source fanStage) :=
    execution
  exact executionStage.extend {
    exactRun := fun request => by
      change certificateMarkingLocalResult ctx executionStage.output request = _
      rw [certificateMarkingLocalResult_transition]
    localFlow := fun scope => scope.higher_or_degreeFour_certificateFlow
    polynomial := fun scope => scope.degreeFourCertificateChecks_polynomial
  }

/-- Verified node `[80]` endpoint with two literal accumulated transitions:
CT9→CT14 for the degree-four fan ledger and CT14→CT14 for assigned
certificate marking. -/
abbrev VerifiedDegreeFourTypeBLedgerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedFanLabelPackingPrefix ctx)
    (fun previous =>
      let source := Core.Routing.ResidualStage.exact (tactic := .ct9) previous
      let fanStage := degreeFourFanLedgerStage ctx source
      Core.Routing.ResidualStage .ct14
        (DegreeFourTypeBLedger ctx source fanStage))

noncomputable def verifiedDegreeFourTypeBLedgerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedFanLabelPackingPrefix ctx) :
    VerifiedDegreeFourTypeBLedgerPrefix ctx :=
  ⟨previous, degreeFourTypeBLedgerStage ctx
    (Core.Routing.ResidualStage.exact previous)⟩

theorem exists_verifiedDegreeFourTypeBLedgerPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedDegreeFourTypeBLedgerPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedFanLabelPackingPrefix object baseline avoids
  exact ⟨ctx, verifiedDegreeFourTypeBLedgerPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
