import Erdos64EG.TypeBFanCertificateRequirement
import Erdos64EG.CT9FanLabelPacking
import StructuralExhaustion.Graph.DegreeFourFanLedger
import StructuralExhaustion.Routes.Accumulated

namespace Erdos64EG.Internal.TypeBDegreeFourLedgerConnector

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

open TypeBEntryRouting

noncomputable def profile
    (residual : VerifiedNode64Residual ctx)
    (_degreeFour : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual) :=
  Graph.DegreeFourFanLedger.profile ctx.G.object
    residual.highSurplus.center residual.highSurplus.high
    (TypeBFanShoulderIncidenceCoordinates.profile residual).deletionCritical
    (TypeBFanWholePortAssignment.Assigned residual)
    (Graph.InducedCoreFanAssignment.assignedDecidable ctx.G.object
      residual.support.core)

noncomputable def target
    (residual : VerifiedNode64Residual ctx)
    (degreeFour : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual) :=
  ((profile residual degreeFour).capability PackedProblem.{u}).executableInterface

noncomputable def adapter
    (residual : VerifiedNode64Residual ctx)
    (degreeFour : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual) :
    Routes.Accumulated.Adapter (VerifiedNode64Residual ctx)
      (target residual degreeFour) where
  targetContext := fun _source => ctx.toBranchContext
  trigger := fun _source => ⟨⟩

def sourceStage (residual : VerifiedNode64Residual ctx) :
    Core.Routing.ResidualStage .ct6 (VerifiedNode64Residual ctx) :=
  Core.Routing.ResidualStage.exact residual

noncomputable def transitionStage
    (residual : VerifiedNode64Residual ctx)
    (degreeFour : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual) :=
  Routes.Accumulated.advanceCurrent (target residual degreeFour)
    (adapter residual degreeFour) (sourceStage residual)

abbrev TransitionLedger
    (residual : VerifiedNode64Residual ctx)
    (degreeFour : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual) :=
  Routes.Accumulated.OutputLedger (sourceTactic := .ct6)
    (target residual degreeFour) (adapter residual degreeFour)
    (sourceStage residual)

structure LedgerFacts
    (residual : VerifiedNode64Residual ctx)
    (degreeFour : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual)
    (execution : TransitionLedger residual degreeFour) : Prop where
  verified : Graph.DegreeFourFanLedger.VerifiedExecutionStage ctx.G.object
    residual.highSurplus.center residual.highSurplus.high
    (TypeBFanShoulderIncidenceCoordinates.profile residual).deletionCritical
    (TypeBFanWholePortAssignment.Assigned residual)
    (Graph.InducedCoreFanAssignment.assignedDecidable ctx.G.object
      residual.support.core)
    ctx.toBranchContext degreeFour.degreeFour execution.targetResult

abbrev Ledger
    (residual : VerifiedNode64Residual ctx)
    (degreeFour : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual) :=
  Core.Routing.LedgerExtension (TransitionLedger residual degreeFour)
    (LedgerFacts residual degreeFour)

abbrev LedgerStage
    (residual : VerifiedNode64Residual ctx)
    (degreeFour : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual) :=
  Core.Routing.ResidualStage .ct14 (Ledger residual degreeFour)

/-- Execute node `[79]` on the actual four incident ports and the assignment
predicate already derived from node `[64]`. -/
noncomputable def ledgerStage
    (residual : VerifiedNode64Residual ctx)
    (degreeFour : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual) :
    LedgerStage residual degreeFour := by
  let execution := transitionStage residual degreeFour
  exact execution.ledgerStage.extend {
    verified := Graph.DegreeFourFanLedger.verifiedExecutionStage ctx.G.object
      residual.highSurplus.center residual.highSurplus.high
      (TypeBFanShoulderIncidenceCoordinates.profile residual).deletionCritical
      (TypeBFanWholePortAssignment.Assigned residual)
      (Graph.InducedCoreFanAssignment.assignedDecidable ctx.G.object
        residual.support.core)
      ctx.toBranchContext degreeFour.degreeFour execution.targetResult rfl
  }

/-- Honest node-`[80]` frontier. The current ancestry supplies neither an
assigned marked fan nor a proof that none was assigned. -/
structure CertificateMarkingRequirement
    (residual : VerifiedNode64Residual ctx)
    (degreeFour : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual)
    (_ledger : LedgerStage residual degreeFour) where
  firstLabel : Graph.FanCertificateRequirement.FirstLabelRequest ctx.G.object
    residual.highSurplus.center residual.highSurplus.high

/-- Exact future node-`[80]` completion type. The unmarked branch must prove
nonexistence of an exact-center marked fan; it cannot be produced by writing
`none`. -/
inductive MarkingDecision
    (residual : VerifiedNode64Residual ctx) : Type u where
  | marked
      (fan : MarkedFan ctx)
      (centerExact : fan.center = residual.highSurplus.center)
  | unmarked
      (absent : ¬∃ fan : MarkedFan ctx,
        fan.center = residual.highSurplus.center)

abbrev MarkingCompletion
    {residual : VerifiedNode64Residual ctx}
    {degreeFour : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual}
    {ledger : LedgerStage residual degreeFour}
    (_requirement : CertificateMarkingRequirement residual degreeFour ledger) :=
  MarkingDecision residual

def markingRequired
    (residual : VerifiedNode64Residual ctx)
    (degreeFour : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual)
    (ledger : LedgerStage residual degreeFour) :
    CertificateMarkingRequirement residual degreeFour ledger where
  firstLabel := Graph.FanCertificateRequirement.firstLabelRequest ctx.G.object
    residual.highSurplus.center residual.highSurplus.high

/-- Advance only the exact degree-four branch. Every degree-above-four route
is retained with the same predecessor payload. -/
inductive Route (residual : VerifiedNode64Residual ctx) where
  | degreeFour
      (source : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual)
      (ledger : LedgerStage residual source)
      (requirement : CertificateMarkingRequirement residual source ledger)
  | triangular
      (result : TypeBFanCompatiblePairAssignment.TriangularResidual residual)
  | firstPortMissing
      (stage : HighCenterPortStage ctx residual.highSurplus.center
        residual.highSurplus.high)
      (degreeAboveFour : 4 < ctx.G.object.degree residual.highSurplus.center)
      (first second : TypeBFanCompatiblePairAssignment.OpenPort residual)
      (compatible : Graph.FanClosedPort.CompatiblePair
        (TypeBFanCompatiblePairAssignment.Profile residual).centerHigh
        (TypeBFanCompatiblePairAssignment.Profile residual).deletionCritical
        first second)
      (missing : TypeBFanCompatiblePairAssignment.MissingOpenPort residual first)
  | secondPortMissing
      (stage : HighCenterPortStage ctx residual.highSurplus.center
        residual.highSurplus.high)
      (degreeAboveFour : 4 < ctx.G.object.degree residual.highSurplus.center)
      (first second : TypeBFanCompatiblePairAssignment.OpenPort residual)
      (compatible : Graph.FanClosedPort.CompatiblePair
        (TypeBFanCompatiblePairAssignment.Profile residual).centerHigh
        (TypeBFanCompatiblePairAssignment.Profile residual).deletionCritical
        first second)
      (firstClosed : TypeBFanCompatiblePairAssignment.ClosedOpenPort residual first)
      (missing : TypeBFanCompatiblePairAssignment.MissingOpenPort residual second)
  | certificateRequired
      (stage : HighCenterPortStage ctx residual.highSurplus.center
        residual.highSurplus.high)
      (ready : TypeBFanCompatiblePairAssignment.ReadyPair residual)
      (requirement : TypeBFanCertificateRequirement.CertificateRequirement
        residual ready)

noncomputable def route (residual : VerifiedNode64Residual ctx) : Route residual := by
  cases TypeBFanCertificateRequirement.route residual with
  | degreeFour source =>
      let ledger := ledgerStage residual source
      exact .degreeFour source ledger (markingRequired residual source ledger)
  | triangular result => exact .triangular result
  | firstPortMissing stage degreeAboveFour first second compatible missing =>
      exact .firstPortMissing stage degreeAboveFour first second compatible missing
  | secondPortMissing stage degreeAboveFour first second compatible firstClosed missing =>
      exact .secondPortMissing stage degreeAboveFour first second compatible
        firstClosed missing
  | certificateRequired stage ready requirement =>
      exact .certificateRequired stage ready requirement

def degreeFourChecks (residual : VerifiedNode64Residual ctx) : Nat :=
  Graph.DegreeFourFanLedger.checks ctx.G.object residual.highSurplus.center

theorem degreeFourChecks_polynomial
    (residual : VerifiedNode64Residual ctx)
    (degreeFour : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual) :
    degreeFourChecks residual ≤ 17 * (ctx.G.object.input.vertices.card + 1) :=
  (ledgerStage residual degreeFour).output.added.verified.polynomial

end Erdos64EG.Internal.TypeBDegreeFourLedgerConnector
