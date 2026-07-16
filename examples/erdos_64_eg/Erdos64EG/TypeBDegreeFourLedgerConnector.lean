import Erdos64EG.TypeBFanCertificateRequirement
import Erdos64EG.CT9FanLabelPacking
import StructuralExhaustion.Graph.DegreeFourFanLedger

namespace Erdos64EG.Internal.TypeBDegreeFourLedgerConnector

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

open TypeBEntryRouting

abbrev LedgerStage
    (residual : VerifiedNode64Residual ctx)
    (degreeFour : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual) :=
  Graph.DegreeFourFanLedger.VerifiedStage ctx.G.object
    residual.highSurplus.center residual.highSurplus.high
    (TypeBFanShoulderIncidenceCoordinates.profile residual).deletionCritical
    (TypeBFanWholePortAssignment.Assigned residual)
    (Graph.InducedCoreFanAssignment.assignedDecidable ctx.G.object
      residual.support.core)
    ctx.toBranchContext degreeFour.degreeFour

/-- Execute node `[79]` on the actual four incident ports and the assignment
predicate already derived from node `[64]`. -/
noncomputable def ledgerStage
    (residual : VerifiedNode64Residual ctx)
    (degreeFour : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual) :
    LedgerStage residual degreeFour :=
  Graph.DegreeFourFanLedger.verifiedStage ctx.G.object
    residual.highSurplus.center residual.highSurplus.high
    (TypeBFanShoulderIncidenceCoordinates.profile residual).deletionCritical
    (TypeBFanWholePortAssignment.Assigned residual)
    (Graph.InducedCoreFanAssignment.assignedDecidable ctx.G.object
      residual.support.core)
    ctx.toBranchContext degreeFour.degreeFour

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
  (ledgerStage residual degreeFour).polynomial

end Erdos64EG.Internal.TypeBDegreeFourLedgerConnector
