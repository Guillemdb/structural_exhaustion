import Erdos64EG.Future.TypeBFanCompatiblePairAssignment
import Erdos64EG.Shared.CT10P13LabelAlgebra
import StructuralExhaustion.Graph.FanCertificateRequirement

namespace Erdos64EG.Internal.TypeBFanCertificateRequirement

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

open TypeBEntryRouting

/-- The next marked-fan datum required on a ready compatible pair. Its port is
the first port of the actual center schedule, not one selected from a label
universe. This structure asserts no absence or failure. -/
structure CertificateRequirement
    (residual : VerifiedNode64Residual ctx)
    (ready : TypeBFanCompatiblePairAssignment.ReadyPair residual) where
  request : Graph.FanCertificateRequirement.FirstLabelRequest ctx.G.object
    residual.highSurplus.center residual.highSurplus.high

/-- Exact completion type for the current request. Producing one value does
not yet supply labels on the remaining ports or pairwise compatibility. -/
abbrev Completion
    {residual : VerifiedNode64Residual ctx}
    {ready : TypeBFanCompatiblePairAssignment.ReadyPair residual}
    (_requirement : CertificateRequirement residual ready) :=
  {label : P13Label // P13Legal label}

/-- Expose the first required local certificate clause. No label assignment is
enumerated and no marked fan is assumed. -/
def labelRequired
    (residual : VerifiedNode64Residual ctx)
    (ready : TypeBFanCompatiblePairAssignment.ReadyPair residual) :
    CertificateRequirement residual ready where
  request := Graph.FanCertificateRequirement.firstLabelRequest ctx.G.object
    residual.highSurplus.center residual.highSurplus.high

theorem labelRequired_port_index
    (residual : VerifiedNode64Residual ctx)
    (ready : TypeBFanCompatiblePairAssignment.ReadyPair residual) :
    (labelRequired residual ready).request.port.1 = 0 :=
  Graph.FanCertificateRequirement.firstLabelRequest_port_index ctx.G.object
    residual.highSurplus.center residual.highSurplus.high

/-- All non-ready branches are copied with their complete predecessor payload.
Only the ready constructor reaches the still-white certificate requirement. -/
inductive Route (residual : VerifiedNode64Residual ctx) where
  | degreeFour
      (result : TypeBFanCompatiblePairAssignment.DegreeFourResidual residual)
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
      (requirement : CertificateRequirement residual ready)

noncomputable def route (residual : VerifiedNode64Residual ctx) : Route residual := by
  cases TypeBFanCompatiblePairAssignment.route residual with
  | degreeFour result => exact .degreeFour result
  | triangular result => exact .triangular result
  | firstPortMissing stage degreeAboveFour first second compatible missing =>
      exact .firstPortMissing stage degreeAboveFour first second compatible missing
  | secondPortMissing stage degreeAboveFour first second compatible firstClosed missing =>
      exact .secondPortMissing stage degreeAboveFour first second compatible
        firstClosed missing
  | ready stage ready =>
      exact .certificateRequired stage ready (labelRequired residual ready)

def additionalChecks : Nat := Graph.FanCertificateRequirement.visibleChecks

theorem additionalChecks_eq_zero : additionalChecks = 0 := rfl

end Erdos64EG.Internal.TypeBFanCertificateRequirement
