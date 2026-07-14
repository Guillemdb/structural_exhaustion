import Erdos64EG.CT9MarkedFanLabelPacking
import StructuralExhaustion.Graph.AssignedFanCharge
import StructuralExhaustion.Graph.CertificateClosedFanCharge

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT14: certificate-closed fan charge

This file completes the charge clause of `lem:fan-certificate`. The
application supplies the manuscript's cubic-closed predicate on actual fan
ports and the defining nonpositive-deficit inequality `4c+k≤11`. The graph
framework computes `c`, executes CT14, and derives the exact quarter-charge
lower bound `11-k-4c≥0`.
-/

def markedFanChargeProfile
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (fan : MarkedFan ctx)
    (centerHigh : 4 ≤ ctx.G.object.degree fan.center)
    (Assigned : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex → Prop)
    (assignedDecidable : ∀ carrier, Decidable (Assigned carrier)) :
    Graph.CertificateClosedFanCharge.Profile
      (Graph.HighCenterPort.Port ctx.G.object fan.center) where
  members := Graph.HighCenterPort.ports ctx.G.object fan.center
  Closed := Graph.AssignedFanCharge.CubicClosed ctx.G.object fan.center Assigned
  closedDecidable := Graph.AssignedFanCharge.cubicClosedDecidable ctx.G.object
    fan.center Assigned assignedDecidable
  quarterCharge := Graph.AssignedFanCharge.quarterCharge ctx.G.object fan.center
    centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx)) Assigned assignedDecidable
  closedQuarterCharge := fun port closed =>
    Graph.AssignedFanCharge.quarterCharge_eq_neg_one_of_cubicClosed ctx.G.object
      fan.center centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx)) Assigned assignedDecidable port closed
  openQuarterChargeLower := fun port openPort =>
    Graph.AssignedFanCharge.quarterCharge_ge_three_of_not_cubicClosed ctx.G.object
      fan.center centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx)) Assigned assignedDecidable port openPort

structure CertificateClosedMarkedFan
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    where
  fan : MarkedFan ctx
  centerHigh : 4 ≤ ctx.G.object.degree fan.center
  Assigned : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex → Prop
  assignedDecidable : ∀ carrier, Decidable (Assigned carrier)
  certificateClosed :
    4 * (markedFanChargeProfile fan centerHigh Assigned
      assignedDecidable).closedCount
      ctx.toBranchContext + ctx.G.object.degree fan.center ≤ 11

namespace CertificateClosedMarkedFan

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (marked : CertificateClosedMarkedFan ctx)

def chargeProfile : Graph.CertificateClosedFanCharge.Profile
    (Graph.HighCenterPort.Port ctx.G.object marked.fan.center) :=
  markedFanChargeProfile marked.fan marked.centerHigh marked.Assigned
    marked.assignedDecidable

def stage : marked.chargeProfile.VerifiedStage ctx.toBranchContext :=
  marked.chargeProfile.verifiedStage ctx.toBranchContext

theorem run_terminal :
    (marked.chargeProfile.run ctx.toBranchContext).terminal = .capacity :=
  marked.stage.terminal

theorem run_trace :
    (marked.chargeProfile.run ctx.toBranchContext).trace =
      [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
        .capacityTerminal] :=
  marked.stage.trace

theorem chargeExact :
    marked.chargeProfile.neighborhoodQuarterChargeLower ctx.toBranchContext =
      11 - (ctx.G.object.degree marked.fan.center : Int) -
        4 * (marked.chargeProfile.closedCount ctx.toBranchContext : Int) := by
  have cardEq : marked.chargeProfile.members.card =
      ctx.G.object.degree marked.fan.center := by
    change (Graph.HighCenterPort.ports ctx.G.object marked.fan.center).card =
      ctx.G.object.degree marked.fan.center
    exact Graph.HighCenterPort.ports_card_eq_degree _ _
  have exactCharge := marked.stage.chargeExact
  rw [cardEq] at exactCharge
  exact exactCharge

theorem charge_nonnegative :
    0 ≤ marked.chargeProfile.neighborhoodQuarterChargeLower
      ctx.toBranchContext := by
  have cardEq : marked.chargeProfile.members.card =
      ctx.G.object.degree marked.fan.center := by
    change (Graph.HighCenterPort.ports ctx.G.object marked.fan.center).card =
      ctx.G.object.degree marked.fan.center
    exact Graph.HighCenterPort.ports_card_eq_degree _ _
  have certificate := marked.certificateClosed
  change 4 * marked.chargeProfile.closedCount ctx.toBranchContext +
    ctx.G.object.degree marked.fan.center ≤ 11 at certificate
  rw [← cardEq] at certificate
  apply marked.chargeProfile.neighborhoodQuarterChargeLower_nonnegative
  exact certificate

end CertificateClosedMarkedFan

structure VerifiedCertificateClosedFanChargePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedMarkedFanLabelPackingPrefix ctx
  terminal : ∀ marked : CertificateClosedMarkedFan ctx,
    (marked.chargeProfile.run ctx.toBranchContext).terminal = .capacity
  trace : ∀ marked : CertificateClosedMarkedFan ctx,
    (marked.chargeProfile.run ctx.toBranchContext).trace =
      [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
        .capacityTerminal]
  charge : ∀ marked : CertificateClosedMarkedFan ctx,
    0 ≤ marked.chargeProfile.neighborhoodQuarterChargeLower ctx.toBranchContext

def verifiedCertificateClosedFanChargePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedMarkedFanLabelPackingPrefix ctx) :
    VerifiedCertificateClosedFanChargePrefix ctx where
  previous := previous
  terminal := fun marked => marked.run_terminal
  trace := fun marked => marked.run_trace
  charge := fun marked => marked.charge_nonnegative

theorem exists_verifiedCertificateClosedFanChargePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedCertificateClosedFanChargePrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedMarkedFanLabelPackingPrefix object baseline avoids
  exact ⟨ctx, rankLe,
    verifiedCertificateClosedFanChargePrefix ctx previous⟩

end Erdos64EG.Internal
