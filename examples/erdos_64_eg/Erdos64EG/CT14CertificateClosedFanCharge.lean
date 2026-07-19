import Erdos64EG.CT9MarkedFanLabelPacking
import StructuralExhaustion.Graph.AssignedFanCharge
import StructuralExhaustion.Graph.CertificateClosedFanCharge

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v

/-!
# CT14: certificate-closed fan charge

Certificate-closed fans are a proof-indexed CT9→CT14 family.  The framework
retains the complete fan-packing ledger once and executes one specialized CT14
entry per supplied fan, without enumerating fan centres or assignments.
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
      assignedDecidable).closedCount ctx.toBranchContext +
      ctx.G.object.degree fan.center ≤ 11

namespace CertificateClosedMarkedFan

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (marked : CertificateClosedMarkedFan ctx)

def chargeProfile : Graph.CertificateClosedFanCharge.Profile
    (Graph.HighCenterPort.Port ctx.G.object marked.fan.center) :=
  markedFanChargeProfile marked.fan marked.centerHigh marked.Assigned
    marked.assignedDecidable

theorem chargeExact :
    marked.chargeProfile.neighborhoodQuarterChargeLower ctx.toBranchContext =
      11 - (ctx.G.object.degree marked.fan.center : Int) -
        4 * (marked.chargeProfile.closedCount ctx.toBranchContext : Int) := by
  have cardEq : marked.chargeProfile.members.card =
      ctx.G.object.degree marked.fan.center := by
    change (Graph.HighCenterPort.ports ctx.G.object marked.fan.center).card =
      ctx.G.object.degree marked.fan.center
    exact Graph.HighCenterPort.ports_card_eq_degree _ _
  have exactCharge :=
    marked.chargeProfile.neighborhoodQuarterChargeLower_eq ctx.toBranchContext
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
  exact marked.chargeProfile.neighborhoodQuarterChargeLower_nonnegative
    ctx.toBranchContext certificate

end CertificateClosedMarkedFan

noncomputable def certificateClosedFanTarget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (marked : CertificateClosedMarkedFan ctx) :=
  (marked.chargeProfile.capability PackedProblem.{u}).executableInterface

noncomputable def certificateClosedFanAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (marked : CertificateClosedMarkedFan ctx) :
    Routes.Accumulated.Adapter Unit (certificateClosedFanTarget ctx marked) where
  targetContext := fun _source => ctx.toBranchContext
  trigger := fun _source => ⟨⟩

noncomputable def certificateClosedFanTransition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (marked : CertificateClosedMarkedFan ctx) :=
  Routes.Accumulated.transition (sourceTactic := .ct9)
    (certificateClosedFanTarget ctx marked)
    (certificateClosedFanAdapter ctx marked)

noncomputable def certificateClosedFanPointwiseAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (Ledger : Sort v) :
    Routes.Accumulated.PointwiseAdapter .ct9 .ct14
      (CertificateClosedMarkedFan ctx) Ledger where
  Source := fun _marked => Unit
  target := certificateClosedFanTarget ctx
  adapter := certificateClosedFanAdapter ctx
  current := fun _marked _ledger => ()

noncomputable def certificateClosedFanTransitionFamily
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (Ledger : Sort v) :=
  Routes.Accumulated.pointwiseFamily
    (certificateClosedFanPointwiseAdapter ctx Ledger)

noncomputable def certificateClosedFanTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct9 Ledger) :=
  Routes.Accumulated.advancePointwise
    (certificateClosedFanPointwiseAdapter ctx Ledger) source

abbrev CertificateClosedFanTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct9 Ledger) :=
  Routes.Accumulated.PointwiseOutputLedger
    (certificateClosedFanPointwiseAdapter ctx Ledger) source

structure CertificateClosedFanFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct9 Ledger}
    (execution : CertificateClosedFanTransitionLedger ctx source) : Prop where
  terminal : ∀ marked : CertificateClosedMarkedFan ctx,
    (execution.localStage marked).targetResult.terminal = .capacity
  trace : ∀ marked : CertificateClosedMarkedFan ctx,
    (execution.localStage marked).targetResult.trace =
      [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
        .capacityTerminal]
  charge : ∀ marked : CertificateClosedMarkedFan ctx,
    0 ≤ marked.chargeProfile.neighborhoodQuarterChargeLower ctx.toBranchContext

abbrev CertificateClosedFanLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct9 Ledger) :=
  Core.Routing.LedgerExtension
    (CertificateClosedFanTransitionLedger ctx source)
    (CertificateClosedFanFacts ctx)

noncomputable def certificateClosedFanLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    (source : Core.Routing.ResidualStage .ct9 Ledger) :
    Core.Routing.ResidualStage .ct14
      (CertificateClosedFanLedger ctx source) := by
  let execution := certificateClosedFanTransitionStage ctx source
  exact execution.ledgerStage.extend {
    terminal := fun marked => by
      change (marked.chargeProfile.run ctx.toBranchContext).terminal = .capacity
      exact marked.chargeProfile.run_terminal ctx.toBranchContext
    trace := fun marked => by
      change (marked.chargeProfile.run ctx.toBranchContext).trace = _
      exact marked.chargeProfile.run_trace ctx.toBranchContext
    charge := fun marked => marked.charge_nonnegative
  }

noncomputable def runCertificateClosedFanCT14
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Ledger : Sort v}
    {source : Core.Routing.ResidualStage .ct9 Ledger}
    (stage : Core.Routing.ResidualStage .ct14
      (CertificateClosedFanLedger ctx source))
    (marked : CertificateClosedMarkedFan ctx) :=
  (stage.output.previous.localStage marked).targetResult

theorem certificateClosedFanTransition_profile_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (marked : CertificateClosedMarkedFan ctx) :
    (certificateClosedFanTransition ctx marked).profileId =
      "CT9.residual.accumulatedLedger->CT14" :=
  Routes.Accumulated.transition_profile_id
    (certificateClosedFanTarget ctx marked)
    (certificateClosedFanAdapter ctx marked)

noncomputable def CertificateClosedFanStep
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedMarkedFanLabelPackingPrefix ctx) := by
  rcases previous with ⟨fanLabelPrefix, markedFanStage⟩
  rcases fanLabelPrefix with ⟨twoWindowPrefix, _fanLabelStage⟩
  rcases twoWindowPrefix with ⟨directPrefix, _twoWindowStage⟩
  rcases directPrefix with ⟨hybridPrefix, _directStage⟩
  rcases hybridPrefix with ⟨massPrefix, _hybridStage⟩
  rcases massPrefix with ⟨fanPrefix, _massStage⟩
  rcases fanPrefix with ⟨crossPrefix, _fanStage⟩
  rcases crossPrefix with ⟨landingPrefix, _crossStage⟩
  rcases landingPrefix with ⟨returnPrefix, _landingContinuation⟩
  rcases returnPrefix with ⟨bridgePrefix, _returnContinuation⟩
  rcases bridgePrefix with ⟨shoulderPrefix, _bridgeContinuation⟩
  rcases shoulderPrefix with
    ⟨highCenterPrefix, _triangularShoulderContinuation⟩
  rcases highCenterPrefix with
    ⟨compatibilityPrefix, _highCenterContinuation⟩
  rcases compatibilityPrefix with
    ⟨shoulderLedgerPrefix, _compatibilityContinuation⟩
  rcases shoulderLedgerPrefix with
    ⟨responsePrefix, _shoulderContinuation⟩
  rcases responsePrefix with ⟨_sourceLedger, state⟩
  cases state with
  | routed _source =>
      exact Core.Routing.ResidualStage .ct14
        (CertificateClosedFanLedger ctx markedFanStage)
  | bounded _certificate =>
      exact PUnit

abbrev VerifiedCertificateClosedFanChargePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedMarkedFanLabelPackingPrefix ctx)
    (CertificateClosedFanStep ctx)

noncomputable def verifiedCertificateClosedFanChargePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedMarkedFanLabelPackingPrefix ctx) :
    VerifiedCertificateClosedFanChargePrefix ctx :=
  ⟨previous, by
    rcases previous with ⟨fanLabelPrefix, markedFanStage⟩
    rcases fanLabelPrefix with ⟨twoWindowPrefix, _fanLabelStage⟩
    rcases twoWindowPrefix with ⟨directPrefix, _twoWindowStage⟩
    rcases directPrefix with ⟨hybridPrefix, _directStage⟩
    rcases hybridPrefix with ⟨massPrefix, _hybridStage⟩
    rcases massPrefix with ⟨fanPrefix, _massStage⟩
    rcases fanPrefix with ⟨crossPrefix, _fanStage⟩
    rcases crossPrefix with ⟨landingPrefix, _crossStage⟩
    rcases landingPrefix with ⟨returnPrefix, _landingContinuation⟩
    rcases returnPrefix with ⟨bridgePrefix, _returnContinuation⟩
    rcases bridgePrefix with ⟨shoulderPrefix, _bridgeContinuation⟩
    rcases shoulderPrefix with
      ⟨highCenterPrefix, _triangularShoulderContinuation⟩
    rcases highCenterPrefix with
      ⟨compatibilityPrefix, _highCenterContinuation⟩
    rcases compatibilityPrefix with
      ⟨shoulderLedgerPrefix, _compatibilityContinuation⟩
    rcases shoulderLedgerPrefix with
      ⟨responsePrefix, _shoulderContinuation⟩
    rcases responsePrefix with ⟨_sourceLedger, state⟩
    cases state with
    | routed _source =>
        exact certificateClosedFanLedgerStage ctx markedFanStage
    | bounded _certificate =>
        exact PUnit.unit
  ⟩

theorem exists_verifiedCertificateClosedFanChargePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedCertificateClosedFanChargePrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedMarkedFanLabelPackingPrefix object baseline avoids
  exact ⟨ctx, verifiedCertificateClosedFanChargePrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
