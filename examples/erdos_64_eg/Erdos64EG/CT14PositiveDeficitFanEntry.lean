import Erdos64EG.CT14CertificateClosedFanCharge
import Erdos64EG.CT5FanClosedPort
import StructuralExhaustion.Graph.HybridFanIncidence

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT14: positive-deficit marked-fan entry

This stage composes the already derived certificate-marked degree bound with
the actual cubic-closed-neighbour and incidence CT14 executions.  Its input is
literal assigned fan data containing two compatible fan-closed ports.  The
framework proves that the resulting closed-neighbour count is at least two,
that the quarter-deficit is positive, and that the exact window/non-window
incidence ledger pays it.  The Erdős layer supplies no degree cap, count, CT
terminal, or capacity conclusion.
-/

/-- Exact local data in the surviving fan-closed branch of
`prop:fan-closed-port-typeB-routing`. -/
structure PositiveDeficitMarkedFan
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    where
  fan : MarkedFan ctx
  centerHigh : 4 ≤ ctx.G.object.degree fan.center
  Assigned : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex → Prop
  assignedDecidable : ∀ carrier, Decidable (Assigned carrier)
  first : FanClosedOpenPort ctx fan.center centerHigh
  second : FanClosedOpenPort ctx fan.center centerHigh
  compatible : Graph.FanClosedPort.CompatiblePair centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx)) first second
  assigned : Graph.FanClosedPort.AssignedPair centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx Assigned assignedDecidable) first second

namespace PositiveDeficitMarkedFan

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (entry : PositiveDeficitMarkedFan ctx)

/-- The marked-fan CT9 cap is consumed directly; it is not repeated as an
input field. -/
theorem degree_le_eight : ctx.G.object.degree entry.fan.center ≤ 8 :=
  entry.fan.degree_le_eight

/-- The exact two-fan-closed-port input forces at least two actual
cubic-closed neighbours. -/
theorem two_le_closedCount :
    2 ≤ (Graph.FanClosedPortMass.cubicClosedNeighbors
      (object := ctx.G.object) (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned
        entry.assignedDecidable)).card :=
  Graph.FanClosedPortMass.two_le_cubicClosed_card entry.centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
    entry.first entry.second entry.compatible entry.assigned

/-- Exact positive Type-B deficit in quarter units:
`4c + degree - 11 > 0`. -/
theorem positiveDeficit :
    0 < Graph.FanClosedPortMass.deficitNumerator
      (ctx.G.object.degree entry.fan.center)
      (Graph.FanClosedPortMass.cubicClosedNeighbors
        (object := ctx.G.object) (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned
          entry.assignedDecidable)).card :=
  Graph.FanClosedPortMass.deficitNumerator_positive entry.centerHigh
    entry.two_le_closedCount

/-- The exact half-incidence capacity pays the positive deficit with at least
three quarter-units of slack. -/
theorem hybrid_credit_pays :
    (3 : Int) ≤
      (Graph.HybridFanIncidence.totalQuarterCredit
        (object := ctx.G.object) (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned
          entry.assignedDecidable) : Int) -
      Graph.FanClosedPortMass.deficitNumerator
        (ctx.G.object.degree entry.fan.center)
        (Graph.HybridFanIncidence.closedMembers
          (object := ctx.G.object) (center := entry.fan.center)
          (p13FanWindowProfile ctx entry.Assigned
            entry.assignedDecidable)).card :=
  Graph.HybridFanIncidence.total_credit_pays_deficit_with_three_slack
    (object := ctx.G.object)
    (center := entry.fan.center)
    (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
    entry.degree_le_eight

end PositiveDeficitMarkedFan

/-- The exact mathematical obligations of one positive-deficit fan entry.
Transport is deliberately absent: actual CT14 executions live only in the
accumulated transition ledger. -/
structure PositiveDeficitFanFacts
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : PositiveDeficitMarkedFan ctx) : Prop where
  closedCount : 2 ≤ (Graph.FanClosedPortMass.cubicClosedNeighbors
    (object := ctx.G.object) (center := entry.fan.center)
    (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)).card
  positiveDeficit : 0 < Graph.FanClosedPortMass.deficitNumerator
    (ctx.G.object.degree entry.fan.center)
    (Graph.FanClosedPortMass.cubicClosedNeighbors
      (object := ctx.G.object) (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)).card
  hybridCreditPays : (3 : Int) ≤
    (Graph.HybridFanIncidence.totalQuarterCredit
      (object := ctx.G.object) (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable) : Int) -
    Graph.FanClosedPortMass.deficitNumerator
      (ctx.G.object.degree entry.fan.center)
      (Graph.HybridFanIncidence.closedMembers
        (object := ctx.G.object) (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)).card

/-- One same-prefix theorem extension; no predecessor fields are restated. -/
abbrev VerifiedPositiveDeficitFanEntryPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedCertificateClosedFanChargePrefix ctx)
    (fun _previous => ∀ entry : PositiveDeficitMarkedFan ctx,
      PositiveDeficitFanFacts entry)

noncomputable def verifiedPositiveDeficitFanEntryPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedCertificateClosedFanChargePrefix ctx) :
    VerifiedPositiveDeficitFanEntryPrefix ctx :=
  ⟨previous, fun entry => {
    closedCount := entry.two_le_closedCount
    positiveDeficit := entry.positiveDeficit
    hybridCreditPays := entry.hybrid_credit_pays
  }⟩

theorem exists_verifiedPositiveDeficitFanEntryPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedPositiveDeficitFanEntryPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedCertificateClosedFanChargePrefix object baseline avoids
  exact ⟨ctx, verifiedPositiveDeficitFanEntryPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
