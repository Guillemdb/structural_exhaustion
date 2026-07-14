import Erdos64EG.CT14CertificateClosedFanCharge
import Erdos64EG.CT14HybridFanIncidence

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

/-- CT14 scans the exact actual cubic-closed subtype produced by the assigned
fan profile. -/
noncomputable def massStage : FanClosedMassStage ctx entry.fan.center
    entry.centerHigh entry.Assigned entry.assignedDecidable entry.first
    entry.second entry.compatible entry.assigned :=
  fanClosedMassStage ctx entry.fan.center entry.centerHigh entry.Assigned
    entry.assignedDecidable entry.first entry.second entry.compatible
    entry.assigned

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
  entry.massStage.countAtLeastTwo

/-- Exact positive Type-B deficit in quarter units:
`4c + degree - 11 > 0`. -/
theorem positiveDeficit :
    0 < Graph.FanClosedPortMass.deficitNumerator
      (ctx.G.object.degree entry.fan.center)
      (Graph.FanClosedPortMass.cubicClosedNeighbors
        (object := ctx.G.object) (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned
          entry.assignedDecidable)).card :=
  entry.massStage.positiveDeficit

/-- The routed CT14 incidence refinement uses the derived degree cap and
therefore constructs the complete local hybrid entry without an application
assertion. -/
noncomputable def hybridStage : HybridFanIncidenceStage ctx entry.fan.center
    entry.centerHigh entry.degree_le_eight entry.Assigned
    entry.assignedDecidable entry.first entry.second entry.compatible
    entry.assigned :=
  hybridFanIncidenceStage ctx entry.fan.center entry.centerHigh
    entry.degree_le_eight entry.Assigned entry.assignedDecidable entry.first
    entry.second entry.compatible entry.assigned

theorem hybrid_terminal :
    (Graph.HybridFanIncidence.run
      (base := fixedPackedInput ctx)
      (baseline := (packedStaticInput.fixedContext ctx).baseline)
      entry.centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
      entry.first entry.second entry.assigned).terminal = .capacity :=
  entry.hybridStage.terminal

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
  entry.hybridStage.creditPays

end PositiveDeficitMarkedFan

/-- The verified prefix now composes the marked-fan CT9 result with the exact
CT5-to-CT14 and CT14-to-CT14 local fan entry. -/
structure VerifiedPositiveDeficitFanEntryPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedCertificateClosedFanChargePrefix ctx
  localStage : ∀ entry : PositiveDeficitMarkedFan ctx,
    HybridFanIncidenceStage ctx entry.fan.center entry.centerHigh
      entry.degree_le_eight entry.Assigned entry.assignedDecidable entry.first
      entry.second entry.compatible entry.assigned

noncomputable def verifiedPositiveDeficitFanEntryPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedCertificateClosedFanChargePrefix ctx) :
    VerifiedPositiveDeficitFanEntryPrefix ctx where
  previous := previous
  localStage := fun entry => entry.hybridStage

theorem exists_verifiedPositiveDeficitFanEntryPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedPositiveDeficitFanEntryPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedCertificateClosedFanChargePrefix object baseline avoids
  exact ⟨ctx, rankLe,
    verifiedPositiveDeficitFanEntryPrefix ctx previous⟩

end Erdos64EG.Internal
