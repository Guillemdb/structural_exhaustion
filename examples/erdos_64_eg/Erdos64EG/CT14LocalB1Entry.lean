import Erdos64EG.CT14PositiveDeficitFanEntry

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT14: the positive-deficit entry is manuscript B1

The graph framework owns the semantic local-ledger interface.  This file only
identifies the already verified positive-deficit Erdős fan stage with that
interface; it adds no alternative-exclusion, disjointness, or payment premise.
-/

namespace PositiveDeficitMarkedFan

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (entry : PositiveDeficitMarkedFan ctx)

/-- The local entry in `lem:typeB-hybrid-B1` and
`cor:typeB-local-entry-is-B1`, projected from the exact CT14 stage. -/
noncomputable def localB1Entry :
    Graph.HybridFanIncidence.LocalLedgerEntry
      (base := fixedPackedInput ctx)
      (baseline := (packedStaticInput.fixedContext ctx).baseline)
      entry.centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
      entry.first entry.second entry.assigned :=
  entry.hybridStage.toLocalLedgerEntry

theorem localB1_endpoint_disjoint : Function.Injective (fun incidence :
    Graph.HybridFanIncidence.Incidence
      (object := ctx.G.object) (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable) =>
      Graph.HybridFanIncidence.other
        (object := ctx.G.object) (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
        incidence.1 incidence.2) :=
  entry.localB1Entry.endpointDisjoint

theorem localB1_nonWindow_credit_pays :
    Graph.HybridFanIncidence.remainingNonWindowDemand
        (base := fixedPackedInput ctx) (object := ctx.G.object)
        (baseline := (packedStaticInput.fixedContext ctx).baseline)
        (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable) ≤
      (Graph.HybridFanIncidence.nonWindowQuarterCredit
        (base := fixedPackedInput ctx) (object := ctx.G.object)
        (baseline := (packedStaticInput.fixedContext ctx).baseline)
        (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable) : Int) :=
  entry.localB1Entry.nonWindowCreditPays

end PositiveDeficitMarkedFan

/-- The verified prefix now exposes the exact local B1 interface, not merely
the underlying CT14 execution. -/
structure VerifiedLocalB1Prefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedPositiveDeficitFanEntryPrefix ctx
  localB1 : ∀ entry : PositiveDeficitMarkedFan ctx,
    Graph.HybridFanIncidence.LocalLedgerEntry
      (base := fixedPackedInput ctx)
      (baseline := (packedStaticInput.fixedContext ctx).baseline)
      entry.centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
      entry.first entry.second entry.assigned

noncomputable def verifiedLocalB1Prefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedPositiveDeficitFanEntryPrefix ctx) :
    VerifiedLocalB1Prefix ctx where
  previous := previous
  localB1 := fun entry => entry.localB1Entry

theorem exists_verifiedLocalB1Prefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedLocalB1Prefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedPositiveDeficitFanEntryPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedLocalB1Prefix ctx previous⟩

end Erdos64EG.Internal
