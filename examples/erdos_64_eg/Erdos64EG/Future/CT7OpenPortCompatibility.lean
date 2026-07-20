import Erdos64EG.Future.CT5PortShoulderLedger
import StructuralExhaustion.Graph.OpenPortCompatibility

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Fan-compatible interpretation of the overload pair

This is a theorem-only extension of the exact CT5 ledger, not a second CT7
execution.  The bounded fibre branch is retained.  In the overload branch,
four-cycle avoidance proves that a nonadjacent endpoint pair has disjoint
shoulders and hence is fan-compatible; endpoint adjacency remains an explicit
alternative for the subsequent heavy-centre dichotomy.
-/

abbrev OpenPortCompatibilityState
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : OpenPortSourceResidual ctx) :=
  Graph.OpenPortCompatibility.StateSpace
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx)) source

theorem openPortCompatibility_stateSpace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : OpenPortSourceResidual ctx) :
    OpenPortCompatibilityState ctx source :=
  Graph.OpenPortCompatibility.stateSpace
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    source
    (fourCycleFree ctx)

abbrev OpenPortCompatibilityLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : OpenPortSourceResidual ctx)
    {sourceLedger : OpenPortPairLedger ctx}
    (responseStage : Core.Routing.ResidualStage .ct7
      (OpenPortRoutedLedger ctx sourceLedger source)) :=
  Core.Routing.LedgerExtension
    (Graph.PortShoulderLedger.AccumulatedLedger
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx)) responseStage)
    (fun _shoulderLedger => OpenPortCompatibilityState ctx source)

/-- The compatibility refinement stores the complete node-[70] ledger once.
The bounded edge is proof-only; the routed edge adds the literal theorem-only
CT5 refinement stage. -/
noncomputable def OpenPortCompatibilityContinuation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedPortShoulderLedgerPrefix ctx) :=
  match previous.previous.added with
  | .bounded _certificate => PUnit
  | .routed source =>
      let responseStage :=
        Graph.OpenPortResponse.routedLedgerStage
          (fixedPackedInput ctx) ctx.G.object
          (packedStaticInput.fixedContext ctx).baseline
          ((fixedPackedInput ctx).dart_has_tight_endpoint
            (packedStaticInput.fixedContext ctx))
          previous.previous.previous source
      Core.Routing.ResidualStage .ct5
        (OpenPortCompatibilityLedger ctx source responseStage)

abbrev VerifiedOpenPortCompatibilityPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedPortShoulderLedgerPrefix ctx)
    (OpenPortCompatibilityContinuation ctx)

noncomputable def verifiedOpenPortCompatibilityPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedPortShoulderLedgerPrefix ctx) :
    VerifiedOpenPortCompatibilityPrefix ctx := by
  rcases previous with ⟨⟨sourceLedger, state⟩, continuation⟩
  cases state with
  | bounded certificate =>
      exact ⟨⟨⟨sourceLedger, .bounded certificate⟩, continuation⟩, PUnit.unit⟩
  | routed source =>
      exact ⟨⟨⟨sourceLedger, .routed source⟩, continuation⟩,
        continuation.extend
          (Added := fun _shoulderLedger =>
            OpenPortCompatibilityState ctx source)
          (openPortCompatibility_stateSpace ctx source)⟩

theorem exists_verifiedOpenPortCompatibilityPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedOpenPortCompatibilityPrefix ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedPortShoulderLedgerPrefix object baseline avoids
  exact ⟨ctx, verifiedOpenPortCompatibilityPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
