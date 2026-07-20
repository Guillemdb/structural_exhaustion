import Erdos64EG.Future.CT7OpenPortResponses
import StructuralExhaustion.Graph.PortShoulderLedger

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT5: exact selected-port shoulder ledger

The graph-owned CT5 profile uses one finite witness per canonical surplus
slot: the deletion-critical cubic endpoint has exactly two non-centre
shoulders.  On the overload branch it executes from the complete CT7 ledger;
the bounded CT9 branch is retained unchanged.
-/

def portShoulderLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.PortShoulderLedger.VerifiedStage
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx)) :=
  Graph.PortShoulderLedger.verifiedStage
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

theorem runPortShoulderLedgerCT5_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.PortShoulderLedger.run
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))).terminal = .charge :=
  (portShoulderLedgerStage ctx).terminal

theorem runPortShoulderLedgerCT5_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    CT5.ledgerTotal
      (Graph.PortShoulderLedger.spec
        (fixedPackedInput ctx) ctx.G.object
        ((fixedPackedInput ctx).dart_has_tight_endpoint
          (packedStaticInput.fixedContext ctx)))
      (Graph.PortShoulderLedger.capability
        (fixedPackedInput ctx) ctx.G.object
        ((fixedPackedInput ctx).dart_has_tight_endpoint
          (packedStaticInput.fixedContext ctx)))
      (Graph.PortShoulderLedger.context
        (fixedPackedInput ctx) ctx.G.object
        (packedStaticInput.fixedContext ctx).baseline) =
      2 * (Graph.SurplusPortActivity.portSlots ctx.G.object).card :=
  (portShoulderLedgerStage ctx).ledgerTotal

theorem runPortShoulderLedgerCT5_checks_quadratic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.PortShoulderLedger.checks ctx.G.object ≤
      2 * ctx.G.object.input.vertices.card ^ 2 + 2 :=
  (portShoulderLedgerStage ctx).polynomial

/-- The node-[70] continuation is indexed by the literal node-[69] decision.
The bounded edge adds no data; the routed edge stores only the CT5 stage.  The
complete source ledger remains in `previous` exactly once. -/
noncomputable def PortShoulderContinuation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedOpenPortResponsePrefix ctx) :=
  match previous.added with
  | .bounded _certificate => PUnit
  | .routed source =>
      let responseStage :=
        Graph.OpenPortResponse.routedLedgerStage
          (fixedPackedInput ctx) ctx.G.object
          (packedStaticInput.fixedContext ctx).baseline
          ((fixedPackedInput ctx).dart_has_tight_endpoint
            (packedStaticInput.fixedContext ctx)) previous.previous source
      Core.Routing.ResidualStage .ct5
        (Graph.PortShoulderLedger.AccumulatedLedger
          (fixedPackedInput ctx) ctx.G.object
          (packedStaticInput.fixedContext ctx).baseline
          ((fixedPackedInput ctx).dart_has_tight_endpoint
            (packedStaticInput.fixedContext ctx)) responseStage)

abbrev VerifiedPortShoulderLedgerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedOpenPortResponsePrefix ctx)
    (PortShoulderContinuation ctx)

noncomputable def verifiedPortShoulderLedgerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedOpenPortResponsePrefix ctx) :
    VerifiedPortShoulderLedgerPrefix ctx := by
  rcases previous with ⟨sourceLedger, state⟩
  cases state with
  | bounded certificate =>
      exact ⟨⟨sourceLedger, .bounded certificate⟩, PUnit.unit⟩
  | routed source =>
      let responseStage :=
        Graph.OpenPortResponse.routedLedgerStage
            (fixedPackedInput ctx) ctx.G.object
            (packedStaticInput.fixedContext ctx).baseline
            ((fixedPackedInput ctx).dart_has_tight_endpoint
              (packedStaticInput.fixedContext ctx)) sourceLedger source
      exact ⟨⟨sourceLedger, .routed source⟩,
        Graph.PortShoulderLedger.accumulatedLedgerStage
          (fixedPackedInput ctx) ctx.G.object
          (packedStaticInput.fixedContext ctx).baseline
          ((fixedPackedInput ctx).dart_has_tight_endpoint
            (packedStaticInput.fixedContext ctx)) responseStage⟩

theorem exists_verifiedPortShoulderLedgerPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedPortShoulderLedgerPrefix ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedOpenPortResponsePrefix object baseline avoids
  exact ⟨ctx, verifiedPortShoulderLedgerPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
