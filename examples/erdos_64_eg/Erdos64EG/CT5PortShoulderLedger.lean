import Erdos64EG.CT7OpenPortResponses
import StructuralExhaustion.Graph.PortShoulderLedger

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT5: exact selected-port shoulder ledger

The graph-owned CT5 profile uses one finite witness per canonical surplus
slot: the deletion-critical cubic endpoint has exactly two non-centre
shoulders.  The application contributes only the already verified packed
graph and its inherited deletion-critical theorem.
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

structure VerifiedPortShoulderLedgerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedOpenPortResponsePrefix ctx
  stage : Graph.PortShoulderLedger.VerifiedStage
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

def verifiedPortShoulderLedgerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedOpenPortResponsePrefix ctx) :
    VerifiedPortShoulderLedgerPrefix ctx where
  previous := previous
  stage := portShoulderLedgerStage ctx

theorem exists_verifiedPortShoulderLedgerPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedPortShoulderLedgerPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedOpenPortResponsePrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedPortShoulderLedgerPrefix ctx previous⟩

end Erdos64EG.Internal
