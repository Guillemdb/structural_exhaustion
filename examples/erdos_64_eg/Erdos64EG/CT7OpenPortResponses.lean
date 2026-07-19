import Erdos64EG.CT9OpenPortPairs
import StructuralExhaustion.Graph.OpenPortResponse

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT7: routed open-port adjacency responses

This is a thin instantiation of the framework-owned CT9-to-CT7 transition.
The bounded CT9 branch is retained verbatim.  Only an actual overload
residual is routed to CT7, where the two canonical port endpoints are compared
against the exact declared vertex context.
-/

abbrev OpenPortPairLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.ResidualStage .ct9 (VerifiedOpenPortPairPrefix ctx)

abbrev OpenPortBounded
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  ∀ center,
    CT9.fibreCount (openPortPairCapability ctx)
      (openPortPairInput ctx) center ≤ 1

abbrev OpenPortSourceResidual
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.OpenPortResponse.SourceResidual
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

abbrev OpenPortRoutedLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (sourceLedger : OpenPortPairLedger ctx)
    (source : OpenPortSourceResidual ctx) :=
  Graph.OpenPortResponse.RoutedLedger
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx)) sourceLedger source

abbrev OpenPortResponseState
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (sourceLedger : OpenPortPairLedger ctx) :=
  Graph.OpenPortResponse.StateSpace
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx)) sourceLedger

def openPortResponse_stateSpace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (sourceLedger : OpenPortPairLedger ctx) :
    OpenPortResponseState ctx sourceLedger :=
  Graph.OpenPortResponse.stateSpace
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx)) sourceLedger

abbrev VerifiedOpenPortResponsePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (OpenPortPairLedger ctx)
    (OpenPortResponseState ctx)

def verifiedOpenPortResponsePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedOpenPortPairPrefix ctx) :
    VerifiedOpenPortResponsePrefix ctx :=
  let sourceLedger :=
    Core.Routing.ResidualStage.exact (tactic := .ct9) previous
  ⟨sourceLedger, openPortResponse_stateSpace ctx sourceLedger⟩

theorem exists_verifiedOpenPortResponsePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedOpenPortResponsePrefix ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedOpenPortPairPrefix object baseline avoids
  exact ⟨ctx, verifiedOpenPortResponsePrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
