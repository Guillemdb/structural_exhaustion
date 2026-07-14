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

theorem openPortResponse_stateSpace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (∀ center,
      CT9.fibreCount (openPortPairCapability ctx)
        (openPortPairInput ctx) center ≤ 1) ∨
      (∃ source : Graph.OpenPortResponse.SourceResidual
          (fixedPackedInput ctx) ctx.G.object
          (packedStaticInput.fixedContext ctx).baseline
          ((fixedPackedInput ctx).dart_has_tight_endpoint
            (packedStaticInput.fixedContext ctx)),
        Graph.OpenPortResponse.RoutedStage
          (fixedPackedInput ctx) ctx.G.object
          (packedStaticInput.fixedContext ctx).baseline
          ((fixedPackedInput ctx).dart_has_tight_endpoint
            (packedStaticInput.fixedContext ctx)) source) :=
  Graph.OpenPortResponse.stateSpace
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

structure VerifiedOpenPortResponsePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedOpenPortPairPrefix ctx
  stateSpace :
    (∀ center,
      CT9.fibreCount (openPortPairCapability ctx)
        (openPortPairInput ctx) center ≤ 1) ∨
      (∃ source : Graph.OpenPortResponse.SourceResidual
          (fixedPackedInput ctx) ctx.G.object
          (packedStaticInput.fixedContext ctx).baseline
          ((fixedPackedInput ctx).dart_has_tight_endpoint
            (packedStaticInput.fixedContext ctx)),
        Graph.OpenPortResponse.RoutedStage
          (fixedPackedInput ctx) ctx.G.object
          (packedStaticInput.fixedContext ctx).baseline
          ((fixedPackedInput ctx).dart_has_tight_endpoint
            (packedStaticInput.fixedContext ctx)) source)

def verifiedOpenPortResponsePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedOpenPortPairPrefix ctx) :
    VerifiedOpenPortResponsePrefix ctx where
  previous := previous
  stateSpace := openPortResponse_stateSpace ctx

theorem exists_verifiedOpenPortResponsePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedOpenPortResponsePrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedOpenPortPairPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedOpenPortResponsePrefix ctx previous⟩

end Erdos64EG.Internal
