import Erdos64EG.CT5TriangularShoulderCompletion
import StructuralExhaustion.Graph.PackedBridgeReduction

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT2: bridge-contraction reduction

The framework constructs the contraction and proves strict rank decrease,
minimum-degree preservation, and exact cycle-length transport.  The Erdős
application supplies only its threshold fact `2 ≤ 3` and retains the framework
stage after the preceding verified prefix.
-/

abbrev BridgeReductionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  packedStaticInput.BridgeReductionStage (by decide) ctx

def bridgeReductionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    BridgeReductionStage ctx :=
  packedStaticInput.bridgeReductionStage (by decide) ctx

/-- Every oriented edge of the selected counterexample is non-bridging. -/
theorem dart_not_bridge
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (dart : ctx.G.object.graph.Dart) :
    ¬ctx.G.object.graph.IsBridge dart.edge :=
  (bridgeReductionStage ctx).bridgeless dart

structure VerifiedBridgeReductionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedTriangularShoulderCompletionPrefix ctx
  bridgeStage : BridgeReductionStage ctx

def verifiedBridgeReductionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTriangularShoulderCompletionPrefix ctx) :
    VerifiedBridgeReductionPrefix ctx where
  previous := previous
  bridgeStage := bridgeReductionStage ctx

theorem exists_verifiedBridgeReductionPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedBridgeReductionPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedTriangularShoulderCompletionPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedBridgeReductionPrefix ctx previous⟩

end Erdos64EG.Internal
