import Erdos64EG.CT2BridgeContraction
import StructuralExhaustion.Graph.TriangularPortReturn

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT1: triangular-port return

The CT2 bridge stage is consumed through the framework's generic
`BridgeReductionStage.dartReturn` transition.  The graph layer then derives
the shoulder, the simple path in `G-x`, its reconstructed cycle and first
landing, and executes one certificate-driven CT1 check.  This application
adds only the power-of-two length interpretation.
-/

def triangularPortTargetAvoiding
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ¬Graph.HasCycleWithLength ctx.G.object.graph
      (fixedPackedInput ctx).LengthOK :=
  (packedStaticInput.fixedContext ctx).avoids

noncomputable def triangularPortRoot
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (port : Graph.TriangularPortReturn.TriPort
      (triangularShoulderSetup ctx center centerHigh)) :=
  (bridgeReductionStage ctx).dartReturn
    (Graph.TriangularPortReturn.rootDart
      (triangularShoulderSetup ctx center centerHigh) port)

abbrev TriangularPortReturnStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (port : Graph.TriangularPortReturn.TriPort
      (triangularShoulderSetup ctx center centerHigh)) :=
  Graph.TriangularPortReturn.VerifiedStage
    (triangularShoulderSetup ctx center centerHigh) port
    (triangularPortRoot ctx center centerHigh port)
    (triangularPortTargetAvoiding ctx)

noncomputable def triangularPortReturnStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (port : Graph.TriangularPortReturn.TriPort
      (triangularShoulderSetup ctx center centerHigh)) :
    TriangularPortReturnStage ctx center centerHigh port :=
  Graph.TriangularPortReturn.verifiedStage
    (triangularShoulderSetup ctx center centerHigh) port
    (triangularPortRoot ctx center centerHigh port)
    (triangularPortTargetAvoiding ctx)

/-- The manuscript's displayed Mersenne-predecessor exclusion. -/
theorem triangularPortReturn_length_ne
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (port : Graph.TriangularPortReturn.TriPort
      (triangularShoulderSetup ctx center centerHigh))
    (exponent : Nat) (lower : 2 ≤ exponent) :
    (Graph.TriangularPortReturn.certificate
      (triangularShoulderSetup ctx center centerHigh) port
      (triangularPortRoot ctx center centerHigh port)).path.length ≠
        2 ^ exponent - 2 := by
  intro equality
  apply (triangularPortReturnStage ctx center centerHigh port).lengthExcluded
  change PowerOfTwoLength
    ((Graph.TriangularPortReturn.certificate
      (triangularShoulderSetup ctx center centerHigh) port
      (triangularPortRoot ctx center centerHigh port)).path.length + 2)
  rw [powerOfTwoLength_iff]
  refine ⟨exponent, lower, ?_⟩
  have powerLower : 2 ^ 2 ≤ 2 ^ exponent :=
    Nat.pow_le_pow_right (by decide) lower
  omega

structure VerifiedTriangularPortReturnPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedBridgeReductionPrefix ctx
  localStage : ∀ center (centerHigh : 4 ≤ ctx.G.object.degree center)
    (port : Graph.TriangularPortReturn.TriPort
      (triangularShoulderSetup ctx center centerHigh)),
    TriangularPortReturnStage ctx center centerHigh port

noncomputable def verifiedTriangularPortReturnPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedBridgeReductionPrefix ctx) :
    VerifiedTriangularPortReturnPrefix ctx where
  previous := previous
  localStage := triangularPortReturnStage ctx

theorem exists_verifiedTriangularPortReturnPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedTriangularPortReturnPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedBridgeReductionPrefix object baseline avoids
  exact ⟨ctx, rankLe,
    verifiedTriangularPortReturnPrefix ctx previous⟩

end Erdos64EG.Internal
