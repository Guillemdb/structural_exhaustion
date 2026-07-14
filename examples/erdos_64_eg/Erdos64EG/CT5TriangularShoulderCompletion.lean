import Erdos64EG.CT10HighCenterPortDichotomy
import StructuralExhaustion.Graph.TriangularShoulderCompletion

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT5: triangular shoulder-completion bookkeeping

The framework owns the actual triangular-port shoulder sites, completion
incidences, all four structural clauses, the CT5 witness search, and its work
bound.  This module only supplies the verified Erdős graph hypotheses.
-/

def triangularShoulderSetup
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center) :
    Graph.TriangularShoulderCompletion.Setup
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline center where
  centerHigh := centerHigh
  threeLeMinimum := Nat.le_refl 3
  deletionCritical :=
    (fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx)
  fourFree := fourCycleFree ctx

abbrev TriangularShoulderStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center) :=
  Graph.TriangularShoulderCompletion.VerifiedStage
    (triangularShoulderSetup ctx center centerHigh)

theorem triangularShoulder_stage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center) :
    TriangularShoulderStage ctx center centerHigh :=
  Graph.TriangularShoulderCompletion.verifiedStage
    (triangularShoulderSetup ctx center centerHigh)

structure VerifiedTriangularShoulderCompletionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedHighCenterPortDichotomyPrefix ctx
  localStage : ∀ center (centerHigh : 4 ≤ ctx.G.object.degree center),
    TriangularShoulderStage ctx center centerHigh

def verifiedTriangularShoulderCompletionPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedHighCenterPortDichotomyPrefix ctx) :
    VerifiedTriangularShoulderCompletionPrefix ctx where
  previous := previous
  localStage := triangularShoulder_stage ctx

theorem exists_verifiedTriangularShoulderCompletionPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedTriangularShoulderCompletionPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedHighCenterPortDichotomyPrefix object baseline avoids
  exact ⟨ctx, rankLe,
    verifiedTriangularShoulderCompletionPrefix ctx previous⟩

end Erdos64EG.Internal
