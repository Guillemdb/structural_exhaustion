import Erdos64EG.CT7OpenPortCompatibility
import StructuralExhaustion.Graph.HighCenterPort

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT10: all-incident-port dichotomy at high centres

The framework profile scans exactly one centre's declared neighbour list.  It
classifies every actual incident port as open or triangular, then combines the
classification with four-cycle avoidance.  The Erdős layer supplies only the
already verified graph hypotheses and retains the preceding prefix.
-/

abbrev HighCenterPortStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex)
    (centerHigh : 4 ≤ ctx.G.object.degree center) :=
  Graph.HighCenterPort.VerifiedStage
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline center centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (fourCycleFree ctx)

theorem highCenterPort_stage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex)
    (centerHigh : 4 ≤ ctx.G.object.degree center) :
    HighCenterPortStage ctx center centerHigh :=
  Graph.HighCenterPort.verifiedStage
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline center centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (fourCycleFree ctx)

structure VerifiedHighCenterPortDichotomyPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedOpenPortCompatibilityPrefix ctx
  localStage : ∀ center (centerHigh : 4 ≤ ctx.G.object.degree center),
    HighCenterPortStage ctx center centerHigh

def verifiedHighCenterPortDichotomyPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedOpenPortCompatibilityPrefix ctx) :
    VerifiedHighCenterPortDichotomyPrefix ctx where
  previous := previous
  localStage := highCenterPort_stage ctx

theorem exists_verifiedHighCenterPortDichotomyPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedHighCenterPortDichotomyPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedOpenPortCompatibilityPrefix object baseline avoids
  exact ⟨ctx, rankLe,
    verifiedHighCenterPortDichotomyPrefix ctx previous⟩

end Erdos64EG.Internal
