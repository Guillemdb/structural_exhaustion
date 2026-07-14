import Erdos64EG.CT5FanClosedPort
import StructuralExhaustion.Graph.FanClosedPortMass

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT14: actual cubic-closed fan mass

The framework-owned CT5→CT14 route consumes the preceding charge residual.
The Erdős layer supplies only its literal `P₁₃` window/remainder profile and
the Type-B assignment predicate.  CT14 scans the actual semantic subtype of
cubic-closed neighbours and derives the positive quarter-deficit numerator.
-/

abbrev FanClosedMassStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (Assigned : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex → Prop)
    (assignedDecidable : ∀ carrier, Decidable (Assigned carrier))
    (first second : FanClosedOpenPort ctx center centerHigh)
    (pair : Graph.FanClosedPort.CompatiblePair centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx)) first second)
    (assigned : Graph.FanClosedPort.AssignedPair centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      (p13FanWindowProfile ctx Assigned assignedDecidable) first second) :=
  Graph.FanClosedPortMass.VerifiedStage
    (base := fixedPackedInput ctx)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx Assigned assignedDecidable)
    first second pair assigned

noncomputable def fanClosedMassStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (Assigned : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex → Prop)
    (assignedDecidable : ∀ carrier, Decidable (Assigned carrier))
    (first second : FanClosedOpenPort ctx center centerHigh)
    (pair : Graph.FanClosedPort.CompatiblePair centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx)) first second)
    (assigned : Graph.FanClosedPort.AssignedPair centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      (p13FanWindowProfile ctx Assigned assignedDecidable) first second) :
    FanClosedMassStage ctx center centerHigh Assigned assignedDecidable first
      second pair assigned :=
  Graph.FanClosedPortMass.verifiedStage centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx Assigned assignedDecidable)
    first second pair assigned

structure VerifiedFanClosedMassPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedFanClosedPortPrefix ctx
  localStage : ∀ center (centerHigh : 4 ≤ ctx.G.object.degree center)
    (Assigned : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex → Prop)
    (assignedDecidable : ∀ carrier, Decidable (Assigned carrier))
    (first second : FanClosedOpenPort ctx center centerHigh)
    (pair : Graph.FanClosedPort.CompatiblePair centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx)) first second)
    (assigned : Graph.FanClosedPort.AssignedPair centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      (p13FanWindowProfile ctx Assigned assignedDecidable) first second),
    FanClosedMassStage ctx center centerHigh Assigned assignedDecidable first
      second pair assigned

noncomputable def verifiedFanClosedMassPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedFanClosedPortPrefix ctx) :
    VerifiedFanClosedMassPrefix ctx where
  previous := previous
  localStage := fanClosedMassStage ctx

theorem exists_verifiedFanClosedMassPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedFanClosedMassPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedFanClosedPortPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedFanClosedMassPrefix ctx previous⟩

end Erdos64EG.Internal
