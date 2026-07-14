import Erdos64EG.CT9TriangularCrossShoulder
import StructuralExhaustion.Graph.FanClosedPort

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT5: fan-compatible open pairs give fan-closed local data

The application supplies the actual packed-window set `W`, its exact
remainder `R = G - W`, and the Type-B assignment predicate.  The framework
derives the two fan-closure conclusions, the four distinct local carriers,
and the complete constant-work CT5 execution.
-/

/-- Erdős `P₁₃` window/remainder interpretation of the generic fan profile.
Only the assigned-incidence predicate remains an input of the later Type-B
construction. -/
noncomputable def p13FanWindowProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (Assigned : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex → Prop)
    (assignedDecidable : ∀ carrier, Decidable (Assigned carrier)) :
    Graph.FanClosedPort.FanWindowProfile ctx.G.Vertex where
  WindowSide := fun vertex => vertex ∈ p13CoveredVertices ctx
  RemainderSide := fun vertex => vertex ∈ p13RemainderVertices ctx
  Assigned := Assigned
  windowDecidable := fun vertex => by classical infer_instance
  remainderDecidable := fun vertex => by classical infer_instance
  assignedDecidable := assignedDecidable
  remainder_not_window := by
    intro vertex remainder
    simpa [p13RemainderVertices, p13CoveredVertices,
      Graph.InducedPathPacking.remainderVertices] using remainder

abbrev FanClosedOpenPort
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center) :=
  Graph.FanClosedPort.OpenPort centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

abbrev FanClosedPairStage
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
  Graph.FanClosedPort.VerifiedStage
    (base := fixedPackedInput ctx)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx Assigned assignedDecidable)
    first second pair assigned

noncomputable def fanClosedPairStage
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
    FanClosedPairStage ctx center centerHigh Assigned assignedDecidable first
      second pair assigned :=
  Graph.FanClosedPort.verifiedStage
    (base := fixedPackedInput ctx)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx Assigned assignedDecidable)
    first second pair assigned

structure VerifiedFanClosedPortPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedTriangularCrossShoulderPrefix ctx
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
    FanClosedPairStage ctx center centerHigh Assigned assignedDecidable first
      second pair assigned

noncomputable def verifiedFanClosedPortPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTriangularCrossShoulderPrefix ctx) :
    VerifiedFanClosedPortPrefix ctx where
  previous := previous
  localStage := fanClosedPairStage ctx

theorem exists_verifiedFanClosedPortPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedFanClosedPortPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedTriangularCrossShoulderPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedFanClosedPortPrefix ctx previous⟩

end Erdos64EG.Internal
