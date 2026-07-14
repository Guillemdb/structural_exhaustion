import Erdos64EG.CT14FanClosedPortMass
import Erdos64EG.CT1HighCenterStructure
import StructuralExhaustion.Graph.HybridFanIncidence

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT14: hybrid window/non-window incidence budget

The framework-owned CT14→CT14 refinement consumes the actual capacity
residual from the cubic-closed mass stage.  This application file supplies
only the Erdős `P₁₃` profile, target-derived four-cycle avoidance, and the
marked-fan branch bound `degree center ≤ 8`.
-/

abbrev HybridFanIncidenceStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (degreeLeEight : ctx.G.object.degree center ≤ 8)
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
  Graph.HybridFanIncidence.VerifiedStage
    (base := fixedPackedInput ctx)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx Assigned assignedDecidable)
    first second pair assigned (fourCycleFree ctx) degreeLeEight

noncomputable def hybridFanIncidenceStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (degreeLeEight : ctx.G.object.degree center ≤ 8)
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
    HybridFanIncidenceStage ctx center centerHigh degreeLeEight Assigned
      assignedDecidable first second pair assigned :=
  Graph.HybridFanIncidence.verifiedStage centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx Assigned assignedDecidable)
    first second pair assigned (fourCycleFree ctx) degreeLeEight

structure VerifiedHybridFanIncidencePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedFanClosedMassPrefix ctx
  localStage : ∀ center (centerHigh : 4 ≤ ctx.G.object.degree center)
    (degreeLeEight : ctx.G.object.degree center ≤ 8)
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
    HybridFanIncidenceStage ctx center centerHigh degreeLeEight Assigned
      assignedDecidable first second pair assigned

noncomputable def verifiedHybridFanIncidencePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedFanClosedMassPrefix ctx) :
    VerifiedHybridFanIncidencePrefix ctx where
  previous := previous
  localStage := hybridFanIncidenceStage ctx

theorem exists_verifiedHybridFanIncidencePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedHybridFanIncidencePrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedFanClosedMassPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedHybridFanIncidencePrefix ctx previous⟩

end Erdos64EG.Internal
