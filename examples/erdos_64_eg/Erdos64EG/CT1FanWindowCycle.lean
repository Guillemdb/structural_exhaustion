import Erdos64EG.CT14HybridFanIncidence
import StructuralExhaustion.Graph.FanWindowCycle

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT1: direct fan-window cycle elimination

This is the exact implementation of `lem:typeB-direct-fan-window-cycles`.
The framework graph profile constructs all three manuscript cycle forms from
literal attachment data and executes certificate-driven CT1.  On the selected
counterexample branch, the zero-enumeration avoiding run proves every closed
pair direct-cycle-free.  The Erdős layer supplies only its power-of-two target
and the already verified target-avoiding context.
-/

abbrev DirectFanWindowStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.FanWindowCycle.VerifiedAvoidingStage
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline ()
    (packedStaticInput.fixedContext ctx).avoids

def directFanWindowStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    DirectFanWindowStage ctx :=
  Graph.FanWindowCycle.verifiedAvoidingStage
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline ()
    (packedStaticInput.fixedContext ctx).avoids

theorem directFanWindowCT1_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.FanWindowCycle.runAvoiding
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline ()
      (packedStaticInput.fixedContext ctx).avoids).result.terminal = .avoiding :=
  (directFanWindowStage ctx).terminal

theorem directFanWindowCT1_checks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.FanWindowCycle.runAvoiding
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline ()
      (packedStaticInput.fixedContext ctx).avoids).checks = 0 :=
  (directFanWindowStage ctx).checks

/-- Literal direct-cycle-free conclusion for every supplied closed pair in a
selected induced path window.  No conclusion is an application field: it is
derived from the framework cycle constructors and `ctx.avoids`. -/
theorem sameWindowPair_directCycleFree
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {order : Nat}
    {path : SimpleGraph.pathGraph order ↪g ctx.G.object.graph}
    (pair : Graph.FanWindowCycle.ClosedPair path) :
    Graph.FanWindowCycle.DirectCycleFree PowerOfTwoLength pair :=
  (directFanWindowStage ctx).directFree pair

structure VerifiedDirectFanWindowPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedHybridFanIncidencePrefix ctx
  stage : DirectFanWindowStage ctx

def verifiedDirectFanWindowPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedHybridFanIncidencePrefix ctx) :
    VerifiedDirectFanWindowPrefix ctx where
  previous := previous
  stage := directFanWindowStage ctx

theorem exists_verifiedDirectFanWindowPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedDirectFanWindowPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedHybridFanIncidencePrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedDirectFanWindowPrefix ctx previous⟩

end Erdos64EG.Internal
