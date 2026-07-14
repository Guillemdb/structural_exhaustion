import Erdos64EG.CT1FanWindowCycle
import StructuralExhaustion.Graph.TwoWindowCycle

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT1: direct cycles through two packed windows

This implements `lem:typeB-two-window-cycles`. The reusable graph profile owns
orientation-independent bridges, support disjointness, the exact cycle length,
and the CT1 execution. The Erdős layer only specializes the length predicate
and retains the already selected target-avoiding context.
-/

abbrev TwoWindowCycleStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.TwoWindowCycle.VerifiedAvoidingStage
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline ()
    (packedStaticInput.fixedContext ctx).avoids

def twoWindowCycleStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    TwoWindowCycleStage ctx :=
  Graph.TwoWindowCycle.verifiedAvoidingStage
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline ()
    (packedStaticInput.fixedContext ctx).avoids

theorem twoWindowCT1_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.FanWindowCycle.runAvoiding
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline ()
      (packedStaticInput.fixedContext ctx).avoids).result.terminal = .avoiding :=
  (twoWindowCycleStage ctx).terminal

theorem twoWindowCT1_checks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.FanWindowCycle.runAvoiding
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline ()
      (packedStaticInput.fixedContext ctx).avoids).checks = 0 :=
  (twoWindowCycleStage ctx).checks

theorem packedTwoWindow_directCycleFree
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {firstOrder secondOrder : Nat}
    {firstPath : SimpleGraph.pathGraph firstOrder ↪g ctx.G.object.graph}
    {secondPath : SimpleGraph.pathGraph secondOrder ↪g ctx.G.object.graph}
    (data : Graph.TwoWindowCycle.Data firstPath secondPath) :
    Graph.TwoWindowCycle.DirectCycleFree PowerOfTwoLength data :=
  (twoWindowCycleStage ctx).directFree data

structure VerifiedTwoWindowCyclePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedDirectFanWindowPrefix ctx
  stage : TwoWindowCycleStage ctx

def verifiedTwoWindowCyclePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedDirectFanWindowPrefix ctx) :
    VerifiedTwoWindowCyclePrefix ctx where
  previous := previous
  stage := twoWindowCycleStage ctx

theorem exists_verifiedTwoWindowCyclePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedTwoWindowCyclePrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedDirectFanWindowPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedTwoWindowCyclePrefix ctx previous⟩

end Erdos64EG.Internal
