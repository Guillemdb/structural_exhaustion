import Erdos64EG.Future.P13FixedSkeletonBranchExcessCorridors
import Erdos64EG.Future.P13SameWindowBaseScaleSplit

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Local F5 scale routing for every branch-excess corridor

The manuscript treats every selected cold half-edge separately.  After the
computed first-failure scan, an F1 hit and an F4 surplus leave immediately.
An F5 structural germ is compared with the fixed
`Q_base = 4^2 * 13^2 * 2^13`; the result is either an actual support bound or
the exact long-support inequality.  This file performs only that stored
length comparison and never enumerates the finite state universe whose
cardinality defines `Q_base`.
-/

inductive P13BranchExcessScaleRoute
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : P13AmbientCubicWindow ctx}
    (corridor : P13BranchExcessCorridor ctx window) : Type u where
  | target
      (hit : InducedPathColdCorridor.Producer.TargetHit
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength)
  | surplus
      (handoff : InducedPathColdCorridor.Producer.SurplusHandoff
        (p13SelectedWindowCorridorProducer ctx))
  | short
      (germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength corridor.stub)
      (bounded :
        ((p13SelectedWindowCorridorProducer ctx).ambientReturn
          corridor.stub).support.length ≤ p13ColdD1D3BaseThreshold)
  | long
      (germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength corridor.stub)
      (exceeds : p13ColdD1D3BaseThreshold <
        ((p13SelectedWindowCorridorProducer ctx).ambientReturn
          corridor.stub).support.length)

/-- Inspect the already computed F1/F4/F5 result and, only on F5, execute the
single fixed-threshold comparison. -/
noncomputable def routeP13BranchExcessScale
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : P13AmbientCubicWindow ctx}
    (corridor : P13BranchExcessCorridor ctx window) :
    P13BranchExcessScaleRoute corridor := by
  cases corridor.result with
  | first _ event =>
      cases event with
      | f1 _ hit => exact .target hit
      | f2 _ _ impossible => exact nomatch impossible
      | f3 _ _ _ impossible => exact nomatch impossible
      | f4 _ _ _ _ handoff => exact .surplus handoff
  | germ _ germ =>
      cases (p13SelectedWindowCorridorProducer ctx).classifyScale
          PowerOfTwoLength corridor.stub germ p13ColdD1D3BaseThreshold with
      | short bounded => exact .short germ bounded
      | long exceeds => exact .long germ exceeds

inductive P13BranchExcessScaleTag
  | target
  | surplus
  | short
  | long
  deriving DecidableEq

def P13BranchExcessScaleRoute.tag
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : P13AmbientCubicWindow ctx}
    {corridor : P13BranchExcessCorridor ctx window} :
    P13BranchExcessScaleRoute corridor → P13BranchExcessScaleTag
  | .target _ => .target
  | .surplus _ => .surplus
  | .short _ _ => .short
  | .long _ _ => .long

/-- One globally scheduled branch-excess source and its computed scale route. -/
structure P13BranchExcessScaleEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Type u where
  source : Sigma fun window : P13AmbientCubicWindow ctx =>
    P13BranchExcessCorridor ctx window
  route : P13BranchExcessScaleRoute source.2
  routeExact : route = routeP13BranchExcessScale source.2

noncomputable def p13BranchExcessScaleEntries
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (P13BranchExcessScaleEntry ctx) :=
  (p13BranchExcessCorridors ctx).map fun source =>
    ⟨source, routeP13BranchExcessScale source.2, rfl⟩

theorem p13BranchExcessScaleEntries_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13BranchExcessScaleEntries ctx).length =
      13 * (p13AmbientCubicWindows ctx).card := by
  rw [p13BranchExcessScaleEntries, List.length_map,
    p13BranchExcessCorridors_length]

noncomputable def p13BranchExcessScaleEntriesWithTag
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (tag : P13BranchExcessScaleTag) :
    List (P13BranchExcessScaleEntry ctx) :=
  (p13BranchExcessScaleEntries ctx).filter fun entry => entry.route.tag = tag

private theorem fourTagPartitionLength
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entries : List (P13BranchExcessScaleEntry ctx)) :
    (entries.filter fun entry => entry.route.tag =
        P13BranchExcessScaleTag.target).length +
      (entries.filter fun entry => entry.route.tag =
        P13BranchExcessScaleTag.surplus).length +
      (entries.filter fun entry => entry.route.tag =
        P13BranchExcessScaleTag.short).length +
      (entries.filter fun entry => entry.route.tag =
        P13BranchExcessScaleTag.long).length = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases tagEquation : entry.route.tag <;>
        simp [tagEquation] <;> omega

/-- Exact all-selected-half-edge scale partition. -/
theorem p13BranchExcessScaleEntries_partition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13BranchExcessScaleEntriesWithTag ctx .target).length +
      (p13BranchExcessScaleEntriesWithTag ctx .surplus).length +
      (p13BranchExcessScaleEntriesWithTag ctx .short).length +
      (p13BranchExcessScaleEntriesWithTag ctx .long).length =
      13 * (p13AmbientCubicWindows ctx).card := by
  rw [p13BranchExcessScaleEntriesWithTag,
    p13BranchExcessScaleEntriesWithTag,
    p13BranchExcessScaleEntriesWithTag,
    p13BranchExcessScaleEntriesWithTag,
    fourTagPartitionLength,
    p13BranchExcessScaleEntries_length]

end Erdos64EG.Internal
