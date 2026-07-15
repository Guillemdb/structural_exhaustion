import StructuralExhaustion.Core.GreedyMatchingStar
import StructuralExhaustion.Graph.SurplusClasswiseOverload

namespace StructuralExhaustion.Graph.SurplusHomogeneousPattern

open StructuralExhaustion

universe u

/-!
# Homogeneous matching--star audit of a coupled surplus overload

The input is exactly the overloaded token--role fibre emitted by the classwise
CT9 stage.  The pair schedule is unchanged.  Depending on the literal token
constructor, the reusable greedy extractor runs at the corresponding authored
threshold.
-/

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (activation : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

abbrev Pair := SurplusPairResponse.ScheduledPair (setup := setup)
abbrev Slot := SurplusPortActivation.Slot setup

@[implicit_reducible]
def slots : FinEnum (Slot (setup := setup)) :=
  SurplusPairResponse.slotEnumeration (setup := setup)

noncomputable abbrev Profile (windowSize remainderSize primitiveSize : Nat) :=
  SurplusClasswiseOverload.profile activation
    windowSize remainderSize primitiveSize

noncomputable abbrev Items := SurplusClasswiseOverload.items (setup := setup)

noncomputable def fibreSource
    (windowSize remainderSize primitiveSize : Nat)
    (overload : (Profile activation windowSize remainderSize primitiveSize).Overload
      ctx.toBranchContext (Items (setup := setup))) :
    Core.OrderedCollection (Pair (setup := setup)) :=
  overload.fibreItems

inductive Audit (windowSize remainderSize primitiveSize : Nat)
    (routed : SurplusClasswiseOverload.RoutedOverload activation
      windowSize remainderSize primitiveSize) : Type _ where
  | window
      (route : SurplusClasswiseOverload.tokenClass
        routed.overload.residual.label.1 = .window)
      (stage : Core.GreedyMatchingStar.VerifiedStage (slots (setup := setup))
        (fibreSource activation windowSize remainderSize primitiveSize
          routed.overload) windowSize) : Audit windowSize remainderSize primitiveSize routed
  | remainder
      (route : SurplusClasswiseOverload.tokenClass
        routed.overload.residual.label.1 = .remainder)
      (stage : Core.GreedyMatchingStar.VerifiedStage (slots (setup := setup))
        (fibreSource activation windowSize remainderSize primitiveSize
          routed.overload) remainderSize) : Audit windowSize remainderSize primitiveSize routed
  | primitive
      (route : SurplusClasswiseOverload.tokenClass
        routed.overload.residual.label.1 = .primitive)
      (stage : Core.GreedyMatchingStar.VerifiedStage (slots (setup := setup))
        (fibreSource activation windowSize remainderSize primitiveSize
          routed.overload) primitiveSize) : Audit windowSize remainderSize primitiveSize routed

theorem overload_bound_window
    (windowSize remainderSize primitiveSize : Nat)
    (overload : (Profile activation windowSize remainderSize primitiveSize).Overload
      ctx.toBranchContext (Items (setup := setup)))
    (route : SurplusClasswiseOverload.tokenClass
      overload.residual.label.1 = .window) :
    Core.GreedyMatchingStar.matchingStarCap windowSize <
      (fibreSource activation windowSize remainderSize primitiveSize overload).values.length := by
  have bound := overload.classCapacity_lt_fibreItems_length
  have classEq :
      (Profile activation windowSize remainderSize primitiveSize).classOf
        overload.residual.label.1 = .window := route
  rw [classEq] at bound
  change Core.GreedyMatchingStar.matchingStarCap windowSize <
    overload.fibreItems.values.length at bound
  exact bound

theorem overload_bound_remainder
    (windowSize remainderSize primitiveSize : Nat)
    (overload : (Profile activation windowSize remainderSize primitiveSize).Overload
      ctx.toBranchContext (Items (setup := setup)))
    (route : SurplusClasswiseOverload.tokenClass
      overload.residual.label.1 = .remainder) :
    Core.GreedyMatchingStar.matchingStarCap remainderSize <
      (fibreSource activation windowSize remainderSize primitiveSize overload).values.length := by
  have bound := overload.classCapacity_lt_fibreItems_length
  have classEq :
      (Profile activation windowSize remainderSize primitiveSize).classOf
        overload.residual.label.1 = .remainder := route
  rw [classEq] at bound
  change Core.GreedyMatchingStar.matchingStarCap remainderSize <
    overload.fibreItems.values.length at bound
  exact bound

theorem overload_bound_primitive
    (windowSize remainderSize primitiveSize : Nat)
    (overload : (Profile activation windowSize remainderSize primitiveSize).Overload
      ctx.toBranchContext (Items (setup := setup)))
    (route : SurplusClasswiseOverload.tokenClass
      overload.residual.label.1 = .primitive) :
    Core.GreedyMatchingStar.matchingStarCap primitiveSize <
      (fibreSource activation windowSize remainderSize primitiveSize overload).values.length := by
  have bound := overload.classCapacity_lt_fibreItems_length
  have classEq :
      (Profile activation windowSize remainderSize primitiveSize).classOf
        overload.residual.label.1 = .primitive := route
  rw [classEq] at bound
  change Core.GreedyMatchingStar.matchingStarCap primitiveSize <
    overload.fibreItems.values.length at bound
  exact bound

/-- Execute exactly one of the three class audits selected by nodes `[139]`
and `[141]`. -/
noncomputable def audit
    (windowSize remainderSize primitiveSize : Nat)
    (routed : SurplusClasswiseOverload.RoutedOverload activation
      windowSize remainderSize primitiveSize) :
    Audit activation windowSize remainderSize primitiveSize routed := by
  cases routed.routed with
  | window route =>
      exact .window route
        (Core.GreedyMatchingStar.verifiedStage (slots (setup := setup)) _ _
          (overload_bound_window activation windowSize remainderSize primitiveSize
            routed.overload route))
  | remainder route =>
      exact .remainder route
        (Core.GreedyMatchingStar.verifiedStage (slots (setup := setup)) _ _
          (overload_bound_remainder activation windowSize remainderSize primitiveSize
            routed.overload route))
  | primitive route =>
      exact .primitive route
        (Core.GreedyMatchingStar.verifiedStage (slots (setup := setup)) _ _
          (overload_bound_primitive activation windowSize remainderSize primitiveSize
            routed.overload route))

end StructuralExhaustion.Graph.SurplusHomogeneousPattern
