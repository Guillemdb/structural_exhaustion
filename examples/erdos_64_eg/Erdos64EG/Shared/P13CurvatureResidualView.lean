import Erdos64EG.Shared.CT15RemainderCurvature
import Erdos64EG.Shared.P13SequentialWindowLedger
import StructuralExhaustion.Core.ConditionalFibreRank
import StructuralExhaustion.Graph.FiniteSupportOutsideContext

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Curvature response view of the accumulated residual

This module contains no route and no application-owned state family.  It
specializes framework views of the one accumulated node-[21] completion
ledger: `RealizedProjection` supplies the exact remainder carrier and
`FiniteSupportOutsideContext` restricts a chosen realizing completion outside
one declared curvature support.
-/

/-- The exact remainder-state carrier already used by node [49], exposed at
its first mathematical use rather than reconstructed by a later node. -/
abbrev P13AccumulatedRemainderState
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {rate : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx rate) :=
  Core.DependentOwnerGlueCapacity.RealizedProjection
    aggregate.JointState (SimpleGraph (P13RemainderVertex ctx))
      aggregate.remainderGraph

/-- Exact enumeration inherited from the framework's realized projection. -/
@[implicit_reducible]
noncomputable def p13AccumulatedRemainderStates
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {rate : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx rate) :
    FinEnum (P13AccumulatedRemainderState aggregate) :=
  Core.DependentOwnerGlueCapacity.realizedProjectionEnumeration
    aggregate.jointStates aggregate.remainderGraph

/-- A live local package has a literal first state. -/
private noncomputable def p13RetainedDefaultChoice
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {rate : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx rate)
    (owner : Fin aggregate.retained.length) :
    P13RetainedLocalChoice aggregate.retained owner := by
  let package := (aggregate.retained.get owner).package
  have positive : 0 < package.states.values.length := by
    have ratePositive : 0 < 2 ^ (118 * package.scaleMultiplicity) :=
      Nat.pow_pos (by decide)
    have lower := package.stateCount_gt_ratePower
    rw [package.profileExact] at lower
    exact ratePositive.trans lower
  let state := package.states.values[0]'positive
  refine ⟨state, ?_⟩
  change state ∈ package.states.values
  simpa [state] using
    (List.getElem_mem package.states.values 0 positive)

/-- Every accumulated hot aggregate supplies one literal joint state. -/
noncomputable def p13AccumulatedJointState
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {rate : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx rate) : aggregate.JointState :=
  aggregate.glue (p13RetainedDefaultChoice aggregate)

/-- The exact realized remainder carrier is nonempty because it contains the
projection of the accumulated joint state. -/
noncomputable def p13AccumulatedRemainderWitness
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {rate : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx rate) :
    P13AccumulatedRemainderState aggregate :=
  Core.DependentOwnerGlueCapacity.realizedProjectionValue
    aggregate.remainderGraph (p13AccumulatedJointState aggregate)

theorem p13AccumulatedRemainderStates_nonempty
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {rate : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx rate) :
    0 < (p13AccumulatedRemainderStates aggregate).toOrderedCollection.values.length := by
  rw [List.length_pos_iff]
  exact List.ne_nil_of_mem
    ((p13AccumulatedRemainderStates aggregate).mem_orderedValues
      (p13AccumulatedRemainderWitness aggregate))

/-- Choose the realizing joint completion already certified by membership in
the framework-owned realized projection. -/
noncomputable def p13AccumulatedRealizingJoint
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {rate : P13BarrierRateCertificate}
    {aggregate : P13SequentialHotAggregate ctx rate}
    (state : P13AccumulatedRemainderState aggregate) : aggregate.JointState :=
  Classical.choose state.property

/-- Framework-normalized outside context of one literal curvature support in
one realizing completion. -/
noncomputable def p13AccumulatedCurvatureContext
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {rate : P13BarrierRateCertificate}
    {aggregate : P13SequentialHotAggregate ctx rate}
    (coordinate : P13CurvatureCoordinate ctx)
    (state : P13AccumulatedRemainderState aggregate) :
    Graph.PackedBoundariedGluing.Context ctx.G.Vertex :=
  Graph.FiniteSupportOutsideContext.context
    (aggregate.global (p13AccumulatedRealizingJoint state)).object
    (p13CurvatureSupport coordinate)

/-- A retained state is curvature-flat at a coordinate precisely when its
exact support response against the framework-normalized outside context does
not hit the target. -/
noncomputable def p13AccumulatedCurvatureAccepts
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {rate : P13BarrierRateCertificate}
    {aggregate : P13SequentialHotAggregate ctx rate}
    (coordinate : P13CurvatureCoordinate ctx)
    (state : P13AccumulatedRemainderState aggregate) : Bool :=
  !(p13CurvatureResponseProfile ctx).responseSystem.response coordinate
    (p13AccumulatedCurvatureContext coordinate state)

/-- Thin P13 instantiation of Core's conditional-fibre rank profile on the
literal accumulated remainder carrier.  All scheduling, filtering, rank
splitting, and product telescoping remain framework-owned. -/
noncomputable def p13AccumulatedCurvatureRankProfile
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {rate : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx rate) :
    Core.ConditionalFibreRank.Profile where
  State := P13AccumulatedRemainderState aggregate
  Coordinate := P13CurvatureCoordinate ctx
  incoming := (p13AccumulatedRemainderStates aggregate).toOrderedCollection
  coordinates := (p13CurvatureCoordinates ctx).toOrderedCollection
  accepts := p13AccumulatedCurvatureAccepts
  safe := 543958
  flat := 111286
  stateCount := Nat.card (P13AccumulatedRemainderState aggregate)
  stateCount_eq := by
    exact (Core.Enumeration.natCard_eq
      (p13AccumulatedRemainderStates aggregate)).trans (by simp)
  incomingNonempty := p13AccumulatedRemainderStates_nonempty aggregate

end Erdos64EG.Internal
