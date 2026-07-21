import Erdos64EG.Shared.P13SequentialWindowLedger
import Erdos64EG.Shared.CT15RemainderCurvature
import StructuralExhaustion.Graph.FiniteSupportOutsideContext
import StructuralExhaustion.Core.LocalBooleanRealization
import StructuralExhaustion.Core.ConditionalFibreRank

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Realized remainder states and their curvature responses

This is a view of the one accumulated node-[21] compatible-completion ledger.
Core owns the realized-image carrier and its exact enumeration.  The Erdős
specialization supplies only the literal remainder projection and evaluates a
declared curvature wedge against the normalized complement of that projected
graph.  No graph family or assignment cube is constructed.
-/

/-- The exact remainder states realized by the accumulated joint-completion
carrier.  This is Core's proof-carrying image view, not an application-owned
family. -/
abbrev P13RealizedRemainderState {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) :=
  let aggregate := p13AccumulatedFinalHotAggregate node18 bounded node21
  Core.DependentOwnerGlueCapacity.RealizedProjection
    aggregate.JointState
    (SimpleGraph (P13RemainderVertex (Node21Context node18)))
    aggregate.remainderGraph

/-- Framework enumeration of exactly the realized remainder projection.  It
maps the existing joint-state enumeration and removes duplicate projections;
the Erdős layer performs no image enumeration itself. -/
@[implicit_reducible]
noncomputable def p13RealizedRemainderStates {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) :
    FinEnum (P13RealizedRemainderState node18 bounded node21) :=
  let aggregate := p13AccumulatedFinalHotAggregate node18 bounded node21
  Core.DependentOwnerGlueCapacity.realizedProjectionEnumeration
    aggregate.jointStates aggregate.remainderGraph

/-- The distinguished original compatible completion, projected to the exact
remainder carrier.  This witness is transported by the one accumulated
ledger; later nodes never reconstruct local choices to prove nonemptiness. -/
noncomputable def p13OriginalRealizedRemainderState {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) :
    P13RealizedRemainderState node18 bounded node21 := by
  let aggregate := p13AccumulatedFinalHotAggregate node18 bounded node21
  let witness := p13AccumulatedOriginalCompletionWitness node18 bounded node21
  exact ⟨aggregate.remainderGraph witness.joint, ⟨witness.joint, rfl⟩⟩

/-- Exact positivity of the realized carrier cardinality. -/
theorem p13RealizedRemainderState_card_pos {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) :
    0 < Nat.card (P13RealizedRemainderState node18 bounded node21) := by
  let enumeration := p13RealizedRemainderStates node18 bounded node21
  let state := p13OriginalRealizedRemainderState node18 bounded node21
  rw [Core.Enumeration.natCard_eq enumeration,
    ← enumeration.orderedValues_length]
  exact List.length_pos_of_mem (enumeration.mem_orderedValues state)

/-- Include a remainder vertex into the ambient vertex type. -/
def p13RemainderEmbedding
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    P13RemainderVertex ctx ↪ ctx.G.Vertex :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- A realized remainder graph regarded as an ambient finite object, with all
vertices outside the remainder isolated. -/
noncomputable def p13RealizedRemainderAmbientObject {V : Type u}
    {residual : InitialResidual V} {node18 : Node18Stage residual}
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    (state : P13RealizedRemainderState node18 bounded node21) :
    Graph.FiniteObject (Node21Context node18).G.Vertex where
  graph := state.1.map (p13RemainderEmbedding (Node21Context node18))
  input := {
    vertices := (Node21Context node18).G.object.input.vertices
    decideAdj := Classical.decRel _
  }

/-- Boolean response of one declared remainder wedge on one actually realized
remainder state.  The normalized complement context is framework-owned and
uses only the graph carried by that state. -/
noncomputable def p13RealizedRemainderResponse {V : Type u}
    {residual : InitialResidual V} {node18 : Node18Stage residual}
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    (coordinate : P13CurvatureCoordinate (Node21Context node18))
    (state : P13RealizedRemainderState node18 bounded node21) : Bool :=
  (p13CurvatureResponseProfile (Node21Context node18)).responseSystem.response
    coordinate
    (Graph.FiniteSupportOutsideContext.context
      (p13RealizedRemainderAmbientObject state)
      (p13CurvatureSupport coordinate))

/-- Exact semantic reflection of the realized-state response. -/
theorem p13RealizedRemainderResponse_true_iff {V : Type u}
    {residual : InitialResidual V} {node18 : Node18Stage residual}
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    (coordinate : P13CurvatureCoordinate (Node21Context node18))
    (state : P13RealizedRemainderState node18 bounded node21) :
    p13RealizedRemainderResponse coordinate state = true ↔
      packedStaticInput.Target
        (Graph.PackedBoundariedGluing.glue
          (Node21Context node18).G.object.input.vertices
          ((p13CurvatureResponseProfile
            (Node21Context node18)).coordinatePiece coordinate)
          (Graph.FiniteSupportOutsideContext.context
            (p13RealizedRemainderAmbientObject state)
            (p13CurvatureSupport coordinate))) :=
  (p13CurvatureResponseProfile
    (Node21Context node18)).response_true_iff coordinate _

/-- The framework Boolean-response system on exactly the remainder states
realized by the incoming accumulated ledger.  This definition introduces no
new family: both finite carriers are projections already owned by earlier
nodes. -/
noncomputable def p13RealizedCurvatureSystem {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) :
    Core.LocalBooleanRealization.System where
  Coordinate := P13CurvatureCoordinate (Node21Context node18)
  State := P13RealizedRemainderState node18 bounded node21
  coordinates := p13CurvatureCoordinates (Node21Context node18)
  states := p13RealizedRemainderStates node18 bounded node21
  value := fun state coordinate => p13RealizedRemainderResponse coordinate state

/-- The framework product-cost profile on the literal realized remainder
carrier.  The application supplies only the already-defined state carrier,
curvature coordinate schedule, and response predicate.  Core owns the
product-cost telescope recovered on the full-output branch.  This is not a
second manuscript rank. -/
noncomputable def p13RealizedCurvatureProductCostProfile {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) :
    Core.ConditionalFibreRank.Profile where
  State := P13RealizedRemainderState node18 bounded node21
  Coordinate := P13CurvatureCoordinate (Node21Context node18)
  incoming := (p13RealizedRemainderStates node18 bounded node21).toOrderedCollection
  coordinates :=
    (p13CurvatureCoordinates (Node21Context node18)).toOrderedCollection
  accepts := fun coordinate state =>
    p13RealizedRemainderResponse coordinate state
  safe := 543958
  flat := 111286
  stateCount := Nat.card (P13RealizedRemainderState node18 bounded node21)
  stateCount_eq := by
    rw [FinEnum.toOrderedCollection_length]
    rw [Core.Enumeration.natCard_eq
      (p13RealizedRemainderStates node18 bounded node21)]
  incomingNonempty := by
    rw [FinEnum.toOrderedCollection_length]
    rw [← Core.Enumeration.natCard_eq
      (p13RealizedRemainderStates node18 bounded node21)]
    exact p13RealizedRemainderState_card_pos node18 bounded node21

end Erdos64EG.Internal
