import Hypostructure.CT4.Automation
import Hypostructure.Graph.Object

/-!
# Graph adapter for CT4 vertex charging

Graph contributes only the packed graph's existing vertex schedule and the
meaning of vertex eligibility, weight, and capacity.  CT4 still owns every
assignment, fibre, decision, route, and output.
-/

namespace Hypostructure.Graph.CT4

universe uPrevious uDemand uVertex

/-- Residual-owned exact vertex-payer schedule of the queried graph. -/
def vertexPayers {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex}) :
    Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (object.read previous).Vertex :=
  object.map fun previous _selected =>
    Core.Finite.Enumeration.ofFinEnum (object.read previous).vertices

/-- Shared CT4 semantics for charging demands to vertices of the graph read
from the predecessor ledger. -/
def vertexChargingSpec {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Demand : Previous -> Type uDemand)
    (Eligible : (previous : Previous) -> (selected : FiniteObject.{uVertex}) ->
      Demand previous -> selected.Vertex -> Prop)
    (demandWeight : (previous : Previous) ->
      (selected : FiniteObject.{uVertex}) -> Demand previous -> Nat)
    (capacity : (previous : Previous) ->
      (selected : FiniteObject.{uVertex}) -> selected.Vertex -> Nat)
    (required : (previous : Previous) ->
      FiniteObject.{uVertex} -> Nat) :
    _root_.Hypostructure.CT4.Spec Previous where
  Demand := Demand
  Payer := fun previous => (object.read previous).Vertex
  Eligible := fun previous demand payer =>
    Eligible previous (object.read previous) demand payer
  demandWeight := fun previous demand =>
    demandWeight previous (object.read previous) demand
  capacity := fun previous payer =>
    capacity previous (object.read previous) payer
  required := fun previous => required previous (object.read previous)

/-- Build the graph vertex-charging capability.  Only the demand schedule is
application-supplied; the payer schedule is derived from the queried graph. -/
def vertexChargingCapability {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Demand : Previous -> Type uDemand)
    (Eligible : (previous : Previous) -> (selected : FiniteObject.{uVertex}) ->
      Demand previous -> selected.Vertex -> Prop)
    (demandWeight : (previous : Previous) ->
      (selected : FiniteObject.{uVertex}) -> Demand previous -> Nat)
    (capacity : (previous : Previous) ->
      (selected : FiniteObject.{uVertex}) -> selected.Vertex -> Nat)
    (required : (previous : Previous) -> FiniteObject.{uVertex} -> Nat)
    (demands : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Demand previous))
    (eligibleDecidable : (previous : Previous) ->
      (selected : FiniteObject.{uVertex}) -> (demand : Demand previous) ->
        (payer : selected.Vertex) ->
          Decidable (Eligible previous selected demand payer))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT4.localCheckBound
          (demands.read previous) (vertexPayers object |>.read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT4.Capability
      (vertexChargingSpec object Demand Eligible demandWeight capacity
        required) where
  demands := demands
  payers := vertexPayers object
  eligibleDecidable := fun previous demand payer =>
    eligibleDecidable previous (object.read previous) demand payer
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.Graph.CT4
