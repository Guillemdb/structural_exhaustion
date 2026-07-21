import Hypostructure.CT10.Automation
import Hypostructure.Graph.Finite

/-!
# Graph specialization of CT10

This adapter classifies vertices of the exact graph read from the predecessor.
The vertex order is the graph object's registered finite schedule; the class
universe remains a separate residual-owned query.  No graph, attachment,
subgraph, or refinement carrier is enumerated here.
-/

namespace Hypostructure.Graph.CT10

universe uPrevious uVertex uClass uPromotion

/-- CT10 semantics for classifying vertices of the current finite graph. -/
@[implicit_reducible]
def vertexSpec {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Class : Previous -> Type uClass)
    (Promotion : Previous -> Type uPromotion)
    (classOf : (previous : Previous) ->
      (object.read previous).Vertex -> Class previous)
    (Direct : (previous : Previous) -> Class previous -> Prop)
    (promote : (previous : Previous) ->
      Class previous -> Promotion previous) :
    _root_.Hypostructure.CT10.Spec Previous where
  Datum := fun previous => (object.read previous).Vertex
  Class := Class
  Promotion := Promotion
  classOf := classOf
  Direct := Direct
  promote := promote

/-- The graph-owned vertex enumeration viewed as Core execution data. -/
def vertexData {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex}) :
    Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (object.read previous).Vertex :=
  object.map fun previous _current =>
    Core.Finite.Enumeration.ofFinEnum (object.read previous).vertices

/-- Build the generic CT10 capability for residual-owned vertex classes. -/
def vertexCapability {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Class : Previous -> Type uClass)
    (Promotion : Previous -> Type uPromotion)
    (classOf : (previous : Previous) ->
      (object.read previous).Vertex -> Class previous)
    (Direct : (previous : Previous) -> Class previous -> Prop)
    (promote : (previous : Previous) ->
      Class previous -> Promotion previous)
    (classes : Core.Residual.Query Previous fun previous =>
      Core.Finite.CompleteEnumeration (Class previous))
    (directDecidable : (previous : Previous) ->
      (cls : Class previous) -> Decidable (Direct previous cls))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT10.localCheckBound
          (vertexSpec object Class Promotion classOf Direct promote)
          (vertexData object) classes previous <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT10.Capability
      (vertexSpec object Class Promotion classOf Direct promote) where
  data := vertexData object
  classes := classes
  directDecidable := directDecidable
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.Graph.CT10
