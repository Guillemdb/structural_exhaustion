import Hypostructure.CT16.Automation
import Hypostructure.Graph.Object

/-!
# Graph adapter for CT16 vertex support

The packed graph's explicit vertex schedule is read through the supplied
object query.  Graph contributes only vertex-support and closed-code semantics;
the CT16 runner remains entirely domain independent.
-/

namespace Hypostructure.Graph.CT16

universe uPrevious uVertex uCode

/-- Residual-owned exact vertex schedule of the queried graph object. -/
def vertexCoordinates {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex}) :
    Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (object.read previous).Vertex :=
  object.map fun previous _selected =>
    Core.Finite.Enumeration.ofFinEnum (object.read previous).vertices

/-- CT16 semantics for whole vertex support and one computed graph code. -/
def vertexSpec {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (InSupport : (selected : FiniteObject.{uVertex}) ->
      selected.Vertex -> Prop)
    (ClosedCode : Type uCode)
    (closedCode : FiniteObject.{uVertex} -> ClosedCode)
    (targetCode : ClosedCode) :
    _root_.Hypostructure.CT16.Spec Previous where
  Coordinate := fun previous => (object.read previous).Vertex
  InSupport := fun previous coordinate =>
    InSupport (object.read previous) coordinate
  ClosedCode := fun _previous => ClosedCode
  closedCode := fun previous => closedCode (object.read previous)
  targetCode := fun _previous => targetCode

/-- Build the graph CT16 capability.  Vertex enumeration is derived from the
queried packed object; no ambient graph or code universe is enumerated.  The
graph code implementation is counted separately from its mathematical
denotation and carries an exact predecessor-indexed budget. -/
def vertexCapability {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (InSupport : (selected : FiniteObject.{uVertex}) ->
      selected.Vertex -> Prop)
    (ClosedCode : Type uCode)
    (closedCode : FiniteObject.{uVertex} -> ClosedCode)
    (targetCode : ClosedCode)
    (computeClosedCode : FiniteObject.{uVertex} -> Core.Counted ClosedCode)
    (computeClosedCode_correct : forall selected,
      (computeClosedCode selected).value = closedCode selected)
    (codeComputationBudget : Core.PolynomialCheckBudget Previous)
    (computeClosedCode_checks : forall previous,
      (computeClosedCode (object.read previous)).checks =
        codeComputationBudget.checks previous)
    (inSupportDecidable : (selected : FiniteObject.{uVertex}) ->
      (vertex : selected.Vertex) -> Decidable (InSupport selected vertex))
    (codeDecidableEq : DecidableEq ClosedCode) :
    _root_.Hypostructure.CT16.Capability
      (vertexSpec object InSupport ClosedCode closedCode targetCode) where
  coordinates := vertexCoordinates object
  inSupportDecidable := fun previous coordinate =>
    inSupportDecidable (object.read previous) coordinate
  codeComputation := {
    run := fun previous => computeClosedCode (object.read previous)
    correct := fun previous =>
      computeClosedCode_correct (object.read previous)
    budget := codeComputationBudget
    checks_eq := computeClosedCode_checks
  }
  equalityDecision :=
    _root_.Hypostructure.CT16.CodeEqualityDecision.unitCost
      codeComputationBudget.size (fun _previous => codeDecidableEq)

end Hypostructure.Graph.CT16
