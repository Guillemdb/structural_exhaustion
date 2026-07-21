import Hypostructure.CT12.Automation
import Hypostructure.Graph.Object

/-!
# Graph adapter for CT12

The adapter derives a vertex-peeling profile from the finite vertex schedule
already carried by a queried graph object.  It performs no graph enumeration,
peeling recursion, branch selection, routing, or ledger update.
-/

namespace Hypostructure.Graph.CT12

universe uPrevious uVertex

/-- Exact graph-vertex schedule read through the same predecessor query. -/
def vertexSchedule
    {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex}) :
    Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (object.read previous).Vertex :=
  object.map fun previous _object =>
    Core.Finite.Enumeration.ofFinEnum (object.read previous).vertices

/-- Canonical CT12 list-peeling profile for residual-owned graph vertices. -/
def vertexPeelingProfile
    {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex}) :
    _root_.Hypostructure.CT12.ListPeeling.Profile Previous where
  Value := fun previous => (object.read previous).Vertex
  schedule := vertexSchedule object

/-- Framework-owned graph-vertex peeling execution. -/
def peelVertices
    {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex}) (previous : Previous) :=
  _root_.Hypostructure.CT12.ListPeeling.run
    (vertexPeelingProfile object) previous

end Hypostructure.Graph.CT12
