import Hypostructure.Graph.Obstruction

/-!
# Induced-path targets for graph CT1

An induced path is one instance of the graph layer's generic induced
obstruction target.  The path length is application data; CT1 only sees the
generic obstruction interface.
-/

namespace Hypostructure.Graph

universe uPrevious uVertex

/-- A literal induced copy of the path on `order` vertices. -/
def HasInducedPath (object : FiniteObject.{uVertex}) (order : Nat) : Prop :=
  HasInducedObstruction (SimpleGraph.pathGraph order) object

/-- The graph contains no induced path on `order` vertices. -/
def InducedPathFree (object : FiniteObject.{uVertex}) (order : Nat) : Prop :=
  InducedObstructionFree (SimpleGraph.pathGraph order) object

/-- The path on `order` vertices, viewed as a generic induced obstruction. -/
abbrev inducedPathObstruction (order : Nat) :=
  SimpleGraph.pathGraph order

namespace CT1

/-- Focused proof-carrying CT1 encoding for induced paths in a graph read from
the active residual. -/
def focusedInducedPathEncoding {Previous : Type uPrevious}
    (profile : Core.Residual.Focus.Profile Previous)
    (object : Core.Residual.Focus.ActiveQuery profile fun _previous _active =>
      FiniteObject.{uVertex})
    (order : Nat) :
    _root_.Hypostructure.CT1.FocusedCertificateEncoding.Encoding profile
      (fun previous active =>
        HasInducedPath (object.read previous active) order) :=
  focusedInducedObstructionEncoding profile object (inducedPathObstruction order)

/-- Counted focused CT1 execution for an induced-path certificate target. -/
noncomputable def executeFocusedInducedPathCounted {Previous : Type uPrevious}
    (profile : Core.Residual.Focus.Profile Previous)
    (object : Core.Residual.Focus.ActiveQuery profile fun _previous _active =>
      FiniteObject.{uVertex})
    (order : Nat) (previous : Previous) :
    Core.Counted
      (_root_.Hypostructure.CT1.FocusedCertificateEncoding.Stage
        (focusedInducedPathEncoding profile object order)) :=
  (focusedInducedPathEncoding profile object order).runCounted previous

/-- Public focused CT1 stage for an induced-path certificate target. -/
noncomputable def executeFocusedInducedPath {Previous : Type uPrevious}
    (profile : Core.Residual.Focus.Profile Previous)
    (object : Core.Residual.Focus.ActiveQuery profile fun _previous _active =>
      FiniteObject.{uVertex})
    (order : Nat) (previous : Previous) :
    _root_.Hypostructure.CT1.FocusedCertificateEncoding.Stage
      (focusedInducedPathEncoding profile object order) :=
  (executeFocusedInducedPathCounted profile object order previous).value

end CT1

end Hypostructure.Graph
