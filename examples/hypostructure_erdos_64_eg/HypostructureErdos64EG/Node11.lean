import Hypostructure.Graph.BoundariedAtom
import HypostructureErdos64EG.Node10

/-!
# Diagram node 11: proper boundaried atoms and degree profiles

Graph registers the universal family of proper connected atom occurrences in
the live minimal graph and derives each atom's uncapped boundary-degree
profile.  The application supplies no profile, successor payload, or route.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- The minimal context inherited through node 10 by a framework query. -/
def node4ContextAtNode10Query :
    Core.Residual.Focus.ActiveQuery Node10Focus
      (fun _stage _active =>
        Core.MinimalCounterexampleContext problem Target EGProgress) :=
  node4ContextAtNode9Query.preserve

/-- Exact accumulated stage emitted by Graph's boundaried-atom executor. -/
abbrev Node11Stage :=
  Graph.FocusedBoundariedAtomStage Node10Focus node4ContextAtNode10Query

/-- Execute node 11 from the literal node-10 predecessor. -/
noncomputable def node11 (previous : Node10Stage.{u}) : Node11Stage.{u} :=
  Graph.executeFocusedBoundariedAtomFamily Node10Focus
    node4ContextAtNode10Query previous

/-- Focus inherited by node 12. -/
abbrev Node11Focus :=
  Graph.FocusedBoundariedAtomProfile Node10Focus node4ContextAtNode10Query

/-- Query Graph's generated family of proper atoms and exact profiles. -/
def node11AtomFamilyQuery :=
  Graph.focusedBoundariedAtomFamilyQuery Node10Focus node4ContextAtNode10Query

@[simp] theorem node11_previous (previous : Node10Stage.{u}) :
    (node11 previous).previous = previous :=
  rfl

/-- Every registered profile coordinate is Graph's uncapped local degree. -/
theorem node11_boundaryDegreeProfile (stage : Node11Stage.{u})
    (active : Node11Focus.Active stage)
    (atom : Graph.ProperBoundariedAtom
      (node4ContextAtNode10Query.read stage.previous active).G)
    (vertex : atom.decomposition.interface.Vertex) :
    (node11AtomFamilyQuery.read stage active atom).boundaryDegreeProfile vertex =
      atom.decomposition.piece.boundaryDegree vertex :=
  (node11AtomFamilyQuery.read stage active atom).profile_apply vertex

#print axioms node11
#print axioms node11_boundaryDegreeProfile

end HypostructureErdos64EG
