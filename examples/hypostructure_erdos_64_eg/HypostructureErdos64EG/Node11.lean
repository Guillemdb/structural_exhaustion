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

/-- Counted node-11 execution, including the inactive outcome. -/
noncomputable def node11Counted (previous : Node10Stage.{u}) :=
  Graph.executeFocusedBoundariedAtomRegistrationCounted Node10Focus
    node4ContextAtNode10Query previous

/-- Execute node 11 from the literal node-10 predecessor. -/
noncomputable def node11 (previous : Node10Stage.{u}) : Node11Stage.{u} :=
  (node11Counted previous).value

/-- Focus inherited by node 12. -/
abbrev Node11Focus :=
  Graph.FocusedBoundariedAtomProfile Node10Focus node4ContextAtNode10Query

/-- Query Graph's complete generated boundaried-atom registration. -/
def node11RegistrationQuery :=
  Graph.focusedBoundariedAtomRegistrationQuery Node10Focus
    node4ContextAtNode10Query

/-- Query Graph's private execution certificate and exact selector work. -/
def node11CertificateQuery :=
  Graph.focusedBoundariedAtomCertificateQuery Node10Focus
    node4ContextAtNode10Query

@[simp] theorem node11_previous (previous : Node10Stage.{u}) :
    (node11 previous).previous = previous :=
  rfl

/-- Every registered profile coordinate is Graph's uncapped local degree. -/
theorem node11_boundaryDegreeProfile (stage : Node11Stage.{u})
    (active : Node11Focus.Active stage)
    (atom : Graph.ProperBoundariedAtom
      (node4ContextAtNode10Query.read stage.previous active).G)
    (vertex : atom.decomposition.interface.Vertex) :
    ((node11RegistrationQuery.read stage active).family atom).boundaryDegreeProfile
        vertex =
      atom.decomposition.piece.boundaryDegree vertex :=
  ((node11RegistrationQuery.read stage active).family atom).profile_apply vertex

/-- Pieces in different uncapped boundary-degree fibres cannot be identified
by the target-complete relation used downstream. -/
theorem node11_profileMismatchRejected (stage : Node11Stage.{u})
    (active : Node11Focus.Active stage)
    {boundary : Graph.Boundary.{u}}
    {left right : Graph.BoundaryPiece boundary}
    (different : left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile) :
    ¬ Graph.BoundaryProfileTargetComplete Target left right :=
  (node11RegistrationQuery.read stage active).profileMismatchRejected different

/-- Exact total work for both active and inactive outcomes. -/
@[simp] theorem node11Counted_checks_eq_one (previous : Node10Stage.{u}) :
    (node11Counted previous).checks = 1 := by
  change
    (Graph.executeFocusedBoundariedAtomRegistrationCounted Node10Focus
      node4ContextAtNode10Query previous).checks = 1
  rw [Graph.executeFocusedBoundariedAtomRegistrationCounted_checks]
  rfl

theorem node11Counted_work_bounded (previous : Node10Stage.{u}) :
    (node11Counted previous).checks ≤
      Node10Focus.selectionBudget.coefficient *
        (Node10Focus.selectionBudget.size previous + 1) ^
          Node10Focus.selectionBudget.degree :=
  Graph.executeFocusedBoundariedAtomRegistrationCounted_checks_bounded
    Node10Focus node4ContextAtNode10Query previous

/-- Node 11 performs one structural focus selection; deriving the atom family
and profiles adds no finite inspection. -/
theorem node11_checks_eq_one (stage : Node11Stage.{u})
    (active : Node11Focus.Active stage) :
    (node11CertificateQuery.read stage active).checks = 1 := by
  exact (node11CertificateQuery.read stage active).checks_eq_budget.trans rfl

/-- The registered work count satisfies Graph's uniform polynomial budget. -/
theorem node11_work_bounded (stage : Node11Stage.{u})
    (active : Node11Focus.Active stage) :
    (node11CertificateQuery.read stage active).checks ≤
      Node10Focus.selectionBudget.coefficient *
        (Node10Focus.selectionBudget.size stage.previous + 1) ^
          Node10Focus.selectionBudget.degree :=
  (node11CertificateQuery.read stage active).work_bounded

#print axioms node11
#print axioms node11_boundaryDegreeProfile
#print axioms node11_profileMismatchRejected
#print axioms node11Counted_checks_eq_one
#print axioms node11Counted_work_bounded
#print axioms node11_checks_eq_one
#print axioms node11_work_bounded

end HypostructureErdos64EG
