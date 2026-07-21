import HypostructureErdos64EG.Node6

/-!
# Diagram node 7: power-of-two-cycle terminal

The inherited minimal context makes CT1's C1 target impossible. CT1 closes
that constructor and appends only its exact avoiding evidence; the application
does not inspect or route either terminal.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Minimal context lifted through node 6 without copying it. -/
def node4ContextAtNode6Query :
    Core.Residual.Focus.ActiveQuery Node6Focus
      (fun stage active =>
        Node4Output stage.previous.previous.previous active) :=
  node4ContextAtNode5Query.preserve

/-- The only node-7 mathematical input: inherited target avoidance. -/
def node7TargetImpossibleQuery :
    Core.Residual.Focus.ActiveQuery Node6Focus
      (fun stage active =>
        Not (Target (node6ObjectQuery.read stage.previous active))) :=
  node4ContextAtNode6Query.map fun stage active _minimal => by
    let minimal := node4ContextAtNode6Query.read stage active
    have objectEq :
        node6ObjectQuery.read stage.previous active = minimal.G := by
      simp [node6ObjectQuery, minimal, node4ContextAtNode6Query]
    rw [objectEq]
    exact minimal.avoids

/-- Exact accumulated successor after CT1 closes C1. -/
abbrev Node7Stage := node6Encoding.AvoidingStage

/-- Execute node 7 using CT1's focused closure executor. -/
noncomputable def node7 (previous : Node6Stage.{u}) : Node7Stage.{u} :=
  node6Encoding.closeC1ContinueAvoiding previous node7TargetImpossibleQuery

/-- Focus inherited by node 8. -/
abbrev Node7Focus :=
  Core.Residual.Focus.successor Node6Focus
    (CT1.FocusedCertificateEncoding.AvoidingEvidence node6Encoding)

/-- Exact avoiding evidence retained by the framework. -/
def node7AvoidingQuery :
    Core.Residual.Focus.ActiveQuery Node7Focus
      (fun stage active =>
        CT1.FocusedCertificateEncoding.AvoidingEvidence
          node6Encoding stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

@[simp] theorem node7_previous (previous : Node6Stage.{u}) :
    (node7 previous).previous = previous :=
  rfl

/-- The sole surviving counterexample arm exactly avoids the public target. -/
theorem node7_avoids (stage : Node7Stage.{u})
    (active : Node7Focus.Active stage) :
    Not (Target (node6ObjectQuery.read stage.previous.previous active)) :=
  (node7AvoidingQuery.read stage active).avoids

/-- The surviving CT1 arm performs zero certificate scans. -/
theorem node7_work (stage : Node7Stage.{u})
    (active : Node7Focus.Active stage) :
    (node6RouteQuery.read stage.previous active).checks = 0 :=
  (node7AvoidingQuery.read stage active).checks_eq_zero

#print axioms node7
#print axioms node7_avoids
#print axioms node7_work

end HypostructureErdos64EG
