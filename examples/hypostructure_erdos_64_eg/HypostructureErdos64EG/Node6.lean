import Hypostructure.Graph.CT1
import HypostructureErdos64EG.Node5

/-!
# Diagram node 6: exhaustive Mersenne-return decision

Node 6 invokes focused proof-carrying CT1 on node 5's literal stage. CT1 owns
the target decision, certificate validation, routing, trace, and work count.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Current selected graph, retrieved only on the active branch. -/
def node6ObjectQuery :
    Core.Residual.Focus.ActiveQuery Node5Focus
      (fun _stage _active => Graph.FiniteObject.{u}) :=
  node4ContextAtNode5Query.map fun _stage _active minimal => minimal.G

/-- The entire node-6 specialization: one graph query and the node-5 algebra. -/
def node6Encoding :=
  Graph.CT1.focusedRootedReturnEncoding Node5Focus node6ObjectQuery
    PowerOfTwoLength mersenneReturnAlgebra

/-- Exact accumulated CT1 decision stage emitted by node 6. -/
abbrev Node6Stage :=
  CT1.FocusedCertificateEncoding.Stage node6Encoding

/-- Counted node-6 execution through the public focused graph CT1 executor. -/
noncomputable def node6Counted (previous : Node5Stage.{u}) :
    Core.Counted Node6Stage.{u} :=
  Graph.CT1.executeFocusedRootedReturnCounted Node5Focus node6ObjectQuery
    PowerOfTwoLength mersenneReturnAlgebra previous

/-- Execute node 6 through the public focused graph CT1 executor. -/
noncomputable def node6 (previous : Node5Stage.{u}) : Node6Stage.{u} :=
  (node6Counted previous).value

/-- Focus inherited after node 6's CT1 extension. -/
abbrev Node6Focus := node6Encoding.SuccessorProfile

/-- Typed query for the framework-generated CT1 route. -/
def node6RouteQuery := node6Encoding.routeQuery

/-- Minimal context lifted through node 6 without copying it. -/
def node4ContextAtNode6Query :
    Core.Residual.Focus.ActiveQuery Node6Focus
      (fun stage active =>
        Node4Output stage.previous.previous.previous active) :=
  node4ContextAtNode5Query.preserve

/-- Node 5's exact return-avoidance certificate retained through node 6. -/
def node5CertificateAtNode6Query :
    Core.Residual.Focus.ActiveQuery Node6Focus
      (fun stage active =>
        Node5Output stage.previous.previous active) :=
  node5CertificateQuery.preserve

/-- The inherited node-5 certificate rules out CT1's public target. -/
def node6TargetImpossibleQuery :
    Core.Residual.Focus.ActiveQuery Node6Focus
      (fun stage active =>
        Not (Target (node6ObjectQuery.read stage.previous active))) :=
  node5CertificateAtNode6Query.map fun _stage _active certificate => by
    simpa [Node5Output, Target, node6ObjectQuery, node4ContextAtNode5Query] using
      certificate.notTarget

/-- Framework-owned residual on node 6's exact avoiding arm. -/
abbrev Node6AvoidingStage := node6Encoding.AvoidingStage

/-- Counted closure of the impossible C1 constructor. -/
noncomputable def node6ContinueAvoidingCounted
    (previous : Node6Stage.{u}) : Core.Counted Node6AvoidingStage.{u} :=
  node6Encoding.closeC1ContinueAvoidingCounted
    previous node6TargetImpossibleQuery

/-- Close the impossible C1 constructor and retain node 6's avoiding residual. -/
noncomputable def node6ContinueAvoiding
    (previous : Node6Stage.{u}) : Node6AvoidingStage.{u} :=
  (node6ContinueAvoidingCounted previous).value

/-- Focus inherited by node 8 from node 6's avoiding residual. -/
abbrev Node6AvoidingFocus :=
  Core.Residual.Focus.successor Node6Focus
    (CT1.FocusedCertificateEncoding.AvoidingEvidence node6Encoding)

/-- Exact avoiding evidence retained by CT1 on the node-6 edge. -/
def node6AvoidingQuery :
    Core.Residual.Focus.ActiveQuery Node6AvoidingFocus
      (fun stage active =>
        CT1.FocusedCertificateEncoding.AvoidingEvidence
          node6Encoding stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

@[simp] theorem node6_previous (previous : Node5Stage.{u}) :
    (node6 previous).previous = previous :=
  rfl

/-- CT1's terminal has exactly its local target/avoidance meaning. -/
theorem node6_semantics (stage : Node6Stage.{u})
    (active : Node6Focus.Active stage) :
    match (node6RouteQuery.read stage active).terminal with
    | .c1 => Target (node6ObjectQuery.read stage.previous active)
    | .avoiding => Not (Target (node6ObjectQuery.read stage.previous active)) := by
  let route := node6RouteQuery.read stage active
  cases terminal : route.terminal with
  | c1 =>
      exact CT1.FocusedCertificateEncoding.target_of_c1 route terminal
  | avoiding =>
      exact CT1.FocusedCertificateEncoding.avoids_of_avoiding route terminal

/-- Node 6 retains CT1's exact terminal-indexed trace. -/
theorem node6_trace_exact (stage : Node6Stage.{u})
    (active : Node6Focus.Active stage) :
    (CT1.CertificateEncoding.traceOfRoute
      (node6RouteQuery.read stage active)).nodes =
      CT1.CertificateEncoding.TypedTrace.expectedNodes
        (node6RouteQuery.read stage active).terminal :=
  (CT1.CertificateEncoding.traceOfRoute
    (node6RouteQuery.read stage active)).nodes_eq_expected

/-- Focused certificate CT1 performs at most one primitive validation. -/
theorem node6_work_bound (stage : Node6Stage.{u})
    (active : Node6Focus.Active stage) :
    (node6RouteQuery.read stage active).checks <= 1 := by
  rw [(node6RouteQuery.read stage active).checks_eq_terminal]
  cases (node6RouteQuery.read stage active).terminal <;> simp

/-- Total node-6 work includes focus selection and CT1 validation. -/
theorem node6Counted_work_bounded (previous : Node5Stage.{u}) :
    (node6Counted previous).checks <=
      node6Encoding.workBudget.coefficient *
        (node6Encoding.workBudget.size previous + 1) ^
          node6Encoding.workBudget.degree :=
  node6Encoding.runCounted_checks_bounded previous

/-- The avoidance continuation also accounts for its focus selection. -/
theorem node6ContinueAvoidingCounted_work_bounded
    (previous : Node6Stage.{u}) :
    (node6ContinueAvoidingCounted previous).checks <=
      node6Encoding.SuccessorProfile.selectionBudget.coefficient *
        (node6Encoding.SuccessorProfile.selectionBudget.size previous + 1) ^
          node6Encoding.SuccessorProfile.selectionBudget.degree :=
  node6Encoding.closeC1ContinueAvoidingCounted_checks_bounded
    previous node6TargetImpossibleQuery

@[simp] theorem node6ContinueAvoiding_previous (previous : Node6Stage.{u}) :
    (node6ContinueAvoiding previous).previous = previous :=
  rfl

/-- Node 6's continuation arm exactly avoids the public target. -/
theorem node6_avoids (stage : Node6AvoidingStage.{u})
    (active : Node6AvoidingFocus.Active stage) :
    Not (Target (node6ObjectQuery.read stage.previous.previous active)) :=
  (node6AvoidingQuery.read stage active).avoids

/-- The avoiding arm performs no certificate validation. -/
theorem node6_avoiding_work (stage : Node6AvoidingStage.{u})
    (active : Node6AvoidingFocus.Active stage) :
    (node6RouteQuery.read stage.previous active).checks = 0 :=
  (node6AvoidingQuery.read stage active).checks_eq_zero

#print axioms node6
#print axioms node6Counted_work_bounded
#print axioms node6ContinueAvoiding
#print axioms node6ContinueAvoidingCounted_work_bounded
#print axioms node6_semantics
#print axioms node6_trace_exact
#print axioms node6_work_bound
#print axioms node6_avoids
#print axioms node6_avoiding_work

end HypostructureErdos64EG
