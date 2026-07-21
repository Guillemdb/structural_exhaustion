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

/-- Execute node 6 through the public focused graph CT1 executor. -/
noncomputable def node6 (previous : Node5Stage.{u}) : Node6Stage.{u} :=
  Graph.CT1.executeFocusedRootedReturn Node5Focus node6ObjectQuery
    PowerOfTwoLength mersenneReturnAlgebra previous

/-- Focus inherited after node 6's CT1 extension. -/
abbrev Node6Focus := node6Encoding.SuccessorProfile

/-- Typed query for the framework-generated CT1 route. -/
def node6RouteQuery := node6Encoding.routeQuery

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

#print axioms node6
#print axioms node6_semantics
#print axioms node6_trace_exact
#print axioms node6_work_bound

end HypostructureErdos64EG
