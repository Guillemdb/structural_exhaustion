import Hypostructure.Core.Closure
import HypostructureErdos64EG.Node6

/-!
# Diagram node 7: power-of-two-cycle terminal

Node 7 is exactly CT1's C1 terminal from node 6. It exposes the generated
power-of-two-cycle target as a direct Core closure and emits no successor.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- CT1's C1 constructor yields the exact public cycle target. -/
theorem node7_powerOfTwoCycle (stage : Node6Stage.{u})
    (active : Node6Focus.Active stage)
    (isC1 : (node6RouteQuery.read stage active).terminal = .c1) :
    Target (node6ObjectQuery.read stage.previous active) :=
  CT1.FocusedCertificateEncoding.target_of_c1
    (node6RouteQuery.read stage active) isC1

/-- Node 7 closes directly with CT1's generated target certificate. -/
def node7 (stage : Node6Stage.{u})
    (active : Node6Focus.Active stage)
    (isC1 : (node6RouteQuery.read stage active).terminal = .c1) :
    Core.Closure.Result
      (Target (node6ObjectQuery.read stage.previous active)) :=
  Core.Closure.Result.direct
    (.certificate (node7_powerOfTwoCycle stage active isC1))

/-- Node 7 uses Core's direct-certificate closure mechanism. -/
theorem node7_closure_mechanism (stage : Node6Stage.{u})
    (active : Node6Focus.Active stage)
    (isC1 : (node6RouteQuery.read stage active).terminal = .c1) :
    (node7 stage active isC1).mechanism = Core.Closure.Mechanism.direct :=
  rfl

/-- Node 6's C1 route performed exactly one certificate validation. -/
theorem node7_route_checks_eq_one (stage : Node6Stage.{u})
    (active : Node6Focus.Active stage)
    (isC1 : (node6RouteQuery.read stage active).terminal = .c1) :
    (node6RouteQuery.read stage active).checks = 1 := by
  rw [(node6RouteQuery.read stage active).checks_eq_terminal, isC1]

#print axioms node7
#print axioms node7_powerOfTwoCycle
#print axioms node7_closure_mechanism
#print axioms node7_route_checks_eq_one

end HypostructureErdos64EG
