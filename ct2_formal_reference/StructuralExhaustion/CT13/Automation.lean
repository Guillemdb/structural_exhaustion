import StructuralExhaustion.CT13.Theorems
namespace StructuralExhaustion.CT13
syntax (name := ct13Execute) "ct13_execute " term " using " term " with " term " via " term : term
macro_rules
  | `(ct13_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT13.runTraced _ $input $plan $port $handoff)
syntax (name := ct13Tactic) "ct13 " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct13 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT13.run_verified _ $input $plan $port $handoff)
syntax (name := ct13TotalTactic) "ct13_total " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct13_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT13.run_total _ $input $plan $port $handoff)
end StructuralExhaustion.CT13
