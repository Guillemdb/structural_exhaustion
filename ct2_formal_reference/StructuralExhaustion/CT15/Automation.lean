import StructuralExhaustion.CT15.Theorems
namespace StructuralExhaustion.CT15
syntax (name := ct15Execute) "ct15_execute " term " using " term " with " term " via " term : term
macro_rules
  | `(ct15_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT15.runTraced _ $input $plan $port $handoff)
syntax (name := ct15Tactic) "ct15 " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct15 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT15.run_verified _ $input $plan $port $handoff)
syntax (name := ct15TotalTactic) "ct15_total " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct15_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT15.run_total _ $input $plan $port $handoff)
end StructuralExhaustion.CT15
