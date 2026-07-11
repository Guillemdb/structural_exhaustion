import StructuralExhaustion.CT14.Theorems
namespace StructuralExhaustion.CT14
syntax (name := ct14Execute) "ct14_execute " term " using " term " with " term " via " term : term
macro_rules
  | `(ct14_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT14.runTraced _ $input $plan $port $handoff)
syntax (name := ct14Tactic) "ct14 " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct14 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT14.run_verified _ $input $plan $port $handoff)
syntax (name := ct14TotalTactic) "ct14_total " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct14_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT14.run_total _ $input $plan $port $handoff)
end StructuralExhaustion.CT14
