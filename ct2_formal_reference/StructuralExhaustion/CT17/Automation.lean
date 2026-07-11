import StructuralExhaustion.CT17.Theorems
namespace StructuralExhaustion.CT17
syntax (name := ct17Execute) "ct17_execute " term " using " term " with " term " via " term : term
macro_rules
  | `(ct17_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT17.runTraced _ $input $plan $port $handoff)
syntax (name := ct17Tactic) "ct17 " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct17 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT17.run_verified _ $input $plan $port $handoff)
syntax (name := ct17TotalTactic) "ct17_total " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct17_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT17.run_total _ $input $plan $port $handoff)
end StructuralExhaustion.CT17
