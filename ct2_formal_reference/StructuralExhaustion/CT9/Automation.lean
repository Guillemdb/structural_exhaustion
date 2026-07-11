import StructuralExhaustion.CT9.Theorems
namespace StructuralExhaustion.CT9
syntax (name := ct9Execute)
  "ct9_execute " term " using " term " with " term " via " term : term
macro_rules
  | `(ct9_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT9.runTraced _ $input $plan $port $handoff)
syntax (name := ct9Tactic)
  "ct9 " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct9 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT9.run_verified _ $input $plan $port $handoff)
syntax (name := ct9TotalTactic)
  "ct9_total " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct9_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT9.run_total _ $input $plan $port $handoff)
end StructuralExhaustion.CT9
