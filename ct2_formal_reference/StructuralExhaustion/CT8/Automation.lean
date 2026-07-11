import StructuralExhaustion.CT8.Theorems
namespace StructuralExhaustion.CT8
syntax (name := ct8Execute)
  "ct8_execute " term " using " term " with " term " via " term : term
macro_rules
  | `(ct8_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT8.runTraced _ $input $plan $port $handoff)
syntax (name := ct8Tactic)
  "ct8 " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct8 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT8.run_verified _ $input $plan $port $handoff)
syntax (name := ct8TotalTactic)
  "ct8_total " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct8_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT8.run_total _ $input $plan $port $handoff)
end StructuralExhaustion.CT8
