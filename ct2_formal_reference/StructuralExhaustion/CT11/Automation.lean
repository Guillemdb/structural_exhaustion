import StructuralExhaustion.CT11.Theorems

namespace StructuralExhaustion.CT11
syntax (name := ct11Execute)
  "ct11_execute " term " using " term " with " term " via " term : term
macro_rules
  | `(ct11_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT11.runTraced _ $input $plan $port $handoff)
syntax (name := ct11Tactic)
  "ct11 " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct11 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT11.run_verified _ $input $plan $port $handoff)
syntax (name := ct11TotalTactic)
  "ct11_total " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct11_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT11.run_total _ $input $plan $port $handoff)
end StructuralExhaustion.CT11
