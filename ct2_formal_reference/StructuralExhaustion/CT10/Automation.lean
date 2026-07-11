import StructuralExhaustion.CT10.Theorems
namespace StructuralExhaustion.CT10
syntax (name := ct10Execute)
  "ct10_execute " term " using " term " with " term " via " term : term
macro_rules
  | `(ct10_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT10.runTraced _ $input $plan $port $handoff)
syntax (name := ct10Tactic)
  "ct10 " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct10 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT10.run_verified _ $input $plan $port $handoff)
syntax (name := ct10TotalTactic)
  "ct10_total " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct10_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT10.run_total _ $input $plan $port $handoff)
end StructuralExhaustion.CT10
