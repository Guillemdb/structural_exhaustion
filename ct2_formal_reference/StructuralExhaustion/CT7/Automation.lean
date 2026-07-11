import StructuralExhaustion.CT7.Theorems
namespace StructuralExhaustion.CT7
syntax (name := ct7Execute)
  "ct7_execute " term " using " term " with " term " via " term : term
macro_rules
  | `(ct7_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT7.runTraced _ $input $plan $port $handoff)
syntax (name := ct7Tactic)
  "ct7 " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct7 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT7.run_verified _ $input $plan $port $handoff)
syntax (name := ct7TotalTactic)
  "ct7_total " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct7_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT7.run_total _ $input $plan $port $handoff)
end StructuralExhaustion.CT7
