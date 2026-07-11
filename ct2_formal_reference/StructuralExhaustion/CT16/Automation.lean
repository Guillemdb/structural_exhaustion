import StructuralExhaustion.CT16.Theorems
namespace StructuralExhaustion.CT16
syntax (name := ct16Execute) "ct16_execute " term " using " term " with " term " via " term : term
macro_rules
  | `(ct16_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT16.runTraced _ $input $plan $port $handoff)
syntax (name := ct16Tactic) "ct16 " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct16 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT16.run_verified _ $input $plan $port $handoff)
syntax (name := ct16TotalTactic) "ct16_total " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct16_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT16.run_total _ $input $plan $port $handoff)
end StructuralExhaustion.CT16
