import StructuralExhaustion.CT12.Theorems
namespace StructuralExhaustion.CT12
syntax (name := ct12Execute) "ct12_execute " term " using " term " with " term " via " term : term
macro_rules
  | `(ct12_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT12.runTraced _ $input $plan $port $handoff)
syntax (name := ct12Tactic) "ct12 " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct12 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT12.run_verified _ $input $plan $port $handoff)
syntax (name := ct12TotalTactic) "ct12_total " term " using " term " with " term " via " term : tactic
macro_rules
  | `(tactic| ct12_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT12.run_total _ $input $plan $port $handoff)
end StructuralExhaustion.CT12
