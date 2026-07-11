import StructuralExhaustion.CT6.Theorems

namespace StructuralExhaustion.CT6

syntax (name := ct6Execute)
  "ct6_execute " term " using " term " with " term " via " term : term

macro_rules
  | `(ct6_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT6.runTraced _ $input $plan $port $handoff)

syntax (name := ct6Tactic)
  "ct6 " term " using " term " with " term " via " term : tactic

macro_rules
  | `(tactic| ct6 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT6.run_verified
        _ $input $plan $port $handoff)

syntax (name := ct6TotalTactic)
  "ct6_total " term " using " term " with " term " via " term : tactic

macro_rules
  | `(tactic| ct6_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT6.run_total
        _ $input $plan $port $handoff)

end StructuralExhaustion.CT6
