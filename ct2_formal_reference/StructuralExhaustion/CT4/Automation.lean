import StructuralExhaustion.CT4.Theorems

namespace StructuralExhaustion.CT4

syntax (name := ct4Execute)
  "ct4_execute " term " using " term " with " term " via " term : term

macro_rules
  | `(ct4_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT4.runTraced _ $input $plan $port $handoff)

syntax (name := ct4Tactic)
  "ct4 " term " using " term " with " term " via " term : tactic

macro_rules
  | `(tactic| ct4 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT4.run_verified
        _ $input $plan $port $handoff)

syntax (name := ct4TotalTactic)
  "ct4_total " term " using " term " with " term " via " term : tactic

macro_rules
  | `(tactic| ct4_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT4.run_total
        _ $input $plan $port $handoff)

end StructuralExhaustion.CT4
