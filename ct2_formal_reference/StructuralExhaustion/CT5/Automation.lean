import StructuralExhaustion.CT5.Theorems

namespace StructuralExhaustion.CT5

syntax (name := ct5Execute)
  "ct5_execute " term " using " term " with " term " via " term : term

macro_rules
  | `(ct5_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT5.runTraced _ $input $plan $port $handoff)

syntax (name := ct5Tactic)
  "ct5 " term " using " term " with " term " via " term : tactic

macro_rules
  | `(tactic| ct5 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT5.run_verified
        _ $input $plan $port $handoff)

syntax (name := ct5TotalTactic)
  "ct5_total " term " using " term " with " term " via " term : tactic

macro_rules
  | `(tactic| ct5_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT5.run_total
        _ $input $plan $port $handoff)

end StructuralExhaustion.CT5
