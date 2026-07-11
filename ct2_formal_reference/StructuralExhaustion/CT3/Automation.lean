import StructuralExhaustion.CT3.Theorems

namespace StructuralExhaustion.CT3

syntax (name := ct3Execute)
  "ct3_execute " term " using " term " with " term " via " term : term

macro_rules
  | `(ct3_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT3.runTraced _ $input $plan $port $handoff)

syntax (name := ct3Tactic)
  "ct3 " term " using " term " with " term " via " term : tactic

macro_rules
  | `(tactic| ct3 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT3.run_verified
        _ $input $plan $port $handoff)

syntax (name := ct3TotalTactic)
  "ct3_total " term " using " term " with " term " via " term : tactic

macro_rules
  | `(tactic| ct3_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT3.run_total
        _ $input $plan $port $handoff)

end StructuralExhaustion.CT3
