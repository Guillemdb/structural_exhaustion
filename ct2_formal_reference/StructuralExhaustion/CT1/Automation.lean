import StructuralExhaustion.CT1.Theorems

namespace StructuralExhaustion.CT1

syntax (name := ct1Execute)
  "ct1_execute " term " using " term " with " term " via " term : term

macro_rules
  | `(ct1_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT1.runTraced
        _ $input $plan $port $handoff)

syntax (name := ct1Tactic)
  "ct1 " term " using " term " with " term " via " term : tactic

macro_rules
  | `(tactic| ct1 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT1.run_verified
        _ $input $plan $port $handoff)

syntax (name := ct1TotalTactic)
  "ct1_total " term " using " term " with " term " via " term : tactic

macro_rules
  | `(tactic| ct1_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT1.run_total
        _ $input $plan $port $handoff)

end StructuralExhaustion.CT1
