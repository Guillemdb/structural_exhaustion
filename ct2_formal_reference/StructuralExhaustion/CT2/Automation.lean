import StructuralExhaustion.CT2.Theorems

namespace StructuralExhaustion.CT2

/-- Term syntax for a traced CT2 run.  The argument order keeps the core
decision plan visibly separate from the consumer port and handoff proof. -/
syntax (name := ct2Execute)
  "ct2_execute " term " using " term " with " term " via " term : term

macro_rules
  | `(ct2_execute $input:term using $plan:term with $port:term via $handoff:term) =>
      `(StructuralExhaustion.CT2.runTraced
        _ $input $plan $port $handoff)

/-- Goal-closing tactic for the soundness claim of a concrete CT2 run.  It does
not reimplement any mathematics: it applies the kernel-checked aggregate
theorem to the supplied semantic plans. -/
syntax (name := ct2Tactic)
  "ct2 " term " using " term " with " term " via " term : tactic

macro_rules
  | `(tactic| ct2 $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT2.run_verified
        _ $input $plan $port $handoff)

/-- Goal-closing tactic for totality plus trace validity. -/
syntax (name := ct2TotalTactic)
  "ct2_total " term " using " term " with " term " via " term : tactic

macro_rules
  | `(tactic| ct2_total $input:term using $plan:term with $port:term via $handoff:term) =>
      `(tactic| exact StructuralExhaustion.CT2.run_total
        _ $input $plan $port $handoff)

end StructuralExhaustion.CT2
