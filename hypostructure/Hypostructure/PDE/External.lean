import Hypostructure.Core.Provision

/-!
# PDE external theorem boundary

Analytic estimates, compactness results, and model-specific regularity facts
enter the PDE framework only through explicit local contracts.  This keeps
the strategy and CT layers executable without silently importing an
unregistered continuum theorem.
-/

namespace Hypostructure.PDE.External

open Hypostructure

structure LocalTheorem where
  source : Core.DeclarationRef
  hypotheses : Prop
  conclusion : Prop
  proof : hypotheses -> conclusion

namespace LocalTheorem

def apply (contract : LocalTheorem) (hypotheses : contract.hypotheses) :
    contract.conclusion :=
  contract.proof hypotheses

end LocalTheorem

structure Allowlist where
  sources : List Core.DeclarationRef

namespace Allowlist

def contains (allowlist : Allowlist) (source : Core.DeclarationRef) : Prop :=
  source ∈ allowlist.sources

theorem mem_of_list {allowlist : Allowlist} {source : Core.DeclarationRef}
    (membership : source ∈ allowlist.sources) :
    allowlist.contains source :=
  membership

end Allowlist

end Hypostructure.PDE.External
