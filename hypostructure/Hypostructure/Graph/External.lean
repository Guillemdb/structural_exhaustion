import Hypostructure.Core.Provision

/-!
# Graph external theorem boundary

Graph theorem imports that remain black boxes are registered here as exact
local contracts.  The contract stores the source declaration and the
graph-local hypotheses/conclusion pair, but it does not invent a route, node
output, or application theorem.
-/

namespace Hypostructure.Graph.External

universe u

/-- One named graph theorem that is imported as a local black box. -/
structure LocalTheorem where
  source : Core.DeclarationRef
  hypotheses : Prop
  conclusion : Prop
  proof : hypotheses -> conclusion

namespace LocalTheorem

/-- Use the registered theorem contract on its exact local hypotheses. -/
def apply (contract : LocalTheorem) (h : contract.hypotheses) :
    contract.conclusion :=
  contract.proof h

end LocalTheorem

/-- A reviewed exact-name allowlist.  The list is intentionally explicit; the
framework does not infer or scrape it from source text. -/
structure Allowlist where
  sources : List Core.DeclarationRef

namespace Allowlist

def contains (allowlist : Allowlist) (source : Core.DeclarationRef) : Prop :=
  source ∈ allowlist.sources

theorem mem_of_list {allowlist : Allowlist} {source : Core.DeclarationRef}
    (h : source ∈ allowlist.sources) : allowlist.contains source :=
  h

end Allowlist

end Hypostructure.Graph.External
