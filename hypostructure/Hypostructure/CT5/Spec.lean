import Hypostructure.Core.Budget.Resource

/-!
# CT5 local-witness aggregation specification

CT5 either exposes the first active site without a supporting witness in the
exact incoming schedule or aggregates the first support at every active site.
The resource can be a graph count, a rational charge, or a PDE budget; only
the ordered additive operations registered in `Core.ResourceBudget` are used.
-/

namespace Hypostructure.CT5

universe uPrevious uSite uWitness uResource

/-- Domain-neutral local-witness semantics over one literal predecessor.

The site and witness carriers may depend on that predecessor.  Consequently,
the CT never needs an ambient finite universe and cannot silently replace the
residual-owned local family by a detached enumeration. -/
structure Spec (Previous : Type uPrevious) where
  budget : Core.ResourceBudget.{uResource}
  Site : Previous -> Type uSite
  Witness : (previous : Previous) -> Site previous -> Type uWitness
  Active : (previous : Previous) -> Site previous -> Prop
  Supports : (previous : Previous) -> (site : Site previous) ->
    Witness previous site -> Prop
  contribution : (previous : Previous) -> (site : Site previous) ->
    Witness previous site -> budget.Resource
  required : Previous -> budget.Resource
  capacity : Previous -> budget.Resource

end Hypostructure.CT5
