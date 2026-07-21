import Hypostructure.CT5.Automation
import Hypostructure.PDE.Model

/-!
# PDE adapter for CT5

PDE contributes only local support and resource semantics evaluated on a
represented state read from the predecessor.  The common CT5 machine owns the
dependent finite scan, account, comparisons, and routing.
-/

namespace Hypostructure.PDE.CT5

universe uPrevious uModel uSite uWitness uResource

/-- Translate represented PDE local-witness semantics into the shared CT5
contract. -/
def localWitnessSpec {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (budget : Core.ResourceBudget.{uResource})
    (Site : Previous -> Type uSite)
    (Witness : (previous : Previous) -> Site previous -> Type uWitness)
    (Active : (previous : Previous) -> M.problem.Ambient ->
      Site previous -> Prop)
    (Supports : (previous : Previous) -> M.problem.Ambient ->
      (site : Site previous) -> Witness previous site -> Prop)
    (contribution : (previous : Previous) -> M.problem.Ambient ->
      (site : Site previous) -> Witness previous site -> budget.Resource)
    (required capacity : (previous : Previous) -> M.problem.Ambient ->
      budget.Resource) :
    _root_.Hypostructure.CT5.Spec Previous where
  budget := budget
  Site := Site
  Witness := Witness
  Active := fun previous site => Active previous (state.read previous) site
  Supports := fun previous site witness =>
    Supports previous (state.read previous) site witness
  contribution := fun previous site witness =>
    contribution previous (state.read previous) site witness
  required := fun previous => required previous (state.read previous)
  capacity := fun previous => capacity previous (state.read previous)

/-- Build the common CT5 capability from one residual-owned dependent family
and primitive represented-state decisions. -/
def localWitnessCapability {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (budget : Core.ResourceBudget.{uResource})
    (Site : Previous -> Type uSite)
    (Witness : (previous : Previous) -> Site previous -> Type uWitness)
    (Active : (previous : Previous) -> M.problem.Ambient ->
      Site previous -> Prop)
    (Supports : (previous : Previous) -> M.problem.Ambient ->
      (site : Site previous) -> Witness previous site -> Prop)
    (contribution : (previous : Previous) -> M.problem.Ambient ->
      (site : Site previous) -> Witness previous site -> budget.Resource)
    (required capacity : (previous : Previous) -> M.problem.Ambient ->
      budget.Resource)
    (family : Core.Residual.Query Previous fun previous =>
      Core.Finite.DependentEnumeration (Site previous) (Witness previous))
    (activeDecidable : (previous : Previous) ->
      (state : M.problem.Ambient) -> (site : Site previous) ->
        Decidable (Active previous state site))
    (supportsDecidable : (previous : Previous) ->
      (state : M.problem.Ambient) -> (site : Site previous) ->
      (witness : Witness previous site) ->
        Decidable (Supports previous state site witness))
    (resourceLEDecidable : (left right : budget.Resource) ->
      Decidable (left <= right)) :
    _root_.Hypostructure.CT5.Capability
      (localWitnessSpec M state budget Site Witness Active Supports contribution
        required capacity) where
  family := family
  activeDecidable := fun previous site =>
    activeDecidable previous (state.read previous) site
  supportsDecidable := fun previous site witness =>
    supportsDecidable previous (state.read previous) site witness
  resourceLEDecidable := resourceLEDecidable

end Hypostructure.PDE.CT5
