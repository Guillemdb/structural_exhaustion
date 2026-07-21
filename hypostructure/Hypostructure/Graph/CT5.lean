import Hypostructure.CT5.Automation
import Hypostructure.Graph.Object

/-!
# Graph adapter for CT5

The adapter only evaluates caller-supplied local-witness semantics against the
packed graph read from the predecessor.  It creates no sites, witnesses,
ledger entries, route, or terminal.
-/

namespace Hypostructure.Graph.CT5

universe uPrevious uVertex uSite uWitness uResource

/-- Translate graph-indexed local semantics into the shared CT5 contract. -/
def localWitnessSpec {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (budget : Core.ResourceBudget.{uResource})
    (Site : Previous -> Type uSite)
    (Witness : (previous : Previous) -> Site previous -> Type uWitness)
    (Active : (previous : Previous) -> FiniteObject.{uVertex} ->
      Site previous -> Prop)
    (Supports : (previous : Previous) -> FiniteObject.{uVertex} ->
      (site : Site previous) -> Witness previous site -> Prop)
    (contribution : (previous : Previous) -> FiniteObject.{uVertex} ->
      (site : Site previous) -> Witness previous site -> budget.Resource)
    (required capacity : (previous : Previous) -> FiniteObject.{uVertex} ->
      budget.Resource) :
    _root_.Hypostructure.CT5.Spec Previous where
  budget := budget
  Site := Site
  Witness := Witness
  Active := fun previous site =>
    Active previous (object.read previous) site
  Supports := fun previous site witness =>
    Supports previous (object.read previous) site witness
  contribution := fun previous site witness =>
    contribution previous (object.read previous) site witness
  required := fun previous => required previous (object.read previous)
  capacity := fun previous => capacity previous (object.read previous)

/-- Build the shared capability from the exact predecessor-owned dependent
family and primitive graph-semantic decisions. -/
def localWitnessCapability {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (budget : Core.ResourceBudget.{uResource})
    (Site : Previous -> Type uSite)
    (Witness : (previous : Previous) -> Site previous -> Type uWitness)
    (Active : (previous : Previous) -> FiniteObject.{uVertex} ->
      Site previous -> Prop)
    (Supports : (previous : Previous) -> FiniteObject.{uVertex} ->
      (site : Site previous) -> Witness previous site -> Prop)
    (contribution : (previous : Previous) -> FiniteObject.{uVertex} ->
      (site : Site previous) -> Witness previous site -> budget.Resource)
    (required capacity : (previous : Previous) -> FiniteObject.{uVertex} ->
      budget.Resource)
    (family : Core.Residual.Query Previous fun previous =>
      Core.Finite.DependentEnumeration (Site previous) (Witness previous))
    (activeDecidable : (previous : Previous) ->
      (object : FiniteObject.{uVertex}) -> (site : Site previous) ->
        Decidable (Active previous object site))
    (supportsDecidable : (previous : Previous) ->
      (object : FiniteObject.{uVertex}) -> (site : Site previous) ->
      (witness : Witness previous site) ->
        Decidable (Supports previous object site witness))
    (resourceLEDecidable : (left right : budget.Resource) ->
      Decidable (left <= right)) :
    _root_.Hypostructure.CT5.Capability
      (localWitnessSpec object budget Site Witness Active Supports contribution
        required capacity) where
  family := family
  activeDecidable := fun previous site =>
    activeDecidable previous (object.read previous) site
  supportsDecidable := fun previous site witness =>
    supportsDecidable previous (object.read previous) site witness
  resourceLEDecidable := resourceLEDecidable

end Hypostructure.Graph.CT5
