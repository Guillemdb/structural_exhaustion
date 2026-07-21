import Hypostructure.CT5.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query

/-!
# CT5 executable capability

The dependent local family is one typed query into the exact predecessor.
Applications provide primitive decisions only; they do not provide a deficit,
ledger, terminal, or route.
-/

namespace Hypostructure.CT5

universe uPrevious uSite uWitness uResource

/-- Worst-case primitive inspections for the prescribed CT5 flow.

The executor performs one support prepass over the residual-owned witness
fibres, one deficit pass over the sites, one ledger pass when the deficit scan
is clear, and at most two resource comparisons. -/
def localCheckBound {Site : Type uSite} {Witness : Site -> Type uWitness}
    (family : Core.Finite.DependentEnumeration Site Witness) : Nat :=
  family.flatten.card + 2 * family.indices.card + 2

/-- Minimal executable CT5 surface. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous) where
  family : Core.Residual.Query Previous fun previous =>
    Core.Finite.DependentEnumeration (spec.Site previous)
      (spec.Witness previous)
  activeDecidable : (previous : Previous) -> (site : spec.Site previous) ->
    Decidable (spec.Active previous site)
  supportsDecidable : (previous : Previous) ->
    (site : spec.Site previous) ->
    (witness : spec.Witness previous site) ->
      Decidable (spec.Supports previous site witness)
  resourceLEDecidable : (left right : spec.budget.Resource) ->
    Decidable (left <= right)

namespace Capability

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uSite, uWitness, uResource} Previous}

/-- Exact dependent schedule retrieved from the predecessor ledger. -/
def familyAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.DependentEnumeration (spec.Site previous)
      (spec.Witness previous) :=
  capability.family.read previous

/-- Exact ordered site schedule. -/
def sitesAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Site previous) :=
  (capability.familyAt previous).indices

/-- Exact witness fibre at one residual-owned site. -/
def witnessesAt (capability : Capability spec) (previous : Previous)
    (site : spec.Site previous) :
    Core.Finite.Enumeration (spec.Witness previous site) :=
  (capability.familyAt previous).fibres site

/-- Total cardinality of the exact dependent witness family. -/
def witnessCount (capability : Capability spec) (previous : Previous) : Nat :=
  (capability.familyAt previous).flatten.card

/-- Natural input size visible to the verifier-work budget. -/
def inputSize (capability : Capability spec) (previous : Previous) : Nat :=
  capability.witnessCount previous + (capability.sitesAt previous).card

/-- Framework-owned linear envelope for the complete CT5 schedule. -/
def linearWorkBudget (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := fun previous => localCheckBound (capability.familyAt previous)
  coefficient := 2
  degree := 1
  bounded := by
    intro previous
    simp only [localCheckBound, inputSize, witnessCount, sitesAt, familyAt,
      Nat.pow_one]
    omega

end Capability

end Hypostructure.CT5
