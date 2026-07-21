import Hypostructure.CT7.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query
import Hypostructure.Core.Response.FiniteTable

/-!
# CT7 queried capability

Both representatives and the finite context coordinates are typed reads from
the literal predecessor.  Completeness is supplied as semantic coverage of
that exact schedule, never as an ambient context enumeration.
-/

namespace Hypostructure.CT7

universe uPrevious uRepresentative uContext uCoordinate uValue

/-- Worst-case checks: one complete realization pass and, after its failure,
one complete response-comparison pass over the same schedule. -/
def localCheckBound {Coordinate : Type uCoordinate}
    (contexts : Core.Finite.Enumeration Coordinate) : Nat :=
  contexts.card + contexts.card

/-- Minimum executable capability for CT7. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous) where
  representatives : Core.Residual.Query Previous fun _previous =>
    Core.Response.Representatives spec.Representative
  contexts : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration spec.system.Coordinate
  valueDecEq : DecidableEq spec.system.Value
  realizesDecidable : (previous : Previous) ->
    (coordinate : spec.system.Coordinate) ->
      Decidable (spec.Realizes previous
        (representatives.read previous).source
        (spec.system.decode coordinate))
  realizationCoverage : (previous : Previous) ->
    (context : spec.system.Context) ->
      spec.Realizes previous (representatives.read previous).source context ->
        Exists fun index : Fin (contexts.read previous).card =>
          spec.Realizes previous (representatives.read previous).source
            (spec.system.decode ((contexts.read previous).get index))
  responseCoverage : (previous : Previous) ->
    Core.Response.FiniteTable.SymbolicCoverage spec.system
      (representatives.read previous)
      (Core.Response.FiniteTable.ExactSchedule.ofList
        (contexts.read previous).values)

namespace Capability

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
    Previous}

/-- Register a schedule that literally realizes every semantic context.

This constructor derives both realization completeness and symbolic response
coverage.  It is appropriate only when the predecessor's finite coordinates
are complete; otherwise callers provide the two weaker coverage laws directly
through `Capability`. -/
def ofExactContexts
    (representatives : Core.Residual.Query Previous fun _previous =>
      Core.Response.Representatives spec.Representative)
    (contexts : Core.Residual.Query Previous fun _previous =>
      Core.Finite.Enumeration spec.system.Coordinate)
    (valueDecEq : DecidableEq spec.system.Value)
    (realizesDecidable : (previous : Previous) ->
      (coordinate : spec.system.Coordinate) ->
        Decidable (spec.Realizes previous
          (representatives.read previous).source
          (spec.system.decode coordinate)))
    (complete : (previous : Previous) -> (context : spec.system.Context) ->
      Exists fun index : Fin (contexts.read previous).card =>
        context = spec.system.decode ((contexts.read previous).get index)) :
    Capability spec where
  representatives := representatives
  contexts := contexts
  valueDecEq := valueDecEq
  realizesDecidable := realizesDecidable
  realizationCoverage := by
    intro previous context realizes
    obtain ⟨index, equal⟩ := complete previous context
    subst context
    exact ⟨index, realizes⟩
  responseCoverage := by
    intro previous
    refine { locate := ?_ }
    intro context
    obtain ⟨index, equal⟩ := complete previous context
    subst context
    exact ⟨index, rfl, rfl⟩

/-- Exact representative pair retrieved from the predecessor ledger. -/
def representativesAt (capability : Capability spec) (previous : Previous) :
    Core.Response.Representatives spec.Representative :=
  capability.representatives.read previous

/-- Exact ordered context-coordinate schedule retrieved from the predecessor. -/
def contextsAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration spec.system.Coordinate :=
  capability.contexts.read previous

/-- Core response-table view of the exact incoming context schedule. -/
def exactScheduleAt (capability : Capability spec) (previous : Previous) :
    Core.Response.FiniteTable.ExactSchedule spec.system.Coordinate :=
  Core.Response.FiniteTable.ExactSchedule.ofList
    (capability.contextsAt previous).values

/-- Automatically derived linear work envelope for the complete CT7 flow. -/
def linearWorkBudget (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := fun previous => (capability.contextsAt previous).card
  checks := fun previous => localCheckBound (capability.contextsAt previous)
  coefficient := 2
  degree := 1
  bounded := by
    intro previous
    simp only [localCheckBound, Nat.pow_one]
    omega

end Capability

end Hypostructure.CT7
