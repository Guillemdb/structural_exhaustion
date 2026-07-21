import Hypostructure.CT8.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query

/-!
# CT8 residual-owned executable capability

The ordered state list and both finite universes are queried from the literal
predecessor.  CT8 derives its bounded ordered-pair schedule from that exact
list.  No ambient family or detached application sequence is accepted by the
executor.
-/

namespace Hypostructure.CT8

universe uPrevious uState uType uContext uValue uRemoval

/-- Two bounded positions in strict left-to-right order. -/
abbrev OrderedIndexPair (length : Nat) :=
  {pair : Fin length × Fin length // pair.1 < pair.2}

/-- The canonical lexicographic schedule of all strict ordered index pairs. -/
def orderedPairSchedule (length : Nat) :
    Core.Finite.CompleteEnumeration (OrderedIndexPair length) :=
  let indices : Core.Finite.CompleteEnumeration (Fin length) :=
    Core.Finite.CompleteEnumeration.ofFinEnum inferInstance
  (indices.product indices).subtype (fun pair => pair.1 < pair.2)
    (fun _pair => inferInstance)

/-- The derived strict-pair family is quadratically bounded by the incoming
sequence length. -/
theorem orderedPairSchedule_card_le_square (length : Nat) :
    (orderedPairSchedule length).toEnumeration.card <= length * length := by
  let schedule := orderedPairSchedule length
  have all : schedule.toEnumeration.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro pair
    rw [Core.Finite.Enumeration.mem_toFinset]
    exact schedule.complete pair
  calc
    schedule.toEnumeration.card = schedule.toEnumeration.toFinset.card :=
      (Core.Finite.Enumeration.card_toFinset schedule.toEnumeration).symm
    _ = Fintype.card (OrderedIndexPair length) := by rw [all]; simp
    _ <= Fintype.card (Fin length × Fin length) :=
      Fintype.card_subtype_le _
    _ = length * length := by simp

/-- Worst-case primitive comparisons: every ordered pair, then every response
context for the selected repeated pair. -/
def localCheckBound {State : Type uState} {Context : Type uContext}
    (sequence : List State) (contexts : Core.Finite.Enumeration Context) : Nat :=
  (orderedPairSchedule sequence.length).toEnumeration.card + contexts.card

/-- The complete CT8 comparison schedule is quadratic in sequence length and
linear in the number of supplied response contexts. -/
theorem localCheckBound_le_square {State : Type uState}
    {Context : Type uContext} (sequence : List State)
    (contexts : Core.Finite.Enumeration Context) :
    localCheckBound sequence contexts <=
      sequence.length * sequence.length + contexts.card :=
  Nat.add_le_add_right
    (orderedPairSchedule_card_le_square sequence.length) contexts.card

/-- Minimum executable input for CT8.

`remove` is invoked only after CT8 has selected a repeated pair and proved
equality of all responses.  `removeStrict` certifies the exact value returned
by that operation; callers never provide a selected pair or output payload.
-/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uState, uType, uContext, uValue, uRemoval}
      Previous) where
  sequence : Core.Residual.Query Previous fun previous =>
    List (spec.State previous)
  exactTypes : Core.Residual.Query Previous fun previous =>
    Core.Finite.CompleteEnumeration (spec.ExactType previous)
  responseContexts : Core.Residual.Query Previous fun previous =>
    Core.Finite.CompleteEnumeration (spec.ResponseContext previous)
  responseValueDecEq : (previous : Previous) ->
    DecidableEq (spec.ResponseValue previous)
  remove : (previous : Previous) ->
    (first second : spec.State previous) ->
    (sameType : spec.exactType previous first =
      spec.exactType previous second) ->
    (equalResponses : forall context,
      spec.response previous first context =
        spec.response previous second context) ->
      spec.Removal previous
  removeStrict : (previous : Previous) ->
    (first second : spec.State previous) ->
    (sameType : spec.exactType previous first =
      spec.exactType previous second) ->
    (equalResponses : forall context,
      spec.response previous first context =
        spec.response previous second context) ->
      spec.StrictlySmaller previous
        (remove previous first second sameType equalResponses)
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    localCheckBound (sequence.read previous)
        (responseContexts.read previous).toEnumeration <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

namespace Capability

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uState, uType, uContext, uValue, uRemoval}
    Previous}

/-- Literal ordered state sequence retrieved from the predecessor. -/
def sequenceAt (capability : Capability spec) (previous : Previous) :
    List (spec.State previous) :=
  capability.sequence.read previous

/-- Exact finite type universe retrieved from the predecessor. -/
def exactTypesAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.CompleteEnumeration (spec.ExactType previous) :=
  capability.exactTypes.read previous

/-- Exact complete response-context schedule retrieved from the predecessor. -/
def responseContextsAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.CompleteEnumeration (spec.ResponseContext previous) :=
  capability.responseContexts.read previous

/-- Canonical framework-derived pair schedule for the exact incoming list. -/
def orderedPairsAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.CompleteEnumeration
      (OrderedIndexPair (capability.sequenceAt previous).length) :=
  orderedPairSchedule (capability.sequenceAt previous).length

/-- State at one bounded occurrence of the exact incoming list. -/
def stateAt (capability : Capability spec) (previous : Previous)
    (index : Fin (capability.sequenceAt previous).length) :
    spec.State previous :=
  (capability.sequenceAt previous).get index

/-- Decidable exact-type equality comes from the predecessor-owned complete
type schedule. -/
def exactTypeDecEq (capability : Capability spec) (previous : Previous) :
    DecidableEq (spec.ExactType previous) :=
  (capability.exactTypesAt previous).toEnumeration.decEq

/-- Framework-visible polynomial envelope for both CT8 scans. -/
def polynomialBudget (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := fun previous =>
    localCheckBound (capability.sequenceAt previous)
      (capability.responseContextsAt previous).toEnumeration
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := capability.workBound

end Capability

end Hypostructure.CT8
