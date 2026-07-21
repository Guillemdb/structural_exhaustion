import Hypostructure.CT12.Theorems
import Hypostructure.Core.Finite.Enumeration

/-!
# CT12 predecessor-owned list peeling

This profile derives the indexed state, head/tail peel, decreasing
restoration, work budget, and execution from one residual-owned finite
schedule.  It never enumerates the ambient value type.
-/

namespace Hypostructure.CT12.ListPeeling

universe uPrevious uValue

/-- Minimal profile: only the dependent value type and the exact predecessor
schedule are supplied. -/
structure Profile (Previous : Type uPrevious) where
  Value : Previous -> Type uValue
  schedule : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (Value previous)

/-- A list whose remaining length is carried in its state index. -/
structure State {Previous : Type uPrevious} (profile : Profile Previous)
    (previous : Previous) (load : Nat) where
  values : List (profile.Value previous)
  length_eq : values.length = load

/-- Exact head/tail decomposition of one positive-load state. -/
structure Peeled {Previous : Type uPrevious} (profile : Profile Previous)
    (previous : Previous) {load : Nat}
    (state : State profile previous (load + 1)) where
  head : profile.Value previous
  tail : State profile previous load
  exact : state.values = head :: tail.values

/-- Every positive indexed list has a canonical head and tail. -/
def peel {Previous : Type uPrevious} {profile : Profile Previous}
    {previous : Previous} {load : Nat}
    (state : State profile previous (load + 1)) :
    Peeled profile previous state := by
  cases valuesEquation : state.values with
  | nil =>
      have impossible := state.length_eq
      simp [valuesEquation] at impossible
  | cons head tail =>
      have tailLength : tail.length = load := by
        simpa [valuesEquation] using state.length_eq
      exact {
        head := head
        tail := ⟨tail, tailLength⟩
        exact := valuesEquation
      }

/-- Domain-neutral CT12 specification that always continues to the exact tail. -/
def spec {Previous : Type uPrevious} (profile : Profile Previous) :
    CT12.Spec Previous where
  State := fun previous load => State profile previous load
  Peeled := fun {previous} {_load} state => Peeled profile previous state
  DemandResidual := fun _previous => Empty
  TierResidual := fun _previous => Empty
  peel := fun state => peel state
  restorations := fun {_previous} {load} {_state} peeled => {
    first := .continue load peeled.tail (Nat.lt_succ_self load)
  }

/-- Exact initial state derived from the predecessor-owned schedule. -/
def initialState {Previous : Type uPrevious} (profile : Profile Previous)
    (previous : Previous) : CT12.InitialState (spec profile) previous :=
  let schedule := profile.schedule.read previous
  {
    load := schedule.card
    state := ⟨schedule.values, rfl⟩
  }

/-- Complete executable list-peeling capability.  Its linear budget is
framework-derived from the exact schedule length. -/
def capability {Previous : Type uPrevious} (profile : Profile Previous) :
    CT12.Capability (spec profile) where
  initial := profile.schedule.map fun previous _schedule =>
    initialState profile previous
  inputSize := fun previous => (profile.schedule.read previous).card
  workCoefficient := 5
  workDegree := 1
  workBound := by
    intro previous
    change 4 * (profile.schedule.read previous).card + 1 <=
      5 * ((profile.schedule.read previous).card + 1) ^ 1
    simp only [pow_one]
    omega

/-- Execute canonical list peeling on the exact predecessor ledger. -/
def run {Previous : Type uPrevious} (profile : Profile Previous)
    (previous : Previous) :
    CT12.ExecutionResult (spec profile) (capability profile) :=
  CT12.run (spec profile) (capability profile) previous

/-- Exact loop trace for an exhausted head/tail peeling schedule. -/
def expectedLoopTrace : Nat -> List CT12.NodeId
  | 0 => [.saturation, .exhaustedTerminal]
  | load + 1 =>
      [.saturation, .peel, .restoration, .decrease] ++
        expectedLoopTrace load

/-- Exact public trace, including entry. -/
def expectedTrace (load : Nat) : List CT12.NodeId :=
  .entry :: expectedLoopTrace load

private theorem runLoop_terminal_exhausted
    {Previous : Type uPrevious} (profile : Profile Previous)
    (previous : Previous) (load : Nat)
    (state : State profile previous load) :
    (CT12.runLoop (spec profile) previous load state).terminal =
      .exhausted := by
  induction load using Nat.strong_induction_on with
  | h load induction =>
      cases load with
      | zero =>
          rw [CT12.runLoop]
      | succ remaining =>
          rw [CT12.runLoop]
          simp only [CT12.inspect, spec, RestorationOptions.selected]
          change
            (CT12.runLoop (spec profile) previous remaining
              (peel state).tail).terminal = .exhausted
          exact induction remaining (Nat.lt_succ_self remaining)
            (peel state).tail

/-- Canonical list peeling has no demand or tier terminal. -/
theorem run_terminal_exhausted
    {Previous : Type uPrevious} (profile : Profile Previous)
    (previous : Previous) :
    (run profile previous).terminal = .exhausted := by
  exact runLoop_terminal_exhausted profile previous
    (profile.schedule.read previous).card
    (initialState profile previous).state

private theorem runLoop_iterations_eq_load
    {Previous : Type uPrevious} (profile : Profile Previous)
    (previous : Previous) (load : Nat)
    (state : State profile previous load) :
    (CT12.runLoop (spec profile) previous load state).trace.iterations =
      load := by
  induction load using Nat.strong_induction_on with
  | h load induction =>
      cases load with
      | zero =>
          rw [CT12.runLoop]
          rfl
      | succ remaining =>
          rw [CT12.runLoop]
          simp only [CT12.inspect, spec, RestorationOptions.selected]
          change
            (CT12.runLoop (spec profile) previous remaining
              (peel state).tail).trace.iterations + 1 = remaining + 1
          rw [induction remaining (Nat.lt_succ_self remaining)
            (peel state).tail]

/-- Canonical list peeling performs exactly one iteration per scheduled value. -/
theorem run_iterations_eq_card
    {Previous : Type uPrevious} (profile : Profile Previous)
    (previous : Previous) :
    (run profile previous).iterations =
      (profile.schedule.read previous).card := by
  exact runLoop_iterations_eq_load profile previous
    (profile.schedule.read previous).card
    (initialState profile previous).state

private theorem runLoop_trace_eq_expected
    {Previous : Type uPrevious} (profile : Profile Previous)
    (previous : Previous) (load : Nat)
    (state : State profile previous load) :
    (CT12.runLoop (spec profile) previous load state).trace.nodes =
      expectedLoopTrace load := by
  induction load using Nat.strong_induction_on with
  | h load induction =>
      cases load with
      | zero =>
          rw [CT12.runLoop]
          rfl
      | succ remaining =>
          rw [CT12.runLoop]
          simp only [CT12.inspect, spec, RestorationOptions.selected]
          change [.saturation, .peel, .restoration, .decrease] ++
              (CT12.runLoop (spec profile) previous remaining
                (peel state).tail).trace.nodes =
            [.saturation, .peel, .restoration, .decrease] ++
              expectedLoopTrace remaining
          rw [induction remaining (Nat.lt_succ_self remaining)
            (peel state).tail]

/-- Canonical list peeling exposes every loop-back in exact order. -/
theorem run_trace_eq_expected
    {Previous : Type uPrevious} (profile : Profile Previous)
    (previous : Previous) :
    (run profile previous).traceNodes =
      expectedTrace (profile.schedule.read previous).card := by
  change .entry ::
      (CT12.runLoop (spec profile) previous
        (profile.schedule.read previous).card
        (initialState profile previous).state).trace.nodes = _
  rw [runLoop_trace_eq_expected profile previous
    (profile.schedule.read previous).card
    (initialState profile previous).state]
  rfl

/-- Exact work of canonical list peeling. -/
theorem run_checks_eq
    {Previous : Type uPrevious} (profile : Profile Previous)
    (previous : Previous) :
    (run profile previous).checks =
      4 * (profile.schedule.read previous).card + 1 := by
  rw [(run profile previous).checks_eq_exact,
    run_terminal_exhausted profile previous,
    run_iterations_eq_card profile previous]
  rfl

end Hypostructure.CT12.ListPeeling
