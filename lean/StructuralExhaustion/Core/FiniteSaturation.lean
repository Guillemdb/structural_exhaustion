import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Core.FiniteSearch

namespace StructuralExhaustion.Core.FiniteSaturation

universe u v

/-!
An exact sequential machine for finite saturation.

At every state, a machine exposes a duplicate-free ordered frontier and a
decidable enabling predicate.  The reference semantics always selects the
first enabled frontier element.  An enabled step must strictly decrease the
machine measure.  Consequently `execute` returns a finite, proof-carrying
execution whose last state is certified to have no enabled frontier element.
The certificate concerns the frontier exposed by that terminal state; the API
assumes no monotonicity between frontiers and no persistence of earlier
disabled decisions.

The machine is deliberately independent of any CT.  Problem instances supply
only their state, frontier, enabling predicate, certified transition, and
well-founded measure.
-/

/-- Prepending a fresh value to a duplicate-free list strictly decreases the
number of unused slots in an exact finite enumeration.  This is the standard
ranking argument for saturation machines that accumulate fresh values. -/
theorem remainingSlots_cons_lt {α : Type u}
    (enumeration : FinEnum α) {head : α} {tail : List α}
    (nodup : (head :: tail).Nodup) :
    enumeration.orderedValues.length - (head :: tail).length <
      enumeration.orderedValues.length - tail.length := by
  have bound := Enumeration.length_le_elems_of_nodup enumeration nodup
  simp only [List.length_cons] at bound ⊢
  omega

/-- Static contract of a deterministic finite-saturation machine. -/
structure Machine (State : Type u) (Candidate : Type v) where
  /-- Exact duplicate-free ordered candidates inspected at this state. -/
  frontier : State → OrderedCollection Candidate
  /-- The condition under which a frontier candidate may be applied. -/
  Enabled : State → Candidate → Prop
  /-- Executable decision procedure for the enabling condition. -/
  decideEnabled : ∀ state candidate, Decidable (Enabled state candidate)
  /-- The next state produced by a certified enabled frontier candidate. -/
  advance : (state : State) → (candidate : Candidate) →
    candidate ∈ (frontier state).values → Enabled state candidate → State
  /-- Natural-number ranking used only to certify termination. -/
  measure : State → Nat
  /-- Every legal transition strictly decreases the ranking. -/
  advance_decreases : ∀ state candidate member enabled,
    measure (advance state candidate member enabled) < measure state

namespace Machine

variable {State : Type u} {Candidate : Type v}

/-- Ordered one-node decision: the first enabled frontier candidate, or an
exhaustive absence certificate. -/
def select (machine : Machine State Candidate) (state : State) :
    FiniteSearch.FirstResult (machine.frontier state).values
      (machine.Enabled state) :=
  FiniteSearch.firstOnList (machine.frontier state).values
    (machine.Enabled state) (machine.decideEnabled state)

/-- A proof-carrying exact execution from an indexed initial state.

The `step` constructor stores a `FirstHit`, so an execution certifies not only
that its selected candidate was enabled, but also that every earlier frontier
candidate was disabled. -/
inductive Execution (machine : Machine State Candidate) : State → Type (max u v)
  | saturated {state : State}
      (none : ∀ candidate, candidate ∈ (machine.frontier state).values →
        ¬ machine.Enabled state candidate) :
      Execution machine state
  | step {state : State}
      (hit : FiniteSearch.FirstHit (machine.frontier state).values
        (machine.Enabled state))
      (rest : Execution machine
        (machine.advance state hit.value hit.member hit.holds)) :
      Execution machine state

/-- Execute first-enabled transitions until the exact frontier is saturated. -/
def execute (machine : Machine State Candidate) (state : State) :
    Execution machine state :=
  match machine.select state with
  | .found hit =>
      .step hit (execute machine
        (machine.advance state hit.value hit.member hit.holds))
  | .absent absentProof => .saturated absentProof
termination_by machine.measure state
decreasing_by
  exact machine.advance_decreases state hit.value hit.member hit.holds

namespace Execution

variable {machine : Machine State Candidate}

/-- Final state reached by an exact execution. -/
def terminal {state : State} : Execution machine state → State
  | .saturated _ => state
  | .step _ rest => rest.terminal

/-- Candidates selected by the execution, in transition order. -/
def choices {state : State} : Execution machine state → List Candidate
  | .saturated _ => []
  | .step hit rest => hit.value :: rest.choices

/-- States visited by the execution, including its initial and final states. -/
def states {state : State} : Execution machine state → List State
  | .saturated _ => [state]
  | .step _ rest => state :: rest.states

/-- The final state has no enabled candidate in its exact frontier. -/
theorem terminal_saturated {state : State} (execution : Execution machine state) :
    ∀ candidate,
      candidate ∈ (machine.frontier execution.terminal).values →
        ¬ machine.Enabled execution.terminal candidate := by
  induction execution with
  | saturated none => simpa only [terminal] using none
  | step hit rest inductionHypothesis =>
      simpa only [terminal] using inductionHypothesis

/-- The ranking bounds the number of transitions in every certified
execution, independently of the concrete candidate type. -/
theorem choices_length_le_measure {state : State}
    (execution : Execution machine state) :
    execution.choices.length ≤ machine.measure state := by
  induction execution with
  | saturated none => simp [choices]
  | step hit rest inductionHypothesis =>
      simp only [choices, List.length_cons]
      exact Nat.succ_le_of_lt <| Nat.lt_of_le_of_lt inductionHypothesis <|
        machine.advance_decreases _ hit.value hit.member hit.holds

/-- Every nonterminal execution exposes the exact first enabled candidate. -/
theorem step_is_first {initial : State} {hit : FiniteSearch.FirstHit
      (machine.frontier initial).values (machine.Enabled initial)}
    {rest : Execution machine
      (machine.advance initial hit.value hit.member hit.holds)} :
    (Execution.step hit rest : Execution machine initial).choices.head? =
      some hit.value := by
  rfl

end Execution

end Machine

end StructuralExhaustion.Core.FiniteSaturation
