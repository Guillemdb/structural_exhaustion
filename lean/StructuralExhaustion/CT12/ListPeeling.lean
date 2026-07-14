import StructuralExhaustion.CT12.Theorems

namespace StructuralExhaustion.CT12.ListPeeling

open StructuralExhaustion

universe uAmbient uBranch uValue

/-- Minimal static authoring contract for canonical list peeling.  The
framework derives the indexed state, head/tail witness, capability, and exact
execution from this sole type field. -/
structure Profile where
  Value : Type uValue

/-- A list whose length is carried in its type. -/
structure State (Value : Type uValue) (load : Nat) where
  values : List Value
  length_eq : values.length = load

/-- The exact head/tail decomposition computed at one positive-load peeling
step. -/
structure Peeled (Value : Type uValue) {load : Nat}
    (state : State Value (load + 1)) where
  head : Value
  tail : State Value load
  exact : state.values = head :: tail.values

/-- Every positive indexed list has a canonical head/tail decomposition. -/
def peel {Value : Type uValue} {load : Nat}
    (state : State Value (load + 1)) : Peeled Value state := by
  cases valuesEqual : state.values with
  | nil =>
      have lengthEqual := state.length_eq
      simp [valuesEqual] at lengthEqual
  | cons head tail =>
      have tailLength : tail.length = load := by
        simpa [valuesEqual] using state.length_eq
      exact {
        head := head
        tail := ⟨tail, tailLength⟩
        exact := valuesEqual
      }

/-- Domain-independent CT12 capability that repeatedly removes the head of a
list.  Demand and tier terminals are uninhabited; the only positive-load edge
is the strictly decreasing continuation to the tail. -/
def capability (P : Core.Problem.{uAmbient, uBranch})
    (Value : Type uValue) : CT12.Capability P where
  State := State Value
  DemandResidual := Empty
  TierResidual := Empty
  Peeled := Peeled Value
  peel := peel
  restorations := fun {n} {_state} peeled => {
    first := .continue n peeled.tail (Nat.lt_succ_self n)
  }

/-- Canonical indexed state associated with an ordinary list. -/
def initialState (values : List Value) : State Value values.length :=
  ⟨values, rfl⟩

/-- Exact CT12 execution for the canonical head-peeling schedule. -/
def run {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (values : List Value) :
    CT12.ExecutionResult (capability P Value) {
      context := context
      load := values.length
      state := initialState values
    } :=
  CT12.run (capability P Value) {
    context := context
    load := values.length
    state := initialState values
  }

/-- Exact node sequence of an exhausted canonical list-peeling run. -/
def expectedLoopTrace : Nat → List CT12.Graph.NodeId
  | 0 => [.saturation, .exhaustedTerminal]
  | n + 1 => [.saturation, .peel, .restoration, .decrease] ++
      expectedLoopTrace n

def expectedTrace (length : Nat) : List CT12.Graph.NodeId :=
  .entry :: expectedLoopTrace length

private theorem runLoop_terminal_exhausted
    {P : Core.Problem.{uAmbient, uBranch}}
    (load : Nat) (state : State Value load) :
    (CT12.runLoop (capability P Value) load state).terminal =
      .exhausted := by
  induction load using Nat.strong_induction_on with
  | h load ih =>
      cases load with
      | zero => simp [CT12.runLoop]
      | succ n =>
          simp only [CT12.runLoop, capability]
          exact ih n (Nat.lt_succ_self n) (peel state).tail

/-- List peeling cannot reach either semantic residual terminal. -/
theorem run_terminal_exhausted {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (values : List Value) :
    (run context values).terminal = .exhausted := by
  exact runLoop_terminal_exhausted values.length (initialState values)

private theorem runLoop_trace_eq_expected
    {P : Core.Problem.{uAmbient, uBranch}}
    (load : Nat) (state : State Value load) :
    (CT12.runLoop (capability P Value) load state).path.trace =
      expectedLoopTrace load := by
  induction load using Nat.strong_induction_on with
  | h load ih =>
      cases load with
      | zero =>
          rw [CT12.runLoop]
          rfl
      | succ n =>
          rw [CT12.runLoop]
          change [.saturation, .peel, .restoration, .decrease] ++
              (CT12.runLoop (capability P Value) n
                (peel state).tail).path.trace =
            [.saturation, .peel, .restoration, .decrease] ++
              expectedLoopTrace n
          rw [ih n (Nat.lt_succ_self n) (peel state).tail]

/-- Exact typed trace of canonical list peeling, including every loop-back. -/
theorem run_trace_eq_expected {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (values : List Value) :
    (run context values).trace = expectedTrace values.length := by
  unfold run expectedTrace CT12.ExecutionResult.trace CT12.run
    CT12.runReference
  simp only [CT12.Graph.Path.trace]
  rw [runLoop_trace_eq_expected values.length (initialState values)]
  rfl

private theorem runLoop_iterations_eq_length
    {P : Core.Problem.{uAmbient, uBranch}}
    (load : Nat) (state : State Value load) :
    (CT12.runLoop (capability P Value) load state).iterations = load := by
  induction load using Nat.strong_induction_on with
  | h load ih =>
      cases load with
      | zero => simp [CT12.runLoop]
      | succ n =>
          simp only [CT12.runLoop, capability]
          change Nat.succ
            ((CT12.runLoop (capability P Value) n
              (peel state).tail).iterations) = n + 1
          rw [ih n (Nat.lt_succ_self n) (peel state).tail]

/-- Canonical list peeling performs exactly one iteration per list element. -/
theorem run_iterations_eq_length {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (values : List Value) :
    (run context values).iterations = values.length := by
  exact runLoop_iterations_eq_length values.length (initialState values)

end StructuralExhaustion.CT12.ListPeeling
