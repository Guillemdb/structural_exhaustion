import StructuralExhaustion.CT12.Graph

namespace StructuralExhaustion.CT12

universe uAmbient uBranch uState uPeeled uDemand uTier
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uState, uPeeled, uDemand, uTier} P)

inductive Outcome : Graph.Terminal → Type _ where
  | exhausted (certificate : ExhaustedCertificate capability) : Outcome .exhausted
  | demand (residual : capability.DemandResidual) : Outcome .demand
  | tier (residual : capability.TierResidual) : Outcome .tier

/-- Result of the well-founded loop from one indexed state. -/
structure LoopResult (load : Nat) (_state : capability.State load) where
  terminal : Graph.Terminal
  path : Graph.Path capability .saturation terminal.nodeId
  outcome : Outcome capability terminal
  iterations : Nat
  iterations_le_load : iterations ≤ load
  trace_length_le : path.trace.length ≤ 4 * load + 2

/-- Genuine well-founded recursion.  The only recursive call consumes the
strict inequality returned by `Restoration.continue`. -/
def runLoop : (load : Nat) → (state : capability.State load) →
    LoopResult capability load state
  | 0, state => {
      terminal := .exhausted
      path := .cons (.exhausted state) (.nil .exhaustedTerminal)
      outcome := .exhausted ⟨state⟩
      iterations := 0
      iterations_le_load := by simp
      trace_length_le := by simp [Graph.Path.trace]
    }
  | n + 1, state =>
      let peeled := capability.peel state
      let options := capability.restorations peeled
      match options.first with
        | .demand residual => {
          terminal := .demand
          path := .cons (.positive state)
            (.cons (.peeled peeled)
              (.cons (.demand peeled residual) (.nil .demandTerminal)))
          outcome := .demand residual
          iterations := 1
          iterations_le_load := by simp
          trace_length_le := by simp [Graph.Path.trace, Nat.mul_succ]
        }
        | .tier residual => {
          terminal := .tier
          path := .cons (.positive state)
            (.cons (.peeled peeled)
              (.cons (.tier peeled residual) (.nil .tierTerminal)))
          outcome := .tier residual
          iterations := 1
          iterations_le_load := by simp
          trace_length_le := by simp [Graph.Path.trace, Nat.mul_succ]
        }
        | .continue next nextState decreases =>
          let recursive := runLoop next nextState
          have nextLe : next ≤ n := Nat.le_of_lt_succ (by simpa using decreases)
          have iterationsLe : Nat.succ recursive.iterations ≤ n + 1 :=
            Nat.succ_le_succ (Nat.le_trans recursive.iterations_le_load nextLe)
          have mulLe : 4 * next ≤ 4 * n := Nat.mul_le_mul_left 4 nextLe
          have traceLe : 4 + recursive.path.trace.length ≤ 4 * (n + 1) + 2 := by
            calc
              4 + recursive.path.trace.length ≤ 4 + (4 * next + 2) :=
                Nat.add_le_add_left recursive.trace_length_le 4
              _ ≤ 4 + (4 * n + 2) :=
                Nat.add_le_add_left (Nat.add_le_add_right mulLe 2) 4
              _ = 4 * (n + 1) + 2 := by omega
          {
            terminal := recursive.terminal
            path := .cons (.positive state)
              (.cons (.peeled peeled)
                (.cons (.continue peeled nextState decreases)
                  (.cons (.loopBack peeled nextState decreases) recursive.path)))
            outcome := recursive.outcome
            iterations := Nat.succ recursive.iterations
            iterations_le_load := iterationsLe
            trace_length_le := by
              have lengthEq :
                  (Graph.Path.trace capability
                    (.cons (.positive state)
                      (.cons (.peeled peeled)
                        (.cons (.continue peeled nextState decreases)
                          (.cons (.loopBack peeled nextState decreases)
                            recursive.path))))).length =
                    4 + recursive.path.trace.length := by
                simp only [Graph.Path.trace, List.length_cons]
                omega
              rw [lengthEq]
              exact traceLe
          }
termination_by load => load

structure ExecutionResult (input : Input capability) where
  terminal : Graph.Terminal
  path : Graph.Path capability .entry terminal.nodeId
  outcome : Outcome capability terminal
  iterations : Nat
  iterations_le_load : iterations ≤ input.load
  trace_length_le : path.trace.length ≤ 4 * input.load + 3

namespace ExecutionResult
def trace {input : Input capability} (result : ExecutionResult capability input) :=
  result.path.trace
end ExecutionResult

def runReference (input : Input capability) : ExecutionResult capability input :=
  let loop := runLoop capability input.load input.state
  {
    terminal := loop.terminal
    path := .cons .begin loop.path
    outcome := loop.outcome
    iterations := loop.iterations
    iterations_le_load := loop.iterations_le_load
    trace_length_le := by
      simpa [Graph.Path.trace, Nat.add_assoc] using
        Nat.add_le_add_left loop.trace_length_le 1
  }

def run (input : Input capability) : ExecutionResult capability input :=
  runReference capability input

end StructuralExhaustion.CT12
