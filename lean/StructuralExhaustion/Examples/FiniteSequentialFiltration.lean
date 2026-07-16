import StructuralExhaustion.Core.FiniteSequentialFiltration

namespace StructuralExhaustion.Examples.FiniteSequentialFiltration

open StructuralExhaustion.Core
open StructuralExhaustion.Core.FiniteSequentialFiltration

@[implicit_reducible] def states : FinEnum (Fin 6) := inferInstance

def keepAtLeast (cutoff : Nat) : Barrier (Fin 6) where
  accepts := fun state => decide (cutoff ≤ state.1)
  safe := 3
  flat := 2

def passingProfile : Profile where
  State := Fin 6
  states := states
  barriers := [keepAtLeast 2, keepAtLeast 4]

def failingProfile : Profile where
  State := Fin 6
  states := states
  barriers := [keepAtLeast 2, keepAtLeast 3]

/-- Regression profile for the vacuous complete branch: a paying filtration
may reject every state.  Applications must therefore prove terminal
nonemptiness from their own semantics before interpreting the product bound
as entropy. -/
def rejectsAll : Barrier (Fin 6) where
  accepts := fun _ => false
  safe := 2
  flat := 1

def emptyTerminalProfile : Profile where
  State := Fin 6
  states := states
  barriers := [rejectsAll]

def emptyTerminalLedger : CompleteLedger
    emptyTerminalProfile.states.orderedValues
    emptyTerminalProfile.barriers :=
  .cons (by native_decide) (.nil _)

theorem emptyTerminal_complete :
    emptyTerminalProfile.run = Outcome.complete emptyTerminalLedger := by
  rfl

theorem emptyTerminal_is_empty :
    emptyTerminalLedger.finalStates = [] := by
  rfl

def passingLedger : CompleteLedger passingProfile.states.orderedValues
    passingProfile.barriers :=
  .cons (by native_decide) (.cons (by native_decide) (.nil _))

theorem passing_result :
    passingProfile.run = Outcome.complete passingLedger := by
  rfl

theorem passing_product_bound :
    ∃ ledger : CompleteLedger passingProfile.states.orderedValues
        passingProfile.barriers,
      (passingProfile.barriers.map Barrier.safe).prod *
          ledger.finalStates.length ≤
        (passingProfile.barriers.map Barrier.flat).prod *
          passingProfile.states.card := by
  refine ⟨passingLedger, ?_⟩
  simpa using passingLedger.product_le

def failingFailure : FirstFailure failingProfile.states.orderedValues
    failingProfile.barriers :=
  .later (by native_decide) (.here (by native_decide))

theorem failing_result :
    failingProfile.run = Outcome.firstFailure failingFailure := by
  rfl

theorem failing_is_second :
    ∃ failure : FirstFailure failingProfile.states.orderedValues
        failingProfile.barriers,
      failure.index = 1 ∧
        failure.beforeStates.length = 4 ∧
        failure.afterStates.length = 3 ∧
        Fails failure.beforeStates failure.barrier := by
  exact ⟨failingFailure, by native_decide, by native_decide,
    by native_decide, failingFailure.fails⟩

end StructuralExhaustion.Examples.FiniteSequentialFiltration
