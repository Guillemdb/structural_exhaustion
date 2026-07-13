import StructuralExhaustion.Core.FiniteSaturation

namespace StructuralExhaustion.Examples.FiniteSaturation

open Core

/-! Kernel fixture for the generic exact sequential saturation machine. -/

structure RemovalState where
  remaining : List Bool
  nodup : remaining.Nodup

def removalMachine : Core.FiniteSaturation.Machine RemovalState Bool where
  frontier state := {
    values := state.remaining
    nodup := state.nodup
    decEq := inferInstance
  }
  Enabled _ _ := True
  decideEnabled _ _ := inferInstance
  advance state candidate member _ := {
    remaining := state.remaining.erase candidate
    nodup := state.nodup.erase candidate
  }
  measure state := state.remaining.length
  advance_decreases state candidate member _ := by
    simp only
    rw [List.length_erase_of_mem member]
    exact Nat.sub_one_lt (Nat.ne_of_gt (List.length_pos_of_mem member))

def initial : RemovalState := {
  remaining := [false, true]
  nodup := by decide
}

def run := removalMachine.execute initial

example : run.choices = [false, true] := by native_decide

example : run.terminal.remaining = [] := by native_decide

example : run.states.map RemovalState.remaining =
    [[false, true], [true], []] := by native_decide

example : run.choices.length ≤ removalMachine.measure initial :=
  run.choices_length_le_measure

example : ∀ candidate,
    candidate ∈ (removalMachine.frontier run.terminal).values →
      ¬ removalMachine.Enabled run.terminal candidate :=
  run.terminal_saturated

/-! A state-dependent frontier with its first candidate disabled checks that
the machine uses ordered first-hit search rather than arbitrary choice. -/

def stateDependentMachine : Core.FiniteSaturation.Machine Bool Bool where
  frontier state := {
    values := if state then [false] else [false, true]
    nodup := by cases state <;> decide
    decEq := inferInstance
  }
  Enabled state candidate := state = false ∧ candidate = true
  decideEnabled state candidate := by infer_instance
  advance _state _candidate _member _enabled := true
  measure state := if state then 0 else 1
  advance_decreases state candidate member enabled := by
    cases state <;> simp_all

def stateDependentRun := stateDependentMachine.execute false

example : stateDependentRun.choices = [true] := by native_decide

example : stateDependentRun.states = [false, true] := by native_decide

example : stateDependentRun.states.length =
    stateDependentRun.choices.length + 1 := by native_decide

example : (stateDependentMachine.frontier stateDependentRun.terminal).values =
    [false] := by native_decide

end StructuralExhaustion.Examples.FiniteSaturation
