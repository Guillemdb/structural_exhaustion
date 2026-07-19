import StructuralExhaustion.Graph.SelectedSurplusMass

namespace StructuralExhaustion.Examples.SelectedSurplusMass

open StructuralExhaustion

inductive Item
  | left
  | middle
  | right
  deriving DecidableEq

@[implicit_reducible] def items : FinEnum Item :=
  @FinEnum.ofNodupList Item inferInstance [.left, .middle, .right]
    (by intro item; cases item <;> simp) (by simp)

def profile : Graph.SelectedSurplusMass.Profile Item where
  items := items
  Selected
    | .left | .right => True
    | .middle => False
  selectedDecidable := fun item => by cases item <;> infer_instance
  surplus
    | .left => 1
    | .middle => 2
    | .right => 3
  positive := by intro item; cases item <;> decide

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def context : Core.BranchContext problem := ⟨(), trivial, ()⟩

def execution : CT14.ExecutionResult (profile.capability problem) context :=
  CT14.run (profile.capability problem) context (profile.input context)

def stage : profile.VerifiedExecutionStage context execution :=
  profile.verifiedExecutionStage context execution rfl

example : profile.selectedCount = 2 := by native_decide
example : profile.selectedSurplus = 4 := by native_decide
example : profile.totalSurplus = 6 := by native_decide
example : profile.selectedCount ≤ profile.totalSurplus :=
  profile.selectedCount_le_totalSurplus
example : execution.terminal = .capacity := stage.terminal
example : execution.outcome.Valid := stage.verified
example : profile.checks = 13 := by native_decide

end StructuralExhaustion.Examples.SelectedSurplusMass
