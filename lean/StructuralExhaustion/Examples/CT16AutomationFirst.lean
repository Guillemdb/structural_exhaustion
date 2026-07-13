import StructuralExhaustion.CT16.Automation

namespace StructuralExhaustion.Examples.CT16AutomationFirst
open StructuralExhaustion

inductive Obj | proper | equal | mismatch
def objEq : DecidableEq Obj := by
  intro left right
  cases left <;> cases right
  all_goals first | exact .isTrue rfl | exact .isFalse (by intro h; cases h)
def P : Core.Problem where
  Ambient := Obj; Baseline := fun _ => True; rank := fun _ => 0
  BranchState := fun _ => Unit
@[implicit_reducible]
def coords : FinEnum Unit := Core.Enumeration.unit
def C : CT16.Capability P where
  Coordinate := Unit; coordinates := coords
  InSupport := fun G _ => G ≠ .proper
  inSupportDecidable := by
    intro G _
    match objEq G .proper with
    | .isTrue equal => exact .isFalse (fun notEqual => notEqual equal)
    | .isFalse notEqual => exact .isTrue notEqual
  ClosedCode := Bool; codeDecidableEq := inferInstance
  closedCode := fun G => match G with | .mismatch => true | _ => false
  targetCode := false
def ctx (G : Obj) : Core.BranchContext P := ⟨G, trivial, ()⟩
def input (G) : CT16.Input C (ctx G) := ⟨⟩
def properResult := CT16.run C (ctx .proper) (input .proper)
def equalResult := CT16.run C (ctx .equal) (input .equal)
def mismatchResult := CT16.run C (ctx .mismatch) (input .mismatch)
example : properResult.terminal = .proper := rfl
example : equalResult.terminal = .equal := rfl
example : mismatchResult.terminal = .mismatch := rfl
example : properResult.trace = [.entry, .supportScan, .properTerminal] := rfl
example : equalResult.trace =
    [.entry, .supportScan, .codeComputation, .codeComparison, .equalTerminal] := rfl
example : mismatchResult.trace =
    [.entry, .supportScan, .codeComputation, .codeComparison, .mismatchTerminal] := rfl
example : properResult.outcome.Valid := CT16.run_verified C _ _
example : equalResult.outcome.Valid := CT16.run_verified C _ _
example : mismatchResult.outcome.Valid := CT16.run_verified C _ _
example : mismatchResult.outcome.Valid := by
  ct16 C at (ctx .mismatch) on (input .mismatch)
example : ∃ r : CT16.ExecutionResult C (ctx .mismatch), r.outcome.Valid ∧
    @CT16.Graph.ValidTrace P C (ctx .mismatch) r.trace := by
  ct16_total C at (ctx .mismatch) on (input .mismatch)

end StructuralExhaustion.Examples.CT16AutomationFirst
