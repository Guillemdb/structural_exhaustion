import StructuralExhaustion.CT4.Automation

namespace StructuralExhaustion.Examples.CT4AutomationFirst

open StructuralExhaustion

inductive Mode where | missing | overloaded | normal
  deriving Repr, DecidableEq

structure Fixture where
  mode : Mode
  required : Nat

@[implicit_reducible]
def bools : FinEnum Bool :=
  StructuralExhaustion.Core.Enumeration.bool

def problem : Core.Problem where
  Ambient := Fixture
  Baseline := fun _ => True
  rank := fun G => G.required
  BranchState := fun _ => Unit

def eligible (ctx : Core.BranchContext problem) (demand payer : Bool) : Prop :=
  match ctx.G.mode with
  | .missing => False
  | .overloaded => payer = false
  | .normal => payer = demand

def capacity (ctx : Core.BranchContext problem) (payer : Bool) : Nat :=
  match ctx.G.mode with
  | .missing => 0
  | .overloaded => if payer then 0 else 1
  | .normal => 1

def spec : CT4.Spec problem where
  Demand := Bool
  Payer := Bool
  Eligible := eligible
  demandWeight := fun _ _ => 1
  capacity := capacity

def capability : CT4.Capability spec where
  demands := bools
  payers := bools
  eligibleDecidable := by
    intro ctx demand payer
    change Decidable (eligible ctx demand payer)
    unfold eligible
    cases ctx.G.mode with
    | missing => exact .isFalse (fun falseProof => falseProof)
    | overloaded => exact Bool.decEq payer false
    | normal => exact Bool.decEq payer demand
  required := fun ctx => ctx.G.required

def input (mode : Mode) (required : Nat) : CT4.Input problem where
  G := ⟨mode, required⟩
  baseline := trivial
  state := ()

def missingResult := CT4.run spec capability (input .missing 0)
def overloadResult := CT4.run spec capability (input .overloaded 0)
def c4Result := CT4.run spec capability (input .normal 3)
def capacityResult := CT4.run spec capability (input .normal 1)

theorem missing_terminal : missingResult.terminal = .missing := rfl
theorem overload_terminal : overloadResult.terminal = .overload := rfl
theorem c4_terminal : c4Result.terminal = .c4 := rfl
theorem capacity_terminal : capacityResult.terminal = .capacity := rfl

theorem first_eligible_is_canonical :
    CT4.assignedPayer spec capability (input .normal 1) true = some true := rfl
theorem overload_assigns_first_payer :
    CT4.assignedPayer spec capability (input .overloaded 0) true = some false := rfl

theorem missing_trace : missingResult.trace =
    [.entry, .assignment, .availability, .missingTerminal] := rfl
theorem overload_trace : overloadResult.trace =
    [.entry, .assignment, .availability, .fibres, .overloadTerminal] := rfl
theorem c4_trace : c4Result.trace =
    [.entry, .assignment, .availability, .fibres, .comparison, .c4Terminal] := rfl
theorem capacity_trace : capacityResult.trace =
    [.entry, .assignment, .availability, .fibres, .comparison,
      .capacityTerminal] := rfl

example : missingResult.outcome.Valid := missingResult.verified
example : overloadResult.outcome.Valid := overloadResult.verified
example : c4Result.outcome.Valid := c4Result.verified
example : capacityResult.outcome.Valid := capacityResult.verified
example : ∃ result : CT4.ExecutionResult spec capability (input .normal 1),
    result.outcome.Valid ∧
      CT4.Graph.ValidTrace spec capability (input .normal 1) result.trace := by
  ct4_total spec using capability at (input .normal 1)

end StructuralExhaustion.Examples.CT4AutomationFirst
