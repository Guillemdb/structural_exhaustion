import StructuralExhaustion.CT13.Automation

namespace StructuralExhaustion.Examples.CT13AutomationFirst

open StructuralExhaustion

inductive Obj where
  | tierOne | overlap | deficit | reconciled
  deriving DecidableEq

def P : Core.Problem where
  Ambient := Obj
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

@[implicit_reducible]
def bools : FinEnum Bool :=
  StructuralExhaustion.Core.Enumeration.bool

@[implicit_reducible]
def units : FinEnum Unit :=
  StructuralExhaustion.Core.Enumeration.unit

def two : Core.OrderedCollection Bool where
  values := [false, true]
  nodup := by decide
  decEq := inferInstance

abbrev C : CT13.Capability P where
  Payer := Bool
  payers := bools
  Eligible := fun ctx payer => match ctx.G, payer with
    | .tierOne, false => True
    | _, _ => False
  eligibleDecidable := by
    intro ctx payer
    cases ctx.G <;> cases payer <;> exact inferInstance
  Obstruction := Unit
  obstructions := units
  fallbackDefault := ()
  obstructionCost := fun _ _ => 0
  Resource := Bool
  resourceDecidableEq := inferInstance
  resource := fun ctx payer => match ctx.G with
    | .overlap => false
    | _ => payer
  tierTwo := fun _ _ => two
  charge := fun _ _ => 1
  demand := fun ctx => match ctx.G with
    | .deficit => 3
    | _ => 2

def ctx (G : Obj) : Core.BranchContext P := ⟨G, trivial, ()⟩
def input (G : Obj) : CT13.Input C (ctx G) := ⟨⟩

def tierOneResult := CT13.run C (ctx .tierOne) (input .tierOne)
def overlapResult := CT13.run C (ctx .overlap) (input .overlap)
def deficitResult := CT13.run C (ctx .deficit) (input .deficit)
def reconciledResult := CT13.run C (ctx .reconciled) (input .reconciled)

example : tierOneResult.terminal = .tierOne := rfl
example : overlapResult.terminal = .overlap := rfl
example : deficitResult.terminal = .deficit := rfl
example : reconciledResult.terminal = .reconciled := rfl

example : tierOneResult.outcome.Valid := CT13.run_verified C _ _
example : overlapResult.outcome.Valid := CT13.run_verified C _ _
example : deficitResult.outcome.Valid := CT13.run_verified C _ _
example : reconciledResult.outcome.Valid := CT13.run_verified C _ _
example : reconciledResult.outcome.Valid := by
  ct13 C at (ctx .reconciled) on (input .reconciled)

example : ∃ result : CT13.ExecutionResult C (ctx .reconciled),
    result.outcome.Valid ∧
      @CT13.Graph.ValidTrace P C (ctx .reconciled) result.trace := by
  ct13_total C at (ctx .reconciled) on (input .reconciled)

example : reconciledResult.trace =
    [.entry, .tierOne, .fallback, .reconciliation,
      .comparison, .reconciledTerminal] := rfl

end StructuralExhaustion.Examples.CT13AutomationFirst
