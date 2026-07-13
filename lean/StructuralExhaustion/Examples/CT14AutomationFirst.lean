import StructuralExhaustion.CT14.Automation

namespace StructuralExhaustion.Examples.CT14AutomationFirst

open StructuralExhaustion

inductive Obj where
  | unbounded | missing | aggregate | capacity

def P : Core.Problem where
  Ambient := Obj
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

@[implicit_reducible]
def units : FinEnum Unit :=
  StructuralExhaustion.Core.Enumeration.unit

abbrev C : CT14.Capability P where
  Member := Unit
  members := units
  Label := Unit
  labelDecidableEq := inferInstance
  memberLowerMass := fun ctx _ => match ctx.G with
    | .aggregate => 2
    | _ => 1
  memberCapacity := fun ctx _ => match ctx.G with
    | .unbounded => none
    | .aggregate => some 1
    | _ => some 2
  memberLabel := fun ctx _ => match ctx.G with
    | .missing => none
    | _ => some ()

def ctx (G : Obj) : Core.BranchContext P := ⟨G, trivial, ()⟩
def input (G : Obj) : CT14.Input C (ctx G) := ⟨⟩

def unboundedResult := CT14.run C (ctx .unbounded) (input .unbounded)
def missingResult := CT14.run C (ctx .missing) (input .missing)
def aggregateResult := CT14.run C (ctx .aggregate) (input .aggregate)
def capacityResult := CT14.run C (ctx .capacity) (input .capacity)

example : unboundedResult.terminal = .unbounded := rfl
example : missingResult.terminal = .missingLabel := rfl
example : aggregateResult.terminal = .aggregate := rfl
example : capacityResult.terminal = .capacity := rfl

example : unboundedResult.outcome.Valid := CT14.run_verified C _ _
example : missingResult.outcome.Valid := CT14.run_verified C _ _
example : aggregateResult.outcome.Valid := CT14.run_verified C _ _
example : capacityResult.outcome.Valid := CT14.run_verified C _ _
example : capacityResult.outcome.Valid := by
  ct14 C at (ctx .capacity) on (input .capacity)

example : ∃ result : CT14.ExecutionResult C (ctx .capacity),
    result.outcome.Valid ∧
      @CT14.Graph.ValidTrace P C (ctx .capacity) result.trace := by
  ct14_total C at (ctx .capacity) on (input .capacity)

example : aggregateResult.trace =
    [.entry, .lowerMass, .memberScan, .upperCapacity,
      .comparison, .aggregateTerminal] := rfl

example : CT14.multiplicity C (ctx .capacity) () = 1 := rfl

end StructuralExhaustion.Examples.CT14AutomationFirst
