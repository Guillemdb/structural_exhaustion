import StructuralExhaustion.CT5.Automation

namespace StructuralExhaustion.Examples.CT5AutomationFirst

open StructuralExhaustion

structure Fixture where
  supported : Bool
  amount : Nat

def problem : Core.Problem where
  Ambient := Fixture
  Baseline := fun _ => True
  rank := fun G => G.amount
  BranchState := fun _ => Unit

def spec : CT5.Spec problem where
  Site := Unit
  Witness := fun _ => Unit
  Active := fun _ _ => True
  Supports := fun ctx _ _ => ctx.G.supported = true
  contribution := fun ctx _ _ => ctx.G.amount

@[implicit_reducible]
def singletonUnit : FinEnum Unit :=
  StructuralExhaustion.Core.Enumeration.unit

def capability (required capacity : Nat) : CT5.Capability spec where
  sites := singletonUnit
  witnesses := fun _ => singletonUnit
  activeDecidable := fun _ _ => .isTrue trivial
  supportsDecidable := by
    intro ctx _ _
    change Decidable (ctx.G.supported = true)
    exact Bool.decEq _ _
  required := fun _ => required
  capacity := fun _ => capacity

def input (supported : Bool) (amount : Nat) : CT5.Input problem where
  G := ⟨supported, amount⟩
  baseline := trivial
  state := ()

def deficitResult := CT5.run spec (capability 1 1) (input false 2)
def c4Result := CT5.run spec (capability 3 1) (input true 2)
def chargeResult := CT5.run spec (capability 1 2) (input true 1)
def aggregateResult := CT5.run spec (capability 1 2) (input true 3)

theorem deficit_terminal : deficitResult.terminal = .deficit := rfl
theorem c4_terminal : c4Result.terminal = .c4 := rfl
theorem charge_terminal : chargeResult.terminal = .charge := rfl
theorem aggregate_terminal : aggregateResult.terminal = .aggregate := rfl

theorem deficit_trace : deficitResult.trace =
    [.entry, .deficitSearch, .deficitTerminal] := rfl
theorem c4_trace : c4Result.trace =
    [.entry, .deficitSearch, .summation, .comparison, .c4Terminal] := rfl
theorem charge_trace : chargeResult.trace =
    [.entry, .deficitSearch, .summation, .comparison, .chargeTerminal] := rfl
theorem aggregate_trace : aggregateResult.trace =
    [.entry, .deficitSearch, .summation, .comparison, .aggregateTerminal] := rfl

example : deficitResult.outcome.Valid := deficitResult.verified
example : c4Result.outcome.Valid := c4Result.verified
example : chargeResult.outcome.Valid := chargeResult.verified
example : aggregateResult.outcome.Valid := aggregateResult.verified

example : ∃ result : CT5.ExecutionResult spec (capability 1 2) (input true 3),
    result.outcome.Valid ∧
      CT5.Graph.ValidTrace spec (capability 1 2) (input true 3) result.trace := by
  ct5_total spec using (capability 1 2) at (input true 3)

end StructuralExhaustion.Examples.CT5AutomationFirst
