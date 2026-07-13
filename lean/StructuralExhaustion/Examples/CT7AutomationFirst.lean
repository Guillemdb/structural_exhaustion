import StructuralExhaustion.CT7.Automation

namespace StructuralExhaustion.Examples.CT7AutomationFirst

open StructuralExhaustion

structure Object where
  realizes : Bool
  response : Bool

@[implicit_reducible]
def bools : FinEnum Bool :=
  StructuralExhaustion.Core.Enumeration.bool

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def ctx : Core.BranchContext problem where
  G := ()
  baseline := trivial
  state := ()

def spec : CT7.Spec problem where
  Object := Object
  Context := Bool
  Realizes := fun _ object context => object.realizes = true ∧ context = true
  response := fun _ object context => if context then object.response else false

def capability : CT7.Capability spec where
  contexts := fun _ _ _ => bools
  realizesDecidable := by
    intro _ object context
    change Decidable (object.realizes = true ∧ context = true)
    cases object.realizes <;> cases context
    · exact .isFalse (by simp)
    · exact .isFalse (by simp)
    · exact .isFalse (by simp)
    · exact .isTrue ⟨rfl, rfl⟩

def realizationInput : CT7.Input spec ctx where
  left := ⟨true, false⟩
  right := ⟨false, true⟩
def distinguishingInput : CT7.Input spec ctx where
  left := ⟨false, true⟩
  right := ⟨false, false⟩
def neutralInput : CT7.Input spec ctx where
  left := ⟨false, true⟩
  right := ⟨false, true⟩

def realizationResult := CT7.run spec capability ctx realizationInput
def distinguishingResult := CT7.run spec capability ctx distinguishingInput
def neutralResult := CT7.run spec capability ctx neutralInput

theorem realization_terminal : realizationResult.terminal = .realization := rfl
theorem distinguishing_terminal : distinguishingResult.terminal = .distinguishing := rfl
theorem neutral_terminal : neutralResult.terminal = .neutral := rfl
theorem realization_trace : realizationResult.trace =
    [.entry, .realizationSearch, .realizationTerminal] := rfl
theorem distinguishing_trace : distinguishingResult.trace =
    [.entry, .realizationSearch, .distinctionSearch, .distinguishingTerminal] := rfl
theorem neutral_trace : neutralResult.trace =
    [.entry, .realizationSearch, .distinctionSearch, .neutralTerminal] := rfl

example : realizationResult.outcome.Valid := realizationResult.verified
example : distinguishingResult.outcome.Valid := distinguishingResult.verified
example : neutralResult.outcome.Valid := neutralResult.verified
example : ∃ result : CT7.ExecutionResult spec capability ctx neutralInput,
    result.outcome.Valid ∧
      CT7.Graph.ValidTrace spec capability ctx neutralInput result.trace := by
  ct7_total spec using capability at ctx on neutralInput

end StructuralExhaustion.Examples.CT7AutomationFirst
