import StructuralExhaustion.CT11.Automation

namespace StructuralExhaustion.Examples.CT11AutomationFirst

open StructuralExhaustion

abbrev problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def context : Core.BranchContext problem := ⟨(), trivial, ()⟩

def cells : Core.OrderedCollection Bool where
  values := [false, true]
  nodup := by decide
  decEq := inferInstance

abbrev gapCapability : CT11.Capability problem where
  Cell := Bool
  Admissible := fun _ cell => cell = false
  admissibleDecidable := fun _ _ => inferInstance
  localBudget := fun _ cell => if cell then 0 else -1

def gapInput : CT11.Input gapCapability where
  context := context
  cells := cells
  deficit := by decide

def gapTrigger : CT11.Trigger gapCapability context where
  cells := cells
  deficit := by decide
def routedGapInput : CT11.Input gapCapability :=
  CT11.Input.ofTrigger context gapTrigger
example : routedGapInput.context = context := rfl
example : routedGapInput.cells = cells := rfl

def gapResult := ct11_execute gapCapability on gapInput
example : gapResult.terminal = .gap := rfl
example : gapResult.trace = [.entry, .decomposition, .admissibility, .gapTerminal] := rfl
example : gapResult.outcome.Valid := by ct11 gapCapability on gapInput
example : ∃ result : CT11.ExecutionResult gapCapability gapInput,
    result.outcome.Valid ∧
      CT11.Graph.ValidTrace gapCapability gapInput result.trace := by
  ct11_total gapCapability on gapInput

abbrev localizedCapability : CT11.Capability problem where
  Cell := Bool
  Admissible := fun _ _ => True
  admissibleDecidable := fun _ _ => inferInstance
  localBudget := fun _ cell => if cell then -2 else 1

def localizedInput : CT11.Input localizedCapability where
  context := context
  cells := cells
  deficit := by decide

def localizedResult := ct11_execute localizedCapability on localizedInput
example : localizedResult.terminal = .localized := rfl
example : localizedResult.trace =
    [.entry, .decomposition, .admissibility, .localization, .localizedTerminal] := rfl
example : localizedResult.outcome.Valid := CT11.run_verified localizedCapability localizedInput
example : localizedResult = localizedResult :=
  CT11.run_deterministic localizedCapability localizedInput
    localizedResult localizedResult rfl rfl
example : localizedResult.terminal = .gap ∨
    localizedResult.terminal = .localized :=
  CT11.outcome_exhaustive localizedCapability localizedInput localizedResult

def contractNodeIds := CT11.nodeAutomationContracts.map (·.nodeId)
def capabilityDefinitionRefs :=
  CT11.capabilityContract.requiredDefinitions.map (·.ref)
def authorInputRefs := CT11.nodeAutomationContracts.flatMap fun contract =>
  contract.authorInputs.map (·.ref)
example : contractNodeIds = ["CT11.entry", "CT11.compute.decomposition",
    "CT11.search.admissibilityGap", "CT11.search.localNegativeBudget"] :=
  by native_decide
example : (CT11.nodeAutomationContracts.all fun contract =>
    !contract.generatedOutputs.isEmpty && contract.manualObligations.isEmpty) = true :=
  by native_decide
example : (authorInputRefs.all capabilityDefinitionRefs.contains) = true :=
  by native_decide

end StructuralExhaustion.Examples.CT11AutomationFirst
