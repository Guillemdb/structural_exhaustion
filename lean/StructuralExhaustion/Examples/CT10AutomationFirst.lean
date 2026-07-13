import StructuralExhaustion.CT10.Automation

namespace StructuralExhaustion.Examples.CT10AutomationFirst

open StructuralExhaustion

abbrev problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def context : Core.BranchContext problem := ⟨(), trivial, ()⟩

@[implicit_reducible]
def bools : FinEnum Bool :=
  StructuralExhaustion.Core.Enumeration.bool

def falseOnly : Core.OrderedCollection Bool where
  values := [false]
  nodup := by decide
  decEq := inferInstance

def both : Core.OrderedCollection Bool where
  values := [false, true]
  nodup := by decide
  decEq := inferInstance

abbrev directCapability : CT10.Capability problem where
  Datum := Bool
  Class := Bool
  Promotion := Bool
  classes := bools
  classOf := id
  Direct := fun cls => cls = false
  directDecidable := fun _ => inferInstance
  promote := id

def directInput : CT10.Input directCapability := ⟨context, falseOnly⟩
def directTrigger : CT10.Trigger directCapability context := ⟨falseOnly⟩
def routedDirectInput : CT10.Input directCapability :=
  CT10.Input.ofTrigger context directTrigger
example : routedDirectInput.context = context := rfl
example : routedDirectInput.data = falseOnly := rfl
def directResult := ct10_execute directCapability on directInput
example : directResult.terminal = .direct := rfl
example : directResult.trace = [.entry, .table, .direct, .directTerminal] := rfl
example : directResult.outcome.Valid := by ct10 directCapability on directInput
example : ∃ result : CT10.ExecutionResult directCapability directInput,
    result.outcome.Valid ∧
      CT10.Graph.ValidTrace directCapability directInput result.trace := by
  ct10_total directCapability on directInput

abbrev noDirectCapability : CT10.Capability problem where
  Datum := Bool
  Class := Bool
  Promotion := Bool
  classes := bools
  classOf := id
  Direct := fun _ => False
  directDecidable := fun _ => inferInstance
  promote := not

def promotedInput : CT10.Input noDirectCapability := ⟨context, falseOnly⟩
def promotedResult := ct10_execute noDirectCapability on promotedInput
example : promotedResult.terminal = .promoted := rfl
example : promotedResult.trace =
    [.entry, .table, .direct, .missing, .promotion, .promotedTerminal] := rfl
example : promotedResult.outcome.Valid := CT10.run_verified noDirectCapability promotedInput

def exhaustiveInput : CT10.Input noDirectCapability := ⟨context, both⟩
def exhaustiveResult := ct10_execute noDirectCapability on exhaustiveInput
example : exhaustiveResult.terminal = .exhaustive := rfl
example : exhaustiveResult.trace =
    [.entry, .table, .direct, .missing, .exhaustiveTerminal] := rfl
example : exhaustiveResult.outcome.Valid := CT10.run_verified noDirectCapability exhaustiveInput
example : exhaustiveResult = exhaustiveResult :=
  CT10.run_deterministic noDirectCapability exhaustiveInput
    exhaustiveResult exhaustiveResult rfl rfl
example : exhaustiveResult.terminal = .direct ∨
    exhaustiveResult.terminal = .promoted ∨
    exhaustiveResult.terminal = .exhaustive :=
  CT10.outcome_exhaustive noDirectCapability exhaustiveInput exhaustiveResult

def contractNodeIds := CT10.nodeAutomationContracts.map (·.nodeId)
def capabilityDefinitionRefs :=
  CT10.capabilityContract.requiredDefinitions.map (·.ref)
def authorInputRefs := CT10.nodeAutomationContracts.flatMap fun contract =>
  contract.authorInputs.map (·.ref)
example : contractNodeIds = ["CT10.entry", "CT10.compute.classTable",
    "CT10.search.direct", "CT10.search.firstMissing",
    "CT10.compute.promotion"] := by native_decide
example : (CT10.nodeAutomationContracts.all fun contract =>
    !contract.generatedOutputs.isEmpty && contract.manualObligations.isEmpty) = true :=
  by native_decide
example : (authorInputRefs.all capabilityDefinitionRefs.contains) = true :=
  by native_decide

end StructuralExhaustion.Examples.CT10AutomationFirst
