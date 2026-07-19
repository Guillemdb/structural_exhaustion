import StructuralExhaustion.CT8.Automation

namespace StructuralExhaustion.Examples.CT8AutomationFirst

open StructuralExhaustion

inductive Object where | small | large deriving DecidableEq
def rank : Object → Nat | .small => 0 | .large => 1
abbrev problem : Core.Problem where
  Ambient := Object
  Baseline := fun _ => True
  rank := rank
  BranchState := fun _ => Unit
def context : Core.BranchContext problem := ⟨.large, trivial, ()⟩

@[implicit_reducible]
def units : FinEnum Unit :=
  StructuralExhaustion.Core.Enumeration.unit
@[implicit_reducible]
def bools : FinEnum Bool :=
  StructuralExhaustion.Core.Enumeration.bool

def removal (_ _ : Bool) : Core.SmallerObject problem context.G :=
  ⟨.small, by decide⟩

abbrev uniqueCapability : CT8.Capability problem where
  State := Bool
  ExactType := Bool
  ResponseContext := Unit
  exactTypes := bools
  responseContexts := units
  exactType := id
  response := fun state _ => state

def uniqueInput : CT8.Input uniqueCapability context := ⟨[false, true], removal⟩
example : uniqueCapability.executableInterface.Trigger context := uniqueInput
def uniqueResult := ct8_execute uniqueCapability at context on uniqueInput
example : uniqueResult.terminal = .noRepetition := rfl
example : uniqueResult.trace = [.entry, .repetition, .noRepetitionTerminal] := rfl
example : uniqueResult.outcome.Valid := by ct8 uniqueCapability at context on uniqueInput
example : ∃ result : CT8.ExecutionResult uniqueCapability context uniqueInput,
    result.outcome.Valid ∧
      CT8.Graph.ValidTrace uniqueCapability context uniqueInput result.trace := by
  ct8_total uniqueCapability at context on uniqueInput

abbrev separatingCapability : CT8.Capability problem where
  State := Bool
  ExactType := Unit
  ResponseContext := Unit
  exactTypes := units
  responseContexts := units
  exactType := fun _ => ()
  response := fun state _ => state

def separatingInput : CT8.Input separatingCapability context :=
  ⟨[false, true], removal⟩
def separatingResult := ct8_execute separatingCapability at context on separatingInput
example : separatingResult.terminal = .separation := rfl
example : separatingResult.trace =
    [.entry, .repetition, .response, .separationTerminal] := rfl
example : separatingResult.outcome.Valid :=
  CT8.run_verified separatingCapability context separatingInput

abbrev removalCapability : CT8.Capability problem where
  State := Bool
  ExactType := Unit
  ResponseContext := Unit
  exactTypes := units
  responseContexts := units
  exactType := fun _ => ()
  response := fun _ _ => false

def removalInput : CT8.Input removalCapability context := ⟨[false, true], removal⟩
def removalResult := ct8_execute removalCapability at context on removalInput
example : removalResult.terminal = .removal := rfl
example : removalResult.trace = [.entry, .repetition, .response, .removalTerminal] := rfl
example : removalResult.outcome.Valid := CT8.run_verified removalCapability context removalInput
example : removalResult = removalResult :=
  CT8.run_deterministic removalCapability context removalInput
    removalResult removalResult rfl rfl
example : removalResult.terminal = .noRepetition ∨
    removalResult.terminal = .removal ∨ removalResult.terminal = .separation :=
  CT8.outcome_exhaustive removalCapability context removalInput removalResult

def contractNodeIds := CT8.nodeAutomationContracts.map (·.nodeId)
def capabilityDefinitionRefs :=
  CT8.capabilityContract.requiredDefinitions.map (·.ref)
def authorInputRefs := CT8.nodeAutomationContracts.flatMap fun contract =>
  contract.authorInputs.map (·.ref)
example : contractNodeIds = ["CT8.entry", "CT8.search.orderedRepeatedType",
    "CT8.compare.responses"] := by native_decide
example : (CT8.nodeAutomationContracts.all fun contract =>
    !contract.generatedOutputs.isEmpty && contract.manualObligations.isEmpty) = true :=
  by native_decide
example : (authorInputRefs.all capabilityDefinitionRefs.contains) = true :=
  by native_decide

end StructuralExhaustion.Examples.CT8AutomationFirst
