import StructuralExhaustion.CT9.Automation

namespace StructuralExhaustion.Examples.CT9AutomationFirst

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

def items : Core.OrderedCollection Nat where
  values := [0, 1, 2]
  nodup := by decide
  decEq := inferInstance

abbrev overloadedCapability : CT9.Capability problem where
  Item := Nat
  Label := Bool
  labels := bools
  label := fun item => item == 0
  capacity := fun _ => 1

def overloadedInput : CT9.Input overloadedCapability := ⟨context, items⟩
def overloadedTrigger : CT9.Trigger overloadedCapability context := ⟨items⟩
def routedOverloadedInput : CT9.Input overloadedCapability :=
  CT9.Input.ofTrigger context overloadedTrigger
example : routedOverloadedInput.context = context := rfl
example : routedOverloadedInput.items = items := rfl
def overloadedResult := ct9_execute overloadedCapability on overloadedInput

theorem overloadedGlobalExcess :
    CT9.totalCapacity overloadedCapability <
      overloadedInput.items.values.length := by
  decide

theorem overloadedCapacityOne :
    ∀ label : overloadedCapability.Label,
      overloadedCapability.capacity label = 1 := by
  intro label
  rfl

def overloadedResidual :
    CT9.OverloadResidual overloadedCapability overloadedInput :=
  CT9.runOverloadResidualOfTotalCapacityLtCardinality
    overloadedCapability overloadedInput overloadedGlobalExcess

def overloadedPair :
    CT9.SameLabelPair overloadedCapability overloadedInput
      overloadedResidual.label :=
  CT9.runSameLabelPairOfTotalCapacityLtCardinality
    overloadedCapability overloadedInput overloadedGlobalExcess
    overloadedCapacityOne

def overloadedRun : CT9.OverloadedRun overloadedCapability overloadedInput :=
  CT9.runOverloadedOfTotalCapacityLtCardinality overloadedCapability
    overloadedInput overloadedGlobalExcess

example : overloadedResult.terminal = .overloaded := rfl
example : overloadedResult.trace = [.entry, .partition, .overload, .overloadedTerminal] := rfl
example : overloadedResult.terminal = .overloaded :=
  CT9.run_terminal_overloaded_of_totalCapacity_lt_cardinality
    overloadedCapability overloadedInput overloadedGlobalExcess
example : overloadedResult.trace =
    [.entry, .partition, .overload, .overloadedTerminal] :=
  CT9.run_trace_overloaded_of_totalCapacity_lt_cardinality
    overloadedCapability overloadedInput overloadedGlobalExcess
example : overloadedResidual.label = false := rfl
example : overloadedPair.first = 1 := rfl
example : overloadedPair.second = 2 := rfl
example : overloadedPair.first ≠ overloadedPair.second :=
  overloadedPair.distinct
example : overloadedRun.execution = overloadedResult := rfl
example : overloadedResidual = overloadedRun.residual := rfl
example : overloadedRun.execution.terminal = .overloaded :=
  overloadedRun.terminal_eq
example : overloadedRun.execution.trace =
    [.entry, .partition, .overload, .overloadedTerminal] :=
  overloadedRun.trace_eq
example : overloadedCapability.label overloadedPair.first =
    overloadedCapability.label overloadedPair.second :=
  overloadedPair.labels_eq
example : overloadedResult.outcome.Valid := by ct9 overloadedCapability on overloadedInput
example : ∃ result : CT9.ExecutionResult overloadedCapability overloadedInput,
    result.outcome.Valid ∧
      CT9.Graph.ValidTrace overloadedCapability overloadedInput result.trace := by
  ct9_total overloadedCapability on overloadedInput

abbrev boundedCapability : CT9.Capability problem where
  Item := Nat
  Label := Bool
  labels := bools
  label := fun item => item == 0
  capacity := fun _ => 3

def boundedInput : CT9.Input boundedCapability := ⟨context, items⟩
def boundedResult := ct9_execute boundedCapability on boundedInput

example : boundedResult.terminal = .bounded := rfl
example : boundedResult.trace = [.entry, .partition, .overload, .boundedTerminal] := rfl
example : boundedResult.outcome.Valid := CT9.run_verified boundedCapability boundedInput
example : boundedResult = boundedResult :=
  CT9.run_deterministic boundedCapability boundedInput
    boundedResult boundedResult rfl rfl
example : boundedResult.terminal = .overloaded ∨
    boundedResult.terminal = .bounded :=
  CT9.outcome_exhaustive boundedCapability boundedInput boundedResult

abbrev parityCapability : CT9.Capability problem :=
  CT9.parityCapacityOne problem Nat (fun value => value)

def parityInput : CT9.Input parityCapability := ⟨context, items⟩

def parityRun : CT9.ParityCapacityOneRun (fun value : Nat => value)
    parityInput :=
  CT9.runParityCapacityOneOfThreeLeCardinality (fun value : Nat => value)
    parityInput (by decide)

example : CT9.totalCapacity parityCapability = 2 := by simp
example : parityRun.execution.terminal = .overloaded :=
  parityRun.terminal_eq
example : parityRun.pair.first = 0 := rfl
example : parityRun.pair.second = 2 := rfl
example : parityRun.pair.first ≠ parityRun.pair.second :=
  parityRun.pair.distinct
example : parityRun.pair.first % 2 = parityRun.pair.second % 2 :=
  parityRun.pair.same_parity

def contractNodeIds := CT9.nodeAutomationContracts.map (·.nodeId)
def capabilityDefinitionRefs :=
  CT9.capabilityContract.requiredDefinitions.map (·.ref)
def authorInputRefs := CT9.nodeAutomationContracts.flatMap fun contract =>
  contract.authorInputs.map (·.ref)
example : contractNodeIds = ["CT9.entry", "CT9.compute.partition",
    "CT9.search.firstOverload"] := by native_decide
example : (CT9.nodeAutomationContracts.all fun contract =>
    !contract.generatedOutputs.isEmpty && contract.manualObligations.isEmpty) = true :=
  by native_decide
example : (authorInputRefs.all capabilityDefinitionRefs.contains) = true :=
  by native_decide
example : CT9.capabilityContract.derivedOperations.contains
    "CT9.runParityCapacityOneOfThreeLeCardinality" = true := by native_decide

end StructuralExhaustion.Examples.CT9AutomationFirst
