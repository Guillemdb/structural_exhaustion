import StructuralExhaustion.CT17.Automation

namespace StructuralExhaustion.Examples.CT17AutomationFirst

open StructuralExhaustion

inductive Mode where
  | incompatible
  | exhausted
  | survivors
  | targetHit
  | orbit
  deriving DecidableEq

abbrev problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Mode

def context (mode : Mode) : Core.BranchContext problem :=
  ⟨(), trivial, mode⟩

@[implicit_reducible]
def bools : FinEnum Bool :=
  StructuralExhaustion.Core.Enumeration.bool

abbrev spec : CT17.Spec problem where
  Target := Bool
  Offset := Bool
  Position := fun _ => Bool
  Value := Nat
  targetValue := fun target => if target then 10 else 0
  blockValue := fun ctx {_scale} position offset =>
    match ctx.state with
    | .survivors =>
        if position then (if offset then 100 else 99) else 0
    | _ => 0
  orbitValue := fun ctx _scale offset =>
    match ctx.state with
    | .targetHit => 10
    | .orbit => if offset then 100 else 99
    | _ => 0
  Compatible := fun ctx _target _offset => ctx.state ≠ .incompatible

abbrev capability : CT17.Capability spec where
  targets := bools
  offsets := bools
  positions := fun _ => bools
  compatibleDecidable := fun _ _ _ => inferInstance
  valueDecidableEq := inferInstance
  finiteScaleLimit := 1

def incompatibleContext := context .incompatible
def incompatibleInput : CT17.Input spec capability incompatibleContext := ⟨0⟩
def incompatibleResult :=
  ct17_execute spec with capability at incompatibleContext on incompatibleInput

example : incompatibleResult.terminal = .incompatibility := by native_decide
example : incompatibleResult.trace =
    [.entry, .compatibility, .incompatibilityTerminal] := by native_decide
example : incompatibleResult.outcome.Valid :=
  CT17.run_verified spec capability incompatibleContext incompatibleInput

def exhaustedContext := context .exhausted
def exhaustedInput : CT17.Input spec capability exhaustedContext := ⟨0⟩
def exhaustedResult :=
  ct17_execute spec with capability at exhaustedContext on exhaustedInput

example : exhaustedResult.terminal = .exhausted := by native_decide
example : exhaustedResult.trace =
    [.entry, .compatibility, .scale, .survivors, .exhaustedTerminal] :=
  by native_decide
example : CT17.survivorList spec capability exhaustedContext exhaustedInput = [] :=
  by native_decide
example : exhaustedResult.outcome.Valid := by
  ct17 spec with capability at exhaustedContext on exhaustedInput
example : ∃ result :
    CT17.ExecutionResult spec capability exhaustedContext exhaustedInput,
    result.outcome.Valid ∧
      @CT17.Graph.ValidTrace problem spec capability exhaustedContext
        exhaustedInput result.trace := by
  ct17_total spec with capability at exhaustedContext on exhaustedInput

def survivorContext := context .survivors
def survivorInput : CT17.Input spec capability survivorContext := ⟨0⟩
example : (capability.tacticInterface).Trigger survivorContext := survivorInput
def survivorResult :=
  ct17_execute spec with capability at survivorContext on survivorInput

example : survivorResult.terminal = .survivors := by native_decide
example : survivorResult.trace =
    [.entry, .compatibility, .scale, .survivors, .survivorTerminal] :=
  by native_decide
example : CT17.survivorList spec capability survivorContext survivorInput = [true] :=
  by native_decide
example : survivorResult.outcome.Valid :=
  CT17.run_verified spec capability survivorContext survivorInput

def targetHitContext := context .targetHit
def targetHitInput : CT17.Input spec capability targetHitContext := ⟨2⟩
def targetHitResult :=
  ct17_execute spec with capability at targetHitContext on targetHitInput

example : targetHitResult.terminal = .targetHit := by native_decide
example : targetHitResult.trace =
    [.entry, .compatibility, .scale, .arithmetic, .targetHitTerminal] :=
  by native_decide
example : targetHitResult.outcome.Valid :=
  CT17.run_verified spec capability targetHitContext targetHitInput

def orbitContext := context .orbit
def orbitInput : CT17.Input spec capability orbitContext := ⟨2⟩
def orbitResult :=
  ct17_execute spec with capability at orbitContext on orbitInput

example : orbitResult.terminal = .orbit := by native_decide
example : orbitResult.trace =
    [.entry, .compatibility, .scale, .arithmetic, .orbitTerminal] :=
  by native_decide
example : capability.offsets.orderedValues.map
    (spec.orbitValue orbitContext orbitInput.scale) = [99, 100] := by
  native_decide
example : orbitResult.outcome.Valid :=
  CT17.run_verified spec capability orbitContext orbitInput
example : @CT17.Graph.ValidTrace problem spec capability orbitContext orbitInput
    orbitResult.trace :=
  CT17.run_trace_valid spec capability orbitContext orbitInput
example : orbitResult = orbitResult :=
  CT17.run_deterministic spec capability orbitContext orbitInput
    orbitResult orbitResult rfl rfl
example :
    orbitResult.terminal = .incompatibility ∨
    orbitResult.terminal = .exhausted ∨
    orbitResult.terminal = .survivors ∨
    orbitResult.terminal = .targetHit ∨
    orbitResult.terminal = .orbit :=
  CT17.run_exhaustive spec capability orbitContext orbitInput

def contractNodeIds := CT17.nodeAutomationContracts.map (·.nodeId)
def capabilityDefinitionRefs :=
  CT17.capabilityContract.requiredDefinitions.map (·.ref)
def authorInputRefs := CT17.nodeAutomationContracts.flatMap fun contract =>
  contract.authorInputs.map (·.ref)
example : contractNodeIds = ["CT17.entry", "CT17.search.compatibility",
    "CT17.decide.scale", "CT17.enumerate.survivors",
    "CT17.decide.arithmetic"] := by native_decide
example : (CT17.nodeAutomationContracts.all fun contract =>
    !contract.generatedOutputs.isEmpty && contract.manualObligations.isEmpty) = true :=
  by native_decide
example : (authorInputRefs.all capabilityDefinitionRefs.contains) = true :=
  by native_decide

end StructuralExhaustion.Examples.CT17AutomationFirst
