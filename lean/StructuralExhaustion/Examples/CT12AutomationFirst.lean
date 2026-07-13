import StructuralExhaustion.CT12.Automation

namespace StructuralExhaustion.Examples.CT12AutomationFirst

open StructuralExhaustion

abbrev problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit
def context : Core.BranchContext problem := ⟨(), trivial, ()⟩

abbrev demandCapability : CT12.Capability problem where
  State := fun _ => Unit
  DemandResidual := Unit
  TierResidual := Unit
  Peeled := fun _ => Unit
  peel := fun _ => ()
  restorations := fun {_n} {_state} _ => ⟨.demand (), []⟩

def demandInput : CT12.Input demandCapability := ⟨context, 2, ()⟩
def demandTrigger : CT12.Trigger demandCapability context := ⟨2, ()⟩
def routedDemandInput : CT12.Input demandCapability :=
  CT12.Input.ofTrigger context demandTrigger
example : routedDemandInput.context = context := rfl
example : routedDemandInput.load = 2 := rfl
def demandResult := ct12_execute demandCapability on demandInput
example : demandResult.terminal = .demand := by native_decide
example : demandResult.trace =
    [.entry, .saturation, .peel, .restoration, .demandTerminal] := by native_decide
example : demandResult.outcome.Valid := by ct12 demandCapability on demandInput
example : ∃ result : CT12.ExecutionResult demandCapability demandInput,
    result.outcome.Valid ∧ CT12.Graph.ValidTrace demandCapability result.trace ∧
      result.iterations ≤ demandInput.load ∧
      result.trace.length ≤ 4 * demandInput.load + 3 := by
  ct12_total demandCapability on demandInput

abbrev tierCapability : CT12.Capability problem where
  State := fun _ => Unit
  DemandResidual := Unit
  TierResidual := Bool
  Peeled := fun _ => Unit
  peel := fun _ => ()
  restorations := fun {_n} {_state} _ => ⟨.tier true, []⟩

def tierInput : CT12.Input tierCapability := ⟨context, 1, ()⟩
def tierResult := ct12_execute tierCapability on tierInput
example : tierResult.terminal = .tier := by native_decide
example : tierResult.trace =
    [.entry, .saturation, .peel, .restoration, .tierTerminal] := by native_decide
example : tierResult.outcome.Valid := CT12.run_verified tierCapability tierInput

abbrev countdownCapability : CT12.Capability problem where
  State := fun _ => Unit
  DemandResidual := Unit
  TierResidual := Unit
  Peeled := fun _ => Unit
  peel := fun _ => ()
  restorations := fun {n} {_state} _ =>
    ⟨.continue n () (Nat.lt_succ_self n), []⟩

def zeroInput : CT12.Input countdownCapability := ⟨context, 0, ()⟩
def zeroResult := ct12_execute countdownCapability on zeroInput
example : zeroResult.terminal = .exhausted := by native_decide
example : zeroResult.trace = [.entry, .saturation, .exhaustedTerminal] := by native_decide

def countdownInput : CT12.Input countdownCapability := ⟨context, 3, ()⟩
def countdownResult := ct12_execute countdownCapability on countdownInput
example : countdownResult.terminal = .exhausted := by native_decide
example : countdownResult.iterations = 3 := by native_decide
example : countdownResult.iterations ≤ countdownInput.load :=
  CT12.run_iterations_bounded countdownCapability countdownInput
example : countdownResult.trace.length ≤ 4 * countdownInput.load + 3 :=
  CT12.run_trace_bounded countdownCapability countdownInput
example : CT12.Graph.ValidTrace countdownCapability countdownResult.trace :=
  CT12.run_trace_valid countdownCapability countdownInput
example : countdownResult = countdownResult :=
  CT12.run_deterministic countdownCapability
    countdownResult countdownResult rfl rfl
example : countdownResult.terminal = .exhausted ∨
    countdownResult.terminal = .demand ∨ countdownResult.terminal = .tier :=
  CT12.outcome_exhaustive countdownCapability countdownResult

def contractNodeIds := CT12.nodeAutomationContracts.map (·.nodeId)
def capabilityDefinitionRefs :=
  CT12.capabilityContract.requiredDefinitions.map (·.ref)
def authorInputRefs := CT12.nodeAutomationContracts.flatMap fun contract =>
  contract.authorInputs.map (·.ref)
example : contractNodeIds = ["CT12.entry", "CT12.decide.saturation",
    "CT12.compute.peel", "CT12.compute.restoration", "CT12.verify.decrease"] :=
  by native_decide
example : (CT12.nodeAutomationContracts.all fun contract =>
    !contract.generatedOutputs.isEmpty && contract.manualObligations.isEmpty) = true :=
  by native_decide
example : (authorInputRefs.all capabilityDefinitionRefs.contains) = true :=
  by native_decide

end StructuralExhaustion.Examples.CT12AutomationFirst
