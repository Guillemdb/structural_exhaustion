import StructuralExhaustion.CT1.Automation

namespace StructuralExhaustion.Examples.CT1AutomationFirst

open StructuralExhaustion

/-- A complete ordered enumeration used by both executable examples. -/
@[implicit_reducible]
def bools : FinEnum Bool :=
  StructuralExhaustion.Core.Enumeration.bool

@[implicit_reducible]
def units : FinEnum Unit :=
  StructuralExhaustion.Core.Enumeration.unit

def problem : Core.Problem where
  Ambient := Bool
  Baseline := fun _ => True
  rank := fun value => if value then 1 else 0
  BranchState := fun _ => Unit

def input : CT1.Input problem where
  context := {
    G := false
    baseline := trivial
    state := ()
  }

/-! ### Realization branch -/

def hitSpec : CT1.Spec problem where
  TestIndex := Bool
  Witness := fun _ _ => Unit
  Realizes := fun _ index _ => index = true

def hitCapability : CT1.Capability hitSpec where
  tests := bools
  witnesses := fun _ _ => units
  realizesDecidable := by
    intro _ index _
    change Decidable (index = true)
    exact Bool.decEq index true
  inputSize := fun _ => 0
  workCoefficient := 2
  workDegree := 0
  workBound := by intro G; cases G <;> native_decide

def hitResult : CT1.ExecutionResult hitSpec input :=
  ct1_execute input using hitCapability

def hitRun : CT1.ExecutionResult hitSpec input :=
  CT1.run hitSpec hitCapability input

theorem hitTargetPremise : CT1.Target hitSpec input.context.G :=
  ⟨true, (), rfl⟩

theorem hit_terminal : hitResult.terminal = .c1 := rfl

theorem hit_terminal_from_target : hitResult.terminal = .c1 :=
  CT1.run_terminal_c1_of_target hitSpec hitCapability input hitTargetPremise

theorem hit_trace :
    hitResult.trace =
      [.entry, .equivalenceCertification, .realizationDecision,
        .c1Terminal] :=
  rfl

theorem hit_trace_from_target :
    hitResult.trace =
      [.entry, .equivalenceCertification, .realizationDecision,
        .c1Terminal] :=
  CT1.run_trace_c1_of_target hitSpec hitCapability input hitTargetPremise

theorem hit_sound : CT1.OutcomeClaim hitResult.outcome := by
  ct1 input using hitCapability

theorem hit_target : CT1.Target hitSpec input.context.G :=
  hitResult.verified

example : Decidable (CT1.Target hitSpec input.context.G) :=
  CT1.targetDecidable hitSpec hitCapability input.context.G

/-! ### Exhaustive avoidance branch -/

def avoidingSpec : CT1.Spec problem where
  TestIndex := Bool
  Witness := fun _ _ => Unit
  Realizes := fun _ _ _ => False

def avoidingCapability : CT1.Capability avoidingSpec where
  tests := bools
  witnesses := fun _ _ => units
  realizesDecidable := by
    intro _ _ _
    change Decidable False
    exact .isFalse (fun falseProof => falseProof)
  inputSize := fun _ => 0
  workCoefficient := 2
  workDegree := 0
  workBound := by intro G; cases G <;> native_decide

def avoidingResult : CT1.ExecutionResult avoidingSpec input :=
  ct1_execute input using avoidingCapability

theorem avoiding_terminal : avoidingResult.terminal = .avoiding := rfl

theorem avoiding_trace :
    avoidingResult.trace =
      [.entry, .equivalenceCertification, .realizationDecision,
        .avoidingTerminal] :=
  rfl

theorem avoiding_sound : CT1.OutcomeClaim avoidingResult.outcome := by
  ct1 input using avoidingCapability

theorem avoids_target : ¬ CT1.Target avoidingSpec input.context.G :=
  avoidingResult.verified

example :
    ∃ result : CT1.ExecutionResult avoidingSpec input,
      CT1.OutcomeClaim result.outcome ∧
        @CT1.Graph.ValidTrace problem avoidingSpec input result.trace := by
  ct1_total input using avoidingCapability

theorem reference_deterministic
    (first second : CT1.ExecutionResult hitSpec input)
    (hFirst : CT1.run hitSpec hitCapability input = first)
    (hSecond : CT1.run hitSpec hitCapability input = second) :
    first = second :=
  CT1.run_deterministic hitSpec hitCapability input first second hFirst hSecond

end StructuralExhaustion.Examples.CT1AutomationFirst
