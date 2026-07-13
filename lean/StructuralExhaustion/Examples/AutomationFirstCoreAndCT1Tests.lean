import StructuralExhaustion.Core.AutomationFirst
import StructuralExhaustion.CT1.Automation
import StructuralExhaustion.CT1.TargetEncoding

namespace StructuralExhaustion.Examples.AutomationFirstCoreAndCT1Tests

open StructuralExhaustion
open Core.FiniteSearch

/-! ## Exact finite enumerators and ordinary search -/

@[implicit_reducible]
def bools : FinEnum Bool :=
  StructuralExhaustion.Core.Enumeration.bool

@[implicit_reducible]
def reversedBools : FinEnum Bool :=
  @FinEnum.ofNodupList Bool inferInstance [true, false]
    (by intro value; cases value <;> simp) (by decide)

@[implicit_reducible]
def units : FinEnum Unit :=
  StructuralExhaustion.Core.Enumeration.unit

@[implicit_reducible]
def empty : FinEnum Empty :=
  Core.Enumeration.empty

def eqTrueDecisionA (value : Bool) : Decidable (value = true) :=
  Bool.decEq value true

def eqTrueDecisionB (value : Bool) : Decidable (value = true) :=
  match value with
  | false => .isFalse (by simp)
  | true => .isTrue rfl

def ordinaryHit : Result (fun value : Bool => value = true) :=
  search bools (fun value => value = true) eqTrueDecisionA

theorem ordinary_hit_value : ordinaryHit.value? = some true := rfl

theorem ordinary_hit_sound : true = true :=
  search_sound bools (fun value => value = true) eqTrueDecisionA
    ordinary_hit_value

theorem ordinary_hit_complete :
    ∃ value,
      ordinaryHit.value? = some value ∧ value = true :=
  search_complete bools (fun value => value = true) eqTrueDecisionA
    ⟨true, rfl⟩

theorem ordinary_execution_deterministic
    (left right : Result (fun value : Bool => value = true))
    (leftRun : left = ordinaryHit) (rightRun : right = ordinaryHit) :
    left = right :=
  search_deterministic bools (fun value => value = true) eqTrueDecisionA
    left right leftRun rightRun

def ordinaryAbsent : Result (fun _ : Bool => False) :=
  search bools (fun _ => False) (fun _ => inferInstance)

theorem ordinary_absent_value : ordinaryAbsent.value? = none := rfl

theorem ordinary_absent_complete : ∀ _ : Bool, ¬ False :=
  (search_none_iff bools (fun _ => False) (fun _ => inferInstance)).mp
    ordinary_absent_value

/-! ## Ordered first-hit search and determinism -/

def firstTrue : FirstResult bools.orderedValues (fun value : Bool => value = true) :=
  first bools (fun value => value = true) eqTrueDecisionA

def reversedFirstTrue :
    FirstResult reversedBools.orderedValues (fun value : Bool => value = true) :=
  first reversedBools (fun value => value = true) eqTrueDecisionA

theorem first_true_value : firstTrue.value? = some true := rfl
theorem first_true_prefix : firstTrue.before? = some [false] := rfl
theorem reversed_first_true_value : reversedFirstTrue.value? = some true := rfl
theorem reversed_first_true_prefix : reversedFirstTrue.before? = some [] := rfl

/-- The chosen first value does not depend on which correct decision procedure
implements the predicate. -/
theorem first_decider_independent :
    (first bools (fun value => value = true) eqTrueDecisionA).value? =
      (first bools (fun value => value = true) eqTrueDecisionB).value? :=
  first_value_independent bools.orderedValues (fun value => value = true)
    eqTrueDecisionA eqTrueDecisionB

/-- Every first-hit certificate proves absence on the exact prefix that
precedes its witness. -/
theorem every_first_hit_has_clean_prefix
    (hit : FirstHit bools.orderedValues (fun value : Bool => value = true)) :
    ∀ candidate, candidate ∈ hit.before → candidate ≠ true :=
  first_hit_no_earlier hit

theorem first_execution_relationally_deterministic
    (left right : FirstResult bools.orderedValues (fun value : Bool => value = true))
    (leftRun : left = firstTrue) (rightRun : right = firstTrue) :
    left = right :=
  first_deterministic bools.orderedValues (fun value => value = true)
    eqTrueDecisionA left right leftRun rightRun

/-! ## Dependent finite search -/

def DepWitness : Bool → Type
  | false => Empty
  | true => Bool

@[implicit_reducible]
def dependentFibres (index : Bool) : FinEnum (DepWitness index) :=
  match index with
  | false => empty
  | true => bools

def dependentPresentation : Core.DependentEnumeration Bool DepWitness where
  indices := bools
  fibres := dependentFibres

def dependentPredicate : (index : Bool) → DepWitness index → Prop
  | false, witness => nomatch witness
  | true, witness => witness = true

def dependentDecision :
    (index : Bool) → (witness : DepWitness index) →
      Decidable (dependentPredicate index witness)
  | false, witness => nomatch witness
  | true, witness => Bool.decEq witness true

def dependentHit : DependentResult dependentPredicate :=
  dependentSearch dependentPresentation dependentPredicate dependentDecision

theorem dependent_hit_index : dependentHit.index? = some true := rfl

theorem dependent_hit_sound :
    match dependentHit with
    | .found index witness _ => dependentPredicate index witness
    | .absent _ => True :=
  dependentSearch_sound dependentPresentation dependentPredicate
    dependentDecision

theorem dependent_hit_complete :
    match dependentHit with
    | .found _ _ _ => True
    | .absent _ => False :=
  dependentSearch_complete dependentPresentation dependentPredicate
    dependentDecision ⟨true, true, rfl⟩

def dependentAbsent :
    DependentResult (fun (index : Bool) (_ : DepWitness index) => False) :=
  dependentSearch dependentPresentation
    (fun (index : Bool) (_ : DepWitness index) => False)
    (fun _ _ => inferInstance)

theorem dependent_absent_index : dependentAbsent.index? = none := rfl

theorem dependent_absence_is_exhaustive :
    match dependentAbsent with
    | .found _ _ _ => False
    | .absent _ =>
        ∀ (index : Bool), DepWitness index → ¬ (False : Prop) := by
  cases dependentAbsent with
  | found index witness holds => exact holds
  | absent noWitness => exact noWitness

theorem dependent_execution_deterministic
    (left right :
      DependentResult (fun (index : Bool) (_ : DepWitness index) => False))
    (leftRun : left = dependentAbsent) (rightRun : right = dependentAbsent) :
    left = right :=
  dependentSearch_deterministic dependentPresentation
    (fun (index : Bool) (_ : DepWitness index) => False)
    (fun _ _ => inferInstance) left right leftRun rightRun

/-! ## Automation-first CT1 -/

def problem : Core.Problem where
  Ambient := Bool
  Baseline := fun _ => True
  rank := fun value => if value then 1 else 0
  BranchState := fun _ => Unit

def hitInput : CT1.Input problem where
  context := {
    G := true
    baseline := trivial
    state := ()
  }

def avoidingInput : CT1.Input problem where
  context := {
    G := false
    baseline := trivial
    state := ()
  }

/-! The single-code adapter generates the whole CT1 machine surface. -/

def trueEncoding :
    CT1.TargetEncoding (P := problem) (fun G => G = true) where
  Code := fun _ => Unit
  codes := fun _ => Core.Enumeration.unit
  Accepts := fun G _ => G = true
  acceptsDecidable := fun G _ => Bool.decEq G true
  inputSize := fun _ => 0
  workCoefficient := 1
  workDegree := 0
  workBound := by intro G; cases G <;> native_decide
  encode := fun target => ⟨(), target⟩
  decode := fun accepts => accepts

def generatedHitRun :
    CT1.C1Run trueEncoding.spec trueEncoding.capability hitInput :=
  CT1.runC1OfPublicTarget trueEncoding.spec trueEncoding.capability
    trueEncoding.bridge hitInput rfl

theorem generated_hit_terminal : generatedHitRun.result.terminal = .c1 :=
  generatedHitRun.terminal_eq

theorem generated_hit_trace : generatedHitRun.result.trace =
    [.entry, .equivalenceCertification, .realizationDecision,
      .c1Terminal] :=
  generatedHitRun.trace_eq

def generatedAvoidingResult :=
  CT1.run trueEncoding.spec trueEncoding.capability avoidingInput

theorem generated_avoiding_terminal :
    generatedAvoidingResult.terminal = .avoiding :=
  rfl

def generatedPublicTargetDecision : Decidable ((false : Bool) = true) :=
  CT1.TargetBridge.publicTargetDecidable trueEncoding.bridge
    trueEncoding.capability false

def generatedPublicTargetExists : Bool :=
  @decide ((false : Bool) = true) generatedPublicTargetDecision

theorem generated_public_target_absent : ¬ ((false : Bool) = true) :=
  @of_decide_eq_false ((false : Bool) = true)
    generatedPublicTargetDecision (by native_decide)

def localTestSpec : CT1.Spec problem where
  TestIndex := Bool
  Witness := fun _ _ => Unit
  Realizes := fun G index _ => G = true ∧ index = true

def localTestCapability : CT1.Capability localTestSpec where
  tests := bools
  witnesses := fun _ _ => units
  realizesDecidable := by
    intro G index _
    change Decidable (G = true ∧ index = true)
    cases G with
    | false => exact .isFalse (by simp)
    | true =>
        cases index with
        | false => exact .isFalse (by simp)
        | true => exact .isTrue ⟨rfl, rfl⟩
  inputSize := fun _ => 0
  workCoefficient := 2
  workDegree := 0
  workBound := by intro G; cases G <;> native_decide

/-- CT1's target-test equivalence is definitional, not an instance theorem. -/
theorem target_is_definitionally_realization (G : problem.Ambient) :
    CT1.Target localTestSpec G ↔
      ∃ index, ∃ witness, localTestSpec.Realizes G index witness :=
  Iff.rfl

def hitResult : CT1.ExecutionResult localTestSpec hitInput :=
  CT1.run localTestSpec localTestCapability hitInput

def avoidingResult : CT1.ExecutionResult localTestSpec avoidingInput :=
  CT1.run localTestSpec localTestCapability avoidingInput

theorem hit_terminal : hitResult.terminal = .c1 := rfl

theorem hit_trace :
    hitResult.trace =
      [.entry, .equivalenceCertification, .realizationDecision,
        .c1Terminal] :=
  rfl

theorem hit_trace_valid :
    @CT1.Graph.ValidTrace problem localTestSpec hitInput hitResult.trace :=
  hitResult.traceValid

theorem hit_target : CT1.Target localTestSpec hitInput.context.G :=
  hitResult.verified

theorem avoiding_terminal : avoidingResult.terminal = .avoiding := rfl

theorem avoiding_trace :
    avoidingResult.trace =
      [.entry, .equivalenceCertification, .realizationDecision,
        .avoidingTerminal] :=
  rfl

theorem avoiding_trace_valid :
    @CT1.Graph.ValidTrace problem localTestSpec avoidingInput
      avoidingResult.trace :=
  avoidingResult.traceValid

/-- Extract the exhaustive negative certificate from an avoiding terminal. -/
theorem avoiding_outcome_no_realization
    (outcome : CT1.RawOutcome localTestSpec avoidingInput .avoiding) :
    ∀ index witness,
      ¬ localTestSpec.Realizes avoidingInput.context.G index witness := by
  cases outcome with
  | avoiding state => exact state.noRealization

theorem no_realization_derived_by_the_runner :
    ∀ index witness,
      ¬ localTestSpec.Realizes avoidingInput.context.G index witness := by
  apply avoiding_outcome_no_realization
  exact avoiding_terminal ▸ avoidingResult.outcome

/-- Target avoidance is derived solely from exhaustive realization absence. -/
theorem target_avoidance_derived_from_no_realization :
    ¬ CT1.Target localTestSpec avoidingInput.context.G := by
  intro target
  rcases target with ⟨index, witness, realizes⟩
  exact no_realization_derived_by_the_runner index witness realizes

/-- The semantic residual extends, rather than copies or changes, the exact
predecessor branch context. -/
theorem avoiding_context_preserves_predecessor
    {equivalence : CT1.EquivalenceState localTestSpec avoidingInput}
    (state : CT1.AvoidingState localTestSpec avoidingInput equivalence) :
    (state.toAvoidingContext.G = avoidingInput.context.G) ∧
      (state.toAvoidingContext.state = avoidingInput.context.state) ∧
      ¬ CT1.Target localTestSpec state.toAvoidingContext.G :=
  ⟨rfl, rfl, state.toAvoidingContext.avoids⟩

def PublicTarget (G : problem.Ambient) : Prop := G = true

def publicTargetBridge : CT1.TargetBridge localTestSpec PublicTarget where
  equivalent := by
    intro G
    constructor
    · intro publicTarget
      exact ⟨true, (), publicTarget, rfl⟩
    · intro target
      rcases target with ⟨index, witness, realizes⟩
      exact realizes.1

theorem hit_public_target : PublicTarget hitInput.context.G :=
  publicTargetBridge.publicTarget_of_target hit_target

theorem c1_certificate_closes_public_target
    {equivalence : CT1.EquivalenceState localTestSpec hitInput}
    (certificate : CT1.C1Certificate localTestSpec hitInput equivalence) :
    PublicTarget hitInput.context.G :=
  publicTargetBridge.publicTarget_of_c1 certificate

theorem avoiding_public_target_excluded :
    ¬ PublicTarget avoidingInput.context.G :=
  publicTargetBridge.not_publicTarget_of_not_target
    target_avoidance_derived_from_no_realization

theorem avoiding_state_excludes_public_target
    {equivalence : CT1.EquivalenceState localTestSpec avoidingInput}
    (state : CT1.AvoidingState localTestSpec avoidingInput equivalence) :
    ¬ PublicTarget avoidingInput.context.G :=
  publicTargetBridge.not_publicTarget_of_avoiding state

theorem ct1_reference_deterministic
    (left right : CT1.ExecutionResult localTestSpec hitInput)
    (leftRun : CT1.run localTestSpec localTestCapability hitInput = left)
    (rightRun : CT1.run localTestSpec localTestCapability hitInput = right) :
    left = right :=
  CT1.run_deterministic localTestSpec localTestCapability hitInput
    left right leftRun rightRun

theorem ct1_total_from_capability_only :
    ∃ result : CT1.ExecutionResult localTestSpec avoidingInput,
      CT1.OutcomeClaim result.outcome ∧
        @CT1.Graph.ValidTrace problem localTestSpec avoidingInput result.trace :=
  CT1.run_total localTestSpec localTestCapability avoidingInput

/-! ## Mutation barriers for finite enumerators -/

/-- An inhabited exact universe cannot be mutated to an empty enumeration:
the completeness field immediately yields a contradiction. -/
theorem empty_bool_enumeration_is_unconstructible
    (enumeration : FinEnum Bool)
    (mutated : enumeration.orderedValues = []) : False := by
  have member := enumeration.mem_orderedValues false
  rw [mutated] at member
  simp at member

/-- A `FinEnum` cannot be mutated to contain duplicates: its
`Nodup` certificate rejects the malformed enumeration. -/
theorem duplicate_bool_enumeration_is_unconstructible
    (enumeration : FinEnum Bool)
    (mutated : enumeration.orderedValues = [false, false, true]) : False := by
  have nodup := enumeration.nodup_orderedValues
  rw [mutated] at nodup
  simp at nodup

/-- The same completeness barrier applies to a nonempty dependent witness
fibre. -/
theorem empty_unit_fibre_is_unconstructible
    (enumeration : FinEnum Unit)
    (mutated : enumeration.orderedValues = []) : False := by
  have member := enumeration.mem_orderedValues ()
  rw [mutated] at member
  simp at member

end StructuralExhaustion.Examples.AutomationFirstCoreAndCT1Tests
