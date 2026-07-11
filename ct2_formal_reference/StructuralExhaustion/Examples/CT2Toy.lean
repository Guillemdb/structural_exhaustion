import StructuralExhaustion.CT2.Automation
import StructuralExhaustion.Examples.CT3Toy
import StructuralExhaustion.Examples.CT6CT10Interfaces

namespace StructuralExhaustion.Examples.CT2Toy

open StructuralExhaustion.CT2

/-! ## Survivor examples -/

/-- A consistent model in which deletion and smaller replacement are
impossible, leaving the final survivor classifier to select CT10 or CT3. -/
def framework : Framework where
  Ambient := Unit
  Piece := Unit
  Interface := Unit
  Outside := Unit
  Rank := Unit
  rank := fun _ => ()
  smaller := fun _ _ => False
  Baseline := fun _ => True
  Target := fun _ => False
  Proper := fun _ _ => True
  Admissible := fun _ _ => True
  interface := fun _ => ()
  InterfaceBounded := fun _ => True
  Compatible := fun _ _ => True
  Response := fun _ _ => True
  delete := fun _ _ => ()
  replace := fun _ _ _ => ()
  ReplacementAllowed := fun _ _ _ => True
  CriticalityDatum := fun _ _ => Unit
  MissingResponseDatum := fun _ _ => Unit
  ct3 := CT3Toy.framework
  ct10 := CT6CT10Fixtures.ct10Entry
  ContextCT3Aligned := fun _ _ _ _ _ => True
  ResponseCT3Aligned := fun _ _ _ _ => True
  CriticalityCT10Aligned := fun _ _ _ _ => True

private theorem unitCounterexample : Counterexample framework () :=
  ⟨trivial, fun impossible => impossible⟩

def input : Input framework where
  G := ()
  X := ()
  minimal := {
    counterexample := unitCounterexample
    excludesSmaller := by
      intro _ impossible
      exact False.elim impossible
  }
  proper := trivial
  admissible := trivial

def port : Port framework input where
  ct3Accepts := fun _ => True
  ct10Accepts := fun _ => True

def handoff : HandoffPlan framework input port where
  acceptCT3 := fun _ => trivial
  acceptCT10 := fun _ => trivial

private theorem noDeletion : DeletionWitness framework input → False :=
  fun witness => witness.smaller

private theorem noCandidate :
    SmallerReplacementCandidate framework input → False :=
  fun candidate => candidate.smaller

private def criticalState (bounded : BoundedState framework input) :
    DeletionCriticalState framework input :=
  { bounded := bounded, critical := noDeletion }

private def survivorState (critical : DeletionCriticalState framework input) :
    SurvivorState framework input :=
  { deletionCritical := critical, targetUncompressible := noCandidate }

def criticalityPlan : CorePlan framework input where
  interface := { decide := .bounded ⟨trivial⟩ }
  deletion := { decide := fun bounded => .critical (criticalState bounded) }
  replacementCandidate := {
    search := fun critical => .absent (survivorState critical)
  }
  context := {
    certify := fun state => False.elim (noCandidate state.candidate)
  }
  survivor := {
    classify := fun _ => .criticality {
      datum := ()
      downstream := CT6CT10Fixtures.ct10Input
      aligned := trivial
    }
  }

def responsePlan : CorePlan framework input where
  interface := { decide := .bounded ⟨trivial⟩ }
  deletion := { decide := fun bounded => .critical (criticalState bounded) }
  replacementCandidate := {
    search := fun critical => .absent (survivorState critical)
  }
  context := {
    certify := fun state => False.elim (noCandidate state.candidate)
  }
  survivor := {
    classify := fun _ => .missingResponse {
      datum := ()
      downstream := CT3Toy.input
      aligned := trivial
    }
  }

def criticalityResult : ExecutionResult framework input port :=
  ct2_execute input using criticalityPlan with port via handoff

def responseResult : ExecutionResult framework input port :=
  ct2_execute input using responsePlan with port via handoff

theorem criticality_terminal :
    criticalityResult.terminal = .criticalityCT10 := rfl

theorem criticality_trace :
    criticalityResult.trace =
      [.entry, .interfaceDecision, .deletionDecision,
        .replacementCandidateSearch, .survivorClassification,
        .criticalityCT10Terminal] := rfl

theorem response_terminal : responseResult.terminal = .responseCT3 := rfl

theorem response_trace :
    responseResult.trace =
      [.entry, .interfaceDecision, .deletionDecision,
        .replacementCandidateSearch, .survivorClassification,
        .responseCT3Terminal] := rfl

/-- Exact CT3 input extracted from the executed response-defect terminal. -/
def responseDownstreamInput : CT3.Input CT3Toy.framework :=
  match responseResult.outcome with
  | .responseCT3 payload _ =>
      CT3Payload.toInput (.missingResponse payload)

theorem response_adapter_exact : responseDownstreamInput = CT3Toy.input := rfl

def responseDownstreamResult :
    CT3.ExecutionResult CT3Toy.framework responseDownstreamInput CT3Toy.port :=
  CT3.runTraced CT3Toy.framework responseDownstreamInput CT3Toy.ct8Plan
    CT3Toy.port CT3Toy.handoff

theorem response_downstream_terminal :
    responseDownstreamResult.terminal = .ct8 := rfl

example : OutcomeClaim criticalityResult.outcome := by
  ct2 input using criticalityPlan with port via handoff

example : ∃ result : ExecutionResult framework input port,
    OutcomeClaim result.outcome ∧
      @Graph.ValidTrace framework input result.trace := by
  ct2_total input using criticalityPlan with port via handoff

/-! ## Candidate-specific context residual -/

def contextFramework : Framework where
  Ambient := Bool
  Piece := Bool
  Interface := Unit
  Outside := Unit
  Rank := Nat
  rank := fun value => if value then 0 else 1
  smaller := fun first second => first < second
  Baseline := fun _ => True
  Target := fun value => value = true
  Proper := fun _ _ => True
  Admissible := fun _ _ => True
  interface := fun _ => ()
  InterfaceBounded := fun _ => True
  Compatible := fun _ _ => True
  Response := fun piece _ => piece = false
  delete := fun ambient _ => ambient
  replace := fun _ _ replacement => replacement
  ReplacementAllowed := fun _ _ _ => True
  CriticalityDatum := fun _ _ => Unit
  MissingResponseDatum := fun _ _ => Unit
  ct3 := CT3Toy.framework
  ct10 := CT6CT10Fixtures.ct10Entry
  ContextCT3Aligned := fun _ _ _ _ _ => True
  ResponseCT3Aligned := fun _ _ _ _ => True
  CriticalityCT10Aligned := fun _ _ _ _ => True

private theorem falseCounterexample :
    Counterexample contextFramework false := by
  constructor
  · trivial
  · intro equality
    cases equality

def contextInput : Input contextFramework where
  G := false
  X := false
  minimal := {
    counterexample := falseCounterexample
    excludesSmaller := by
      intro H smaller counterexample
      cases H with
      | false =>
          simp [contextFramework] at smaller
      | true =>
          exact counterexample.2 rfl
  }
  proper := trivial
  admissible := trivial

def contextPort : Port contextFramework contextInput where
  ct3Accepts := fun _ => True
  ct10Accepts := fun _ => True

def contextHandoff : HandoffPlan contextFramework contextInput contextPort where
  acceptCT3 := fun _ => trivial
  acceptCT10 := fun _ => trivial

private theorem contextNoDeletion :
    DeletionWitness contextFramework contextInput → False := by
  intro witness
  have impossible : (1 : Nat) < 1 := by
    simpa [contextFramework, contextInput] using witness.smaller
  exact (Nat.lt_irrefl 1) impossible

private def contextCandidate :
    SmallerReplacementCandidate contextFramework contextInput where
  replacement := true
  allowed := trivial
  sameInterface := rfl
  profileIncluded := by
    intro _ profile
    exact False.elim (Bool.noConfusion profile.2)
  smaller := Nat.zero_lt_succ 0

private theorem selectedCandidateIsTrue
    (candidate : SmallerReplacementCandidate contextFramework contextInput) :
    candidate.replacement = true := by
  cases equality : candidate.replacement with
  | false =>
      have impossible : (1 : Nat) < 1 := by
        simpa [contextFramework, contextInput, equality] using candidate.smaller
      exact False.elim ((Nat.lt_irrefl 1) impossible)
  | true => exact rfl

private def contextPayload
    (state : CandidateState contextFramework contextInput) :
    ContextCT3Payload contextFramework contextInput state where
  residual := {
    outside := ()
    compatible := trivial
    sourceResponds := rfl
    replacementMissingResponse := by
      intro response
      change state.candidate.replacement = false at response
      rw [selectedCandidateIsTrue state.candidate] at response
      exact Bool.noConfusion response
  }
  downstream := CT3Toy.input
  aligned := trivial

def contextPlan : CorePlan contextFramework contextInput where
  interface := { decide := .bounded ⟨trivial⟩ }
  deletion := {
    decide := fun bounded => .critical {
      bounded := bounded
      critical := contextNoDeletion
    }
  }
  replacementCandidate := {
    search := fun critical => .found {
      deletionCritical := critical
      candidate := contextCandidate
    }
  }
  context := {
    certify := fun state => .residual (contextPayload state)
  }
  survivor := {
    classify := fun survivor =>
      False.elim (survivor.targetUncompressible contextCandidate)
  }

def contextResult : ExecutionResult contextFramework contextInput contextPort :=
  ct2_execute contextInput using contextPlan
    with contextPort via contextHandoff

theorem context_terminal : contextResult.terminal = .contextCT3 := rfl

theorem context_trace :
    contextResult.trace =
      [.entry, .interfaceDecision, .deletionDecision,
        .replacementCandidateSearch, .candidateContextCertification,
        .contextCT3Terminal] := rfl

/-! ## Scope exit -/

def scopeFramework : Framework where
  Ambient := Unit
  Piece := Unit
  Interface := Unit
  Outside := Unit
  Rank := Unit
  rank := fun _ => ()
  smaller := fun _ _ => False
  Baseline := fun _ => True
  Target := fun _ => False
  Proper := fun _ _ => True
  Admissible := fun _ _ => True
  interface := fun _ => ()
  InterfaceBounded := fun _ => False
  Compatible := fun _ _ => True
  Response := fun _ _ => True
  delete := fun _ _ => ()
  replace := fun _ _ _ => ()
  ReplacementAllowed := fun _ _ _ => True
  CriticalityDatum := fun _ _ => Unit
  MissingResponseDatum := fun _ _ => Unit
  ct3 := CT3Toy.framework
  ct10 := CT6CT10Fixtures.ct10Entry
  ContextCT3Aligned := fun _ _ _ _ _ => True
  ResponseCT3Aligned := fun _ _ _ _ => True
  CriticalityCT10Aligned := fun _ _ _ _ => True

def scopeInput : Input scopeFramework where
  G := ()
  X := ()
  minimal := {
    counterexample := ⟨trivial, fun impossible => impossible⟩
    excludesSmaller := by
      intro _ impossible
      exact False.elim impossible
  }
  proper := trivial
  admissible := trivial

def scopePort : Port scopeFramework scopeInput where
  ct3Accepts := fun _ => True
  ct10Accepts := fun _ => True

def scopeHandoff : HandoffPlan scopeFramework scopeInput scopePort where
  acceptCT3 := fun _ => trivial
  acceptCT10 := fun _ => trivial

def scopePlan : CorePlan scopeFramework scopeInput where
  interface := {
    decide := .scope { unbounded := fun impossible => impossible }
  }
  deletion := {
    decide := fun bounded => False.elim bounded.bounded
  }
  replacementCandidate := {
    search := fun critical => False.elim critical.bounded.bounded
  }
  context := {
    certify := fun state =>
      False.elim state.deletionCritical.bounded.bounded
  }
  survivor := {
    classify := fun state =>
      False.elim state.deletionCritical.bounded.bounded
  }

def scopeResult : ExecutionResult scopeFramework scopeInput scopePort :=
  ct2_execute scopeInput using scopePlan with scopePort via scopeHandoff

theorem scope_terminal : scopeResult.terminal = .scope := rfl

theorem scope_trace :
    scopeResult.trace = [.entry, .interfaceDecision, .scopeTerminal] := rfl

/-! ## The two provenance-safe C2 constructors -/

theorem deletionC2_from_witness {F : Framework} {entry : Input F}
    (witness : DeletionWitness F entry) : False :=
  (C2Certificate.ofDeletion witness).contradiction

theorem replacementC2_from_certificate {F : Framework} {entry : Input F}
    (state : CandidateState F entry)
    (certificate : CandidateContextCertificate F entry state) : False :=
  (C2Certificate.ofReplacement state certificate).contradiction

end StructuralExhaustion.Examples.CT2Toy
