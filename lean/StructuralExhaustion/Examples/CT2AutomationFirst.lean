import StructuralExhaustion.CT2.Automation

namespace StructuralExhaustion.Examples.CT2AutomationFirst

open StructuralExhaustion

/-! Closed executable fixtures for the separating and criticality paths. -/

inductive Object where
  | small
  | large
  deriving DecidableEq

def rank : Object → Nat
  | .small => 0
  | .large => 1

abbrev problem : Core.Problem where
  Ambient := Object
  Baseline := fun _ => True
  rank := rank
  BranchState := fun _ => Unit

def target : Object → Prop
  | .small => True
  | .large => False

def context : Core.MinimalCounterexampleContext problem target where
  toAvoidingContext := {
    toBranchContext := {
      G := .large
      baseline := trivial
      state := ()
    }
    avoids := by simp [target]
  }
  minimal := by
    intro value smaller baseline
    cases value with
    | small => trivial
    | large => simp [rank] at smaller

@[implicit_reducible]
def units : FinEnum Unit :=
  StructuralExhaustion.Core.Enumeration.unit

@[implicit_reducible]
def bools : FinEnum Bool :=
  StructuralExhaustion.Core.Enumeration.bool

inductive ToyPiece : Object → Type
  | large : ToyPiece .large

def toyPieceEq {G : Object} : DecidableEq (ToyPiece G)
  | .large, .large => .isTrue rfl

@[implicit_reducible]
def toyPieces : (G : Object) → FinEnum (ToyPiece G)
  | .small => @FinEnum.ofNodupList (ToyPiece .small) toyPieceEq []
      (by intro piece; nomatch piece) (by simp)
  | .large => @FinEnum.ofNodupList (ToyPiece .large) toyPieceEq [.large]
      (by intro piece; cases piece; simp) (by simp)

abbrev pieces : CT2.PieceSystem problem where
  Piece := ToyPiece
  pieces := toyPieces
  Proper := fun _ => True
  Admissible := fun _ _ => True
  properDecidable := fun _ => inferInstance
  admissibleDecidable := fun _ _ => inferInstance

abbrev interfaces : CT2.InterfaceSystem pieces where
  Interface := Unit
  interface := fun _ => ()

abbrev contexts : CT2.ContextSystem interfaces where
  AbstractPiece := fun _ => Object
  Context := fun _ => Bool
  contexts := fun _ => bools
  glue := fun _ value => value
  abstract := fun piece => match piece with | .large => .large
  currentContext := fun _ => false
  reconstruct := fun piece => by cases piece; rfl

abbrev observable : CT2.Observable problem target where
  baselineDecidable := fun _ => .isTrue trivial
  targetDecidable := fun value => match value with
    | .small => .isTrue trivial
    | .large => .isFalse id

abbrev reductions : CT2.ReductionOps pieces where
  delete := fun piece => match piece with
    | .large => {
        value := .small
        decreases := by simp [rank]
      }

abbrev boolReplacements : CT2.ReplacementSystem contexts where
  Candidate := fun _ => Bool
  candidates := fun _ => bools
  replacement := fun piece _ => match piece with
    | .large => Object.small
  decreases := fun piece candidate => by
    cases piece
    simp [rank]

abbrev separatingCapability : CT2.Capability problem target where
  pieces := pieces
  interfaces := interfaces
  contexts := contexts
  observable := observable
  reductions := reductions
  replacements := boolReplacements

def separatingInput : CT2.Input separatingCapability context where
  seed := {
    piece := .large
    proper := trivial
    admissible := trivial
  }

def discoveryTag : Nat :=
  match CT2.Capability.discover separatingCapability context with
  | .enabled _ => 1
  | .disabled _ => 0

example : discoveryTag = 1 := rfl

def separatingResult :=
  ct2_execute separatingCapability at context on separatingInput

example : separatingResult.terminal = .separating := rfl

example : separatingResult.trace = [
    .entry, .deletionDecision, .replacementAnalysis, .separatingTerminal] := rfl

example : separatingResult.outcome.Valid := by
  ct2 separatingCapability at context on separatingInput

example : separatingResult = separatingResult :=
  CT2.run_deterministic separatingCapability context separatingInput
    separatingResult separatingResult rfl rfl

inductive NoCandidate

def noCandidateEq : DecidableEq NoCandidate := fun value => nomatch value

@[implicit_reducible]
def noCandidates : FinEnum NoCandidate :=
  @FinEnum.ofNodupList NoCandidate noCandidateEq []
    (by intro value; nomatch value) (by simp)

abbrev emptyReplacements : CT2.ReplacementSystem contexts where
  Candidate := fun _ => NoCandidate
  candidates := fun _ => noCandidates
  replacement := fun _ candidate => nomatch candidate
  decreases := fun _ candidate => nomatch candidate

abbrev criticalityCapability : CT2.Capability problem target where
  pieces := pieces
  interfaces := interfaces
  contexts := contexts
  observable := observable
  reductions := reductions
  replacements := emptyReplacements

def criticalityInput : CT2.Input criticalityCapability context where
  seed := {
    piece := .large
    proper := trivial
    admissible := trivial
  }

def criticalityResult :=
  ct2_execute criticalityCapability at context on criticalityInput

example : criticalityResult.terminal = .criticality := rfl

example : criticalityResult.trace = [
    .entry, .deletionDecision, .replacementAnalysis, .criticalityTerminal] := rfl

example : criticalityResult.outcome.Valid :=
  CT2.run_verified criticalityCapability context criticalityInput

example : ∃ result : CT2.ExecutionResult criticalityCapability context criticalityInput,
    result.outcome.Valid ∧
    CT2.Graph.ValidTrace criticalityCapability context criticalityInput result.trace := by
  ct2_total criticalityCapability at context on criticalityInput

end StructuralExhaustion.Examples.CT2AutomationFirst
