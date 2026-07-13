import StructuralExhaustion.CT3.Automation

namespace StructuralExhaustion.Examples.CT3AutomationFirst

open StructuralExhaustion

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def branch : Core.BranchContext problem where
  G := ()
  baseline := trivial
  state := ()

inductive Piece where
  | source
  | same
  | zero
  | one
  deriving Repr, DecidableEq

/-- Two-bit exact response semantics. -/
def response : Piece → Bool → Bool
  | .source, false => true
  | .source, true => false
  | .same, false => true
  | .same, true => false
  | .zero, _ => false
  | .one, _ => true

@[implicit_reducible]
def boolPresentation : FinEnum Bool :=
  StructuralExhaustion.Core.Enumeration.bool

@[implicit_reducible]
def unitPresentation : FinEnum Unit :=
  StructuralExhaustion.Core.Enumeration.unit

/-- Both candidate identifiers are present; their replacement pieces are
chosen by the fixture. -/
@[implicit_reducible]
def candidatePresentation : FinEnum Bool :=
  boolPresentation

def spec (replacement : Bool → Piece) (representative : Piece)
    (stored : Bool → Bool) : CT3.Spec problem where
  Piece := Piece
  Context := Bool
  Candidate := Bool
  Row := Unit
  response := response
  candidatePiece := replacement
  Admissible := fun _ _ _ => True
  Smaller := fun _ _ _ => True
  rowPiece := fun _ => representative
  rowResponse := fun _ => stored

private theorem capabilityWorkBound :
    CT3.localCheckBound boolPresentation candidatePresentation
      unitPresentation ≤ 12 := by
  native_decide

def capability (replacement : Bool → Piece) (representative : Piece)
    (stored : Bool → Bool) :
    CT3.Capability (spec replacement representative stored) where
  contexts := boolPresentation
  candidates := candidatePresentation
  rows := unitPresentation
  admissibleDecidable := fun _ _ _ => .isTrue trivial
  smallerDecidable := fun _ _ _ => .isTrue trivial
  inputSize := fun _ => 0
  workCoefficient := 12
  workDegree := 0
  workBound := by
    intro _
    change CT3.localCheckBound boolPresentation candidatePresentation
      unitPresentation ≤ 12
    exact capabilityWorkBound

def input (replacement : Bool → Piece) (representative : Piece)
    (stored : Bool → Bool) :
    CT3.Input (spec replacement representative stored) where
  context := branch
  piece := .source

/-! The first valid compression candidate is selected. -/

def compressionReplacement : Bool → Piece := fun _ => .same
def compressionStored : Bool → Bool := response .source
def compressionSpec : CT3.Spec problem :=
  spec compressionReplacement .source compressionStored

def compressionCapability : CT3.Capability compressionSpec :=
  capability compressionReplacement .source compressionStored
def compressionInput : CT3.Input compressionSpec :=
  input compressionReplacement .source compressionStored
def compressionResult :=
  CT3.run compressionSpec compressionCapability compressionInput

theorem compression_terminal :
    compressionResult.terminal = .compression :=
  rfl

theorem compression_trace : compressionResult.trace =
    [.entry, .vectorComputation, .compressionSearch,
      .compressionTerminal] :=
  rfl

theorem compression_first_candidate :
    match compressionResult.outcome with
    | .compression certificate => certificate.candidate = false
    | _ => False :=
  rfl

theorem compression_first_has_clean_prefix :
    match compressionResult.outcome with
    | .compression certificate => certificate.hit.before = []
    | _ => False :=
  rfl

/-! A stored row defect returns the concrete first context mismatch. -/

def noncompressingReplacement : Bool → Piece
  | false => .zero
  | true => .one

def defectStored : Bool → Bool := response .source
def defectSpec : CT3.Spec problem :=
  spec noncompressingReplacement .zero defectStored

def defectCapability : CT3.Capability defectSpec :=
  capability noncompressingReplacement .zero defectStored
def defectInput : CT3.Input defectSpec :=
  input noncompressingReplacement .zero defectStored
def defectResult := CT3.run defectSpec defectCapability defectInput

theorem defect_terminal : defectResult.terminal = .distinguishing :=
  rfl

theorem defect_context :
    match defectResult.outcome with
    | .distinguishing residual => residual.context = false
    | _ => False :=
  rfl

theorem defect_trace : defectResult.trace =
    [.entry, .vectorComputation, .compressionSearch,
      .tableValidation, .distinguishingTerminal] :=
  rfl

/-! An exact row equal to the source is recognized. -/

def knownStored : Bool → Bool := response .source
def knownSpec : CT3.Spec problem :=
  spec noncompressingReplacement .source knownStored

def knownCapability : CT3.Capability knownSpec :=
  capability noncompressingReplacement .source knownStored
def knownInput : CT3.Input knownSpec :=
  input noncompressingReplacement .source knownStored
def knownVector := CT3.computeExactVector knownSpec knownInput
def knownCompression :=
  CT3.findCompression knownSpec knownCapability knownInput knownVector
def knownResult := CT3.run knownSpec knownCapability knownInput

theorem known_compression_absence :
    ∀ candidate, ¬ CT3.Compresses knownSpec knownInput candidate := by
  intro candidate
  cases candidate <;>
    simp [CT3.Compresses, CT3.SameResponse,
      knownSpec, knownInput, input, spec, noncompressingReplacement, response]

theorem known_terminal : knownResult.terminal = .knownRow :=
  rfl

theorem known_trace : knownResult.trace =
    [.entry, .vectorComputation, .compressionSearch,
      .tableValidation, .rowLookup, .knownRowTerminal] :=
  rfl

/-! A valid table that lacks the source vector returns a novel type. -/

def novelStored : Bool → Bool := response .zero
def novelSpec : CT3.Spec problem :=
  spec noncompressingReplacement .zero novelStored

def novelCapability : CT3.Capability novelSpec :=
  capability noncompressingReplacement .zero novelStored
def novelInput : CT3.Input novelSpec :=
  input noncompressingReplacement .zero novelStored
def novelResult := CT3.run novelSpec novelCapability novelInput

theorem novel_terminal : novelResult.terminal = .novelRow :=
  rfl

theorem novel_absent_from_every_row :
    match novelResult.outcome with
    | .novelRow _residual =>
        ∀ row, ¬ CT3.RowMatches novelSpec novelInput row
    | _ => False := by
  exact novelResult.outcome.verified

theorem novel_trace : novelResult.trace =
    [.entry, .vectorComputation, .compressionSearch,
      .tableValidation, .rowLookup, .novelRowTerminal] :=
  rfl

/-! Compact codes are usable only through exact-vector refinement. -/

def compactRefinement :
    CT3.CompactCodeRefinement compressionSpec (Bool × Bool) where
  encode := fun piece =>
    (response piece false, response piece true)
  decode := fun code context => match context with
    | false => code.1
    | true => code.2
  refines := by
    intro piece context
    cases piece <;> cases context <;> rfl

theorem compact_equal_codes_are_exact
    {left right : Piece}
    (sameCode : compactRefinement.encode left =
      compactRefinement.encode right) :
    CT3.SameResponse compressionSpec left right :=
  compactRefinement.sameCode_sameResponse sameCode

/-! Public tactic surface and trace/soundness checks. -/

example : CT3.OutcomeClaim compressionResult.outcome := by
  ct3 compressionInput using compressionCapability

example : ∃ result : CT3.ExecutionResult
    novelSpec novelCapability novelInput,
    CT3.OutcomeClaim result.outcome ∧
      @CT3.Graph.ValidTrace problem novelSpec novelCapability
        novelInput result.trace := by
  ct3_total novelInput using novelCapability

example : @CT3.Graph.ValidTrace problem defectSpec defectCapability
    defectInput defectResult.trace :=
  defectResult.traceValid

end StructuralExhaustion.Examples.CT3AutomationFirst
