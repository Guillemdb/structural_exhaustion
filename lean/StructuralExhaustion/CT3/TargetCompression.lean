import StructuralExhaustion.CT3.Theorems

namespace StructuralExhaustion.CT3

universe uAmbient uBranch uPiece uCompatible uCoordinate uCandidate uRow

/-!
# Certified local-coordinate target compression

The contract exposes the finite coordinates used by a structural proof.  A
compatible ambient context is classified into one coordinate, and the author
proves once that the coordinate response is exactly the target response after
gluing.  CT3 subsequently compares only finite response vectors; it never
decides the target by searching an ambient graph universe.
-/

/-- Application data for exact target-response compression through certified
local coordinates. -/
structure TargetCompressionContract
    (P : Core.Problem.{uAmbient, uBranch})
    (Target : P.Ambient → Prop) where
  Piece : Type uPiece
  CompatibleContext : Type uCompatible
  Coordinate : Type uCoordinate
  Candidate : Type uCandidate
  Row : Type uRow
  glue : Piece → CompatibleContext → P.Ambient
  classify : CompatibleContext → Coordinate
  response : Piece → Coordinate → Bool
  response_correct : ∀ piece context,
    response piece (classify context) = true ↔ Target (glue piece context)
  candidatePiece : Candidate → Piece
  AdmissibleReplacement : P.Ambient → Piece → Candidate → Prop
  StrictlySmaller : P.Ambient → Piece → Candidate → Prop
  rowPiece : Row → Piece
  rowResponse : Row → Coordinate → Bool
  coordinates : FinEnum Coordinate
  candidates : FinEnum Candidate
  rows : FinEnum Row
  admissibleDecidable :
    ∀ object source candidate,
      Decidable (AdmissibleReplacement object source candidate)
  smallerDecidable :
    ∀ object source candidate,
      Decidable (StrictlySmaller object source candidate)
  inputSize : P.Ambient → Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : ∀ object,
    localCheckBound coordinates candidates rows ≤
      workCoefficient * (inputSize object + 1) ^ workDegree

namespace TargetCompressionContract

/-- The CT3 specification generated from certified coordinate semantics. -/
def spec {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (contract : TargetCompressionContract P Target) : Spec P where
  Piece := contract.Piece
  Context := contract.Coordinate
  Candidate := contract.Candidate
  Row := contract.Row
  response := contract.response
  candidatePiece := contract.candidatePiece
  Admissible := contract.AdmissibleReplacement
  Smaller := contract.StrictlySmaller
  rowPiece := contract.rowPiece
  rowResponse := contract.rowResponse

/-- The executable CT3 capability generated from the local finite data. -/
def capability {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (contract : TargetCompressionContract P Target) :
    Capability contract.spec where
  contexts := contract.coordinates
  candidates := contract.candidates
  rows := contract.rows
  admissibleDecidable := contract.admissibleDecidable
  smallerDecidable := contract.smallerDecidable
  inputSize := contract.inputSize
  workCoefficient := contract.workCoefficient
  workDegree := contract.workDegree
  workBound := contract.workBound

/-- Materialize a CT3 input while preserving its branch context. -/
def input {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (contract : TargetCompressionContract P Target)
    (branch : Core.BranchContext P) (piece : contract.Piece) :
    Input contract.spec where
  context := branch
  piece := piece

/-- A target-compression execution together with the verified limit on all
primitive local checks in its schedule. -/
structure AuditedRun {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (contract : TargetCompressionContract P Target)
    (branch : Core.BranchContext P) (piece : contract.Piece) where
  result : ExecutionResult contract.spec contract.capability
    (contract.input branch piece)
  checkLimit : Nat
  checkLimit_eq : checkLimit = localCheckBound contract.coordinates
    contract.candidates contract.rows
  polynomial : checkLimit ≤ contract.workCoefficient *
    (contract.inputSize branch.G + 1) ^ contract.workDegree

namespace AuditedRun

def terminal {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {contract : TargetCompressionContract P Target}
    {branch : Core.BranchContext P} {piece : contract.Piece}
    (run : AuditedRun contract branch piece) : Graph.Terminal :=
  run.result.terminal

def trace {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {contract : TargetCompressionContract P Target}
    {branch : Core.BranchContext P} {piece : contract.Piece}
    (run : AuditedRun contract branch piece) : List Graph.NodeId :=
  run.result.trace

def outcome {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {contract : TargetCompressionContract P Target}
    {branch : Core.BranchContext P} {piece : contract.Piece}
    (run : AuditedRun contract branch piece) :
    RawOutcome contract.spec contract.capability
      (contract.input branch piece) run.terminal :=
  run.result.outcome

end AuditedRun

/-- Execute CT3 using only the contract's finite local coordinates. -/
def run {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (contract : TargetCompressionContract P Target)
    (branch : Core.BranchContext P) (piece : contract.Piece) :
    AuditedRun contract branch piece where
  result := CT3.run contract.spec contract.capability
    (contract.input branch piece)
  checkLimit := localCheckBound contract.coordinates contract.candidates
    contract.rows
  checkLimit_eq := rfl
  polynomial := contract.workBound branch.G

/-- The response bit used by CT3 is exact for every compatible glued
context. -/
theorem response_eq_true_iff
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (contract : TargetCompressionContract P Target)
    (piece : contract.Piece) (context : contract.CompatibleContext) :
    contract.response piece (contract.classify context) = true ↔
      Target (contract.glue piece context) :=
  contract.response_correct piece context

/-- Equality of finite coordinate vectors gives target equivalence in every
compatible ambient context. -/
theorem sameResponse_target_iff
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (contract : TargetCompressionContract P Target)
    {left right : contract.Piece}
    (same : SameResponse contract.spec left right)
    (context : contract.CompatibleContext) :
    Target (contract.glue left context) ↔
      Target (contract.glue right context) := by
  have responseEq :
      contract.response left (contract.classify context) =
        contract.response right (contract.classify context) := by
    simpa [spec] using same (contract.classify context)
  calc
    Target (contract.glue left context) ↔
        contract.response left (contract.classify context) = true :=
      (contract.response_correct left context).symm
    _ ↔ contract.response right (contract.classify context) = true := by
      rw [responseEq]
    _ ↔ Target (contract.glue right context) :=
      contract.response_correct right context

/-- Exact coordinate equality supplies the target implication used by
replacement arguments. -/
theorem sameResponse_targetIncluded
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (contract : TargetCompressionContract P Target)
    {left right : contract.Piece}
    (same : SameResponse contract.spec left right)
    (context : contract.CompatibleContext) :
    Target (contract.glue left context) →
      Target (contract.glue right context) :=
  (contract.sameResponse_target_iff same context).mp

/-- Every run exposes the exact finite worst-case check limit. -/
theorem run_checkLimit_eq
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (contract : TargetCompressionContract P Target)
    (branch : Core.BranchContext P) (piece : contract.Piece) :
    (contract.run branch piece).checkLimit =
      localCheckBound contract.coordinates contract.candidates contract.rows :=
  rfl

/-- Every run's complete local schedule satisfies its declared polynomial
bound. -/
theorem run_checkLimit_polynomial
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (contract : TargetCompressionContract P Target)
    (branch : Core.BranchContext P) (piece : contract.Piece) :
    (contract.run branch piece).checkLimit ≤ contract.workCoefficient *
      (contract.inputSize branch.G + 1) ^ contract.workDegree :=
  (contract.run branch piece).polynomial

/-- Every generated execution proves its terminal's structural claim. -/
theorem run_verified {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (contract : TargetCompressionContract P Target)
    (branch : Core.BranchContext P) (piece : contract.Piece) :
    OutcomeClaim (contract.run branch piece).outcome :=
  (contract.run branch piece).result.verified

/-- Every generated execution carries a valid typed trace. -/
theorem run_traceValid {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (contract : TargetCompressionContract P Target)
    (branch : Core.BranchContext P) (piece : contract.Piece) :
    @Graph.ValidTrace P contract.spec contract.capability
      (contract.input branch piece) (contract.run branch piece).trace :=
  (contract.run branch piece).result.traceValid

/-- Finite local data determine a verified result and valid typed trace. -/
theorem run_total {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (contract : TargetCompressionContract P Target)
    (branch : Core.BranchContext P) (piece : contract.Piece) :
    ∃ result : ExecutionResult contract.spec contract.capability
        (contract.input branch piece),
      OutcomeClaim result.outcome ∧
        @Graph.ValidTrace P contract.spec contract.capability
          (contract.input branch piece) result.trace :=
  CT3.run_total contract.spec contract.capability
    (contract.input branch piece)

end TargetCompressionContract

end StructuralExhaustion.CT3
