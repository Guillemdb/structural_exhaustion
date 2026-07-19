import StructuralExhaustion.CT3.Spec

namespace StructuralExhaustion.CT3

universe uAmbient uBranch uPiece uContext uCandidate uRow

/-!
Executable CT3 capability.  Exact Mathlib finite enumerations define reference
search order; the predicates are mathematical data and their decision
procedures do not choose an outcome.
-/

/-- Worst-case number of primitive local checks in one CT3 run: two
structural predicates and one coordinate comparison per candidate, followed
when necessary by table validation and row lookup. -/
def localCheckBound {Context Candidate Row : Type*}
    (contexts : FinEnum Context) (candidates : FinEnum Candidate)
    (rows : FinEnum Row) : Nat :=
  candidates.orderedValues.length * (2 + contexts.orderedValues.length) +
    2 * rows.orderedValues.length * contexts.orderedValues.length

/-- Minimum executable capability for the reference CT3 runner. -/
structure Capability {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P) where
  contexts : FinEnum S.Context
  candidates : FinEnum S.Candidate
  rows : FinEnum S.Row
  admissibleDecidable :
    ∀ G source candidate, Decidable (S.Admissible G source candidate)
  smallerDecidable :
    ∀ G source candidate, Decidable (S.Smaller G source candidate)
  inputSize : P.Ambient → Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : ∀ G,
    localCheckBound contexts candidates rows ≤
      workCoefficient * (inputSize G + 1) ^ workDegree

/-- Transition-facing CT3 trigger.  The shared context is an index, so a transition
construction cannot replace or realign it. -/
structure Trigger {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P) (_context : Core.BranchContext P) where
  piece : S.Piece

namespace Capability

/-- Verified polynomial budget for the complete local CT3 schedule. -/
def polynomialBudget {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec P} (capability : Capability S) :
    Core.PolynomialCheckBudget P.Ambient where
  size := capability.inputSize
  checks := fun _ => localCheckBound capability.contexts
    capability.candidates capability.rows
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := capability.workBound

end Capability

/-- Audit contract for the complete tactic capability. -/
def capabilityContract : Core.CapabilityContract where
  capabilityId := "CT3.reference"
  tacticId := "CT3"
  requiredDefinitions := [
    ⟨"Spec.Piece", .userDefinition⟩,
    ⟨"Spec.Context", .userDefinition⟩,
    ⟨"Spec.Candidate", .userDefinition⟩,
    ⟨"Spec.Row", .userDefinition⟩,
    ⟨"Spec.response", .userOperator⟩,
    ⟨"Spec.candidatePiece", .userOperator⟩,
    ⟨"Spec.Admissible", .userDefinition⟩,
    ⟨"Spec.Smaller", .userDefinition⟩,
    ⟨"Spec.rowPiece", .userOperator⟩,
    ⟨"Spec.rowResponse", .userOperator⟩,
    ⟨"Capability.contexts", .userFiniteEnumeration⟩,
    ⟨"Capability.candidates", .userFiniteEnumeration⟩,
    ⟨"Capability.rows", .userFiniteEnumeration⟩,
    ⟨"Capability.admissibleDecidable", .instanceBridge⟩,
    ⟨"Capability.smallerDecidable", .instanceBridge⟩,
    ⟨"Capability.inputSize", .userOperator⟩,
    ⟨"Capability.workCoefficient", .userDefinition⟩,
    ⟨"Capability.workDegree", .userDefinition⟩,
    ⟨"Capability.workBound", .userDefinition⟩
  ]
  requiredInstances := [
    "Capability.admissibleDecidable",
    "Capability.smallerDecidable"
  ]
  derivedOperations := [
    "CT3.computeExactVector",
    "CT3.findCompression",
    "CT3.validateTable",
    "CT3.lookupRow",
    "CT3.Capability.polynomialBudget",
    "CT3.runReference",
    "CT3.run"
  ]

end StructuralExhaustion.CT3
