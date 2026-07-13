import StructuralExhaustion.CT10.Automation
import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Core.WorkBudget
import Mathlib.Tactic

namespace StructuralExhaustion.CT10.ExhaustiveClassification

open StructuralExhaustion

universe uAmbient uBranch uCandidate

/-!
# CT10 profile for exact accepted-class tables

An application supplies one explicitly finite candidate type and a decidable
acceptance predicate.  The accepted subtype is the class universe, and its
own exact enumeration is also the datum table.  CT10 therefore certifies that
there is no direct exceptional class and that every accepted class has a row.

The runner scans only the supplied finite candidate/class tables.  It never
enumerates ambient objects, graphs, subgraphs, or recursive states.
-/

/-- Static author data for an exact finite classification. -/
structure Profile (Candidate : Type uCandidate) where
  candidates : FinEnum Candidate
  Accepts : Candidate → Prop
  acceptsDecidable : (candidate : Candidate) → Decidable (Accepts candidate)

namespace Profile

variable {Candidate : Type uCandidate}
variable (profile : Profile Candidate)

/-- A class is precisely a candidate satisfying the supplied predicate. -/
abbrev Class := {candidate : Candidate // profile.Accepts candidate}

/-- Exact accepted-class enumeration, retaining the candidate enumeration's
order. -/
@[implicit_reducible]
def classes : FinEnum profile.Class :=
  Core.Enumeration.subtype profile.candidates profile.Accepts
    profile.acceptsDecidable

/-- Canonical CT10 capability: accepted classes classify themselves, and
there is no exceptional direct branch. -/
def capability (P : Core.Problem.{uAmbient, uBranch}) : CT10.Capability P where
  Datum := profile.Class
  Class := profile.Class
  Promotion := profile.Class
  classes := profile.classes
  classOf := id
  Direct := fun _class => False
  directDecidable := fun _class => isFalse id
  promote := id

/-- CT10 receives the complete accepted-class table in its inherited branch
context. -/
def input {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    CT10.Input (profile.capability P) where
  context := context
  data := profile.classes.toOrderedCollection

/-- Execute the canonical CT10 finite-refinement runner. -/
def run {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    CT10.ExecutionResult (profile.capability P) (profile.input context) :=
  CT10.run (profile.capability P) (profile.input context)

/-- Number of source candidates inspected by the finite classifier. -/
def candidateCount : Nat := profile.candidates.card

/-- Number of accepted classes in the exact table. -/
def classCount : Nat := profile.classes.card

/-- Every accepted class occurs as its own table datum. -/
theorem class_mem_own_row {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (cls : profile.Class) :
    cls ∈ CT10.row (profile.capability P) (profile.input context) cls := by
  exact CT10.datum_mem_own_row (profile.capability P)
    (profile.input context) cls (profile.classes.mem_orderedValues cls)

private theorem analyzeDirect_absent
    (P : Core.Problem.{uAmbient, uBranch}) :
    ∃ state : CT10.DirectAbsent (profile.capability P),
      CT10.analyzeDirect (profile.capability P) = .absent state := by
  cases equation : CT10.analyzeDirect (profile.capability P) with
  | found residual => exact residual.direct.elim
  | absent state => exact ⟨state, rfl⟩

private theorem analyzeMissing_exhaustive
    {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P)
    (directAbsent : CT10.DirectAbsent (profile.capability P)) :
    ∃ certificate : CT10.ExhaustiveCertificate (profile.capability P)
        (profile.input context),
      CT10.analyzeMissing (profile.capability P) (profile.input context)
        directAbsent = .exhaustive certificate := by
  cases equation : CT10.analyzeMissing (profile.capability P)
      (profile.input context) directAbsent with
  | promoted residual =>
      have member := profile.class_mem_own_row context residual.missing.cls
      have impossible : False := by
        rw [residual.missing.empty] at member
        exact List.not_mem_nil member
      exact impossible.elim
  | exhaustive certificate => exact ⟨certificate, rfl⟩

/-- The CT10 run cannot terminate at a direct class or at a missing class;
the supplied table is definitionally complete. -/
theorem run_terminal_exhaustive {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    (profile.run context).terminal = .exhaustive := by
  apply CT10.run_terminal_exhaustive_of_noDirect_of_populated
  · intro cls direct
    exact direct
  · intro cls
    exact ⟨cls, profile.class_mem_own_row context cls⟩

/-- Exact typed trace of the complete-table execution. -/
theorem run_trace {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    (profile.run context).trace =
      [.entry, .table, .direct, .missing, .exhaustiveTerminal] := by
  apply CT10.run_trace_exhaustive_of_noDirect_of_populated
  · intro cls direct
    exact direct
  · intro cls
    exact ⟨cls, profile.class_mem_own_row context cls⟩

/-- Semantic verification inherited from CT10. -/
theorem run_verified {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    (profile.run context).outcome.Valid :=
  CT10.run_verified (profile.capability P) (profile.input context)

/-- Typed trace verification inherited from CT10. -/
theorem run_trace_valid {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    CT10.Graph.ValidTrace (profile.capability P) (profile.input context)
      (profile.run context).trace :=
  CT10.run_trace_valid (profile.capability P) (profile.input context)

/-- Totality with the exact terminal and trace of this profile. -/
theorem run_total {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    ∃ result : CT10.ExecutionResult (profile.capability P)
        (profile.input context),
      result.terminal = .exhaustive ∧
        result.trace =
          [.entry, .table, .direct, .missing, .exhaustiveTerminal] ∧
        result.outcome.Valid ∧
        CT10.Graph.ValidTrace (profile.capability P) (profile.input context)
          result.trace :=
  ⟨profile.run context, profile.run_terminal_exhaustive context,
    profile.run_trace context, profile.run_verified context,
    profile.run_trace_valid context⟩

/-- The accepted subtype cannot contain more classes than its source
candidate universe. -/
theorem classCount_le_candidateCount :
    profile.classCount ≤ profile.candidateCount := by
  letI : FinEnum Candidate := profile.candidates
  letI : FinEnum profile.Class := profile.classes
  have cardinality : Fintype.card profile.Class ≤ Fintype.card Candidate :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  simpa [classCount, candidateCount, FinEnum.card_eq_fintypeCard]
    using cardinality

/-- Primitive predicate-check schedule: classify every supplied candidate,
then perform CT10's direct scan and row-population scan. -/
def checks : Nat :=
  profile.candidateCount + profile.classCount + profile.classCount ^ 2

/-- A uniform quadratic budget in the explicitly supplied candidate count. -/
def budget : Core.PolynomialCheckBudget Unit where
  size := fun _ => profile.candidateCount
  checks := fun _ => profile.checks
  coefficient := 1
  degree := 2
  bounded := by
    intro _unit
    have bound := profile.classCount_le_candidateCount
    simp only [checks]
    nlinarith

/-- Complete reusable CT10 result for an exact accepted-class table. -/
structure VerifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) : Prop where
  terminal : (profile.run context).terminal = .exhaustive
  trace : (profile.run context).trace =
    [.entry, .table, .direct, .missing, .exhaustiveTerminal]
  verified : (profile.run context).outcome.Valid
  traceValid : CT10.Graph.ValidTrace (profile.capability P)
    (profile.input context) (profile.run context).trace
  populated : ∀ cls : profile.Class,
    ∃ datum : profile.Class,
      datum ∈ CT10.row (profile.capability P) (profile.input context) cls
  total : ∃ result : CT10.ExecutionResult (profile.capability P)
      (profile.input context),
    result.terminal = .exhaustive ∧
      result.trace =
        [.entry, .table, .direct, .missing, .exhaustiveTerminal] ∧
      result.outcome.Valid ∧
      CT10.Graph.ValidTrace (profile.capability P) (profile.input context)
        result.trace
  classCount_le_candidates : profile.classCount ≤ profile.candidateCount
  polynomial : profile.checks ≤
    profile.budget.coefficient *
      (profile.budget.size () + 1) ^ profile.budget.degree

/-- Construct the verified CT10 stage from the finite predicate alone. -/
def verifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) : profile.VerifiedStage context where
  terminal := profile.run_terminal_exhaustive context
  trace := profile.run_trace context
  verified := profile.run_verified context
  traceValid := profile.run_trace_valid context
  populated := fun cls => ⟨cls, profile.class_mem_own_row context cls⟩
  total := profile.run_total context
  classCount_le_candidates := profile.classCount_le_candidateCount
  polynomial := profile.budget.bounded ()

end Profile

end StructuralExhaustion.CT10.ExhaustiveClassification
