import Hypostructure.Core.Response.FiniteTable

/-!
# Generic response algebra fixtures

The exact coordinate schedule is the root residual.  The examples exercise
assembly-backed evaluation, equal vectors, first-mismatch selection, symbolic
coverage, target completeness, and the impossibility of orientation without
strict progress.
-/

namespace Hypostructure.Fixtures.Response

open Hypostructure.Core
open Hypostructure.Core.Response
open Hypostructure.Core.Response.FiniteTable

def pairProblem : Problem where
  Ambient := Bool × Bool
  Baseline := fun _object => True
  BranchState := fun _object => Unit

def pairSemantics : SemanticEquivalence pairProblem :=
  SemanticEquivalence.equality pairProblem

def pairAssembly : AtomContextAssembly pairProblem pairSemantics where
  Interface := Unit
  Site := fun _object => Unit
  interface := fun _object _site => ()
  Atom := fun _interface => Bool
  Context := fun _interface => Bool
  compatible := fun _atom _context => True
  atom := fun object _site => object.1
  context := fun object _site => object.2
  assemble := fun atom context => (atom, context)
  extractedCompatible := by intros; trivial
  reconstruct := by intros; rfl

/-- Response is conjunction of an atom and its outside context. -/
def boolResponses : System Bool :=
  System.ofAssembly pairAssembly () Bool id Bool
    (fun object => object.1 && object.2)

local instance boolResponseDecidableEq : DecidableEq boolResponses.Value := by
  change DecidableEq Bool
  infer_instance

def schedule : ExactSchedule boolResponses.Coordinate :=
  ExactSchedule.ofList [false, true]

abbrev ScheduleLedger := Residual.Ledger
  (ExactSchedule boolResponses.Coordinate)

def scheduleLedger : ScheduleLedger :=
  Residual.Ledger.initial schedule

def scheduleQuery : Residual.Query ScheduleLedger
    (fun _previous => ExactSchedule boolResponses.Coordinate) :=
  Residual.Query.residual

def equalRepresentatives : Representatives Bool where
  source := true
  replacement := true

def distinctRepresentatives : Representatives Bool where
  source := true
  replacement := false

def equalTable :=
  Table.build boolResponses equalRepresentatives schedule

def distinctTable :=
  Table.build boolResponses distinctRepresentatives schedule

/-- Equal representatives admit no scheduled distinction. -/
theorem equalNotDistinguishes : Not (Distinguishes equalTable) := by
  rintro ⟨index, differs⟩
  apply differs
  fin_cases index <;> rfl

/-- The framework promotes absence of a distinction to exact neutrality. -/
def equalResponses : Neutrality equalTable :=
  equalTable.neutralityOfNotDistinguishes equalNotDistinguishes

/-- The second scheduled coordinate distinguishes `true` from `false`. -/
theorem distinctResponses : Distinguishes distinctTable := by
  refine ⟨⟨1, by decide⟩, ?_⟩
  decide

def firstDistinct : FirstDistinction distinctTable :=
  distinctTable.firstDistinction distinctResponses

/-- Core selects index one because it also certifies equality at index zero. -/
theorem firstDistinct_index : firstDistinct.index.val = 1 := by
  have inBounds : firstDistinct.index.val < 2 :=
    firstDistinct.index.isLt
  have nonzero : Not (firstDistinct.index.val = 0) := by
    intro isZero
    have indexEq : firstDistinct.index = ⟨0, by decide⟩ :=
      Fin.ext isZero
    have contradiction := firstDistinct.differs
    rw [indexEq] at contradiction
    exact contradiction rfl
  omega

theorem firstDistinct_earlierEqual :
    distinctTable.sourceVector ⟨0, by decide⟩ =
      distinctTable.replacementVector ⟨0, by decide⟩ := by
  apply firstDistinct.earlierEqual
  show 0 < firstDistinct.index.val
  rw [firstDistinct_index]
  decide

/-- Both Boolean contexts occur in the residual-owned schedule. -/
def completeCoverage
    (representatives : Representatives Bool) :
    SymbolicCoverage boolResponses representatives schedule where
  locate := by
    intro context
    cases context
    · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩

def targetSemantics : TargetSemantics boolResponses where
  TargetResponse := fun representative context =>
    (representative && context) = true
  Accepts := fun response => response = true
  target_iff_accepts := by intros; rfl

/-- Finite equality and symbolic completeness imply equality in every outside
context. -/
def universalNeutrality :
    UniversalNeutrality boolResponses equalRepresentatives :=
  equalResponses.universal (completeCoverage equalRepresentatives)

theorem universalNeutrality_at (context : Bool) :
    boolResponses.contextResponse equalRepresentatives.source context =
      boolResponses.contextResponse equalRepresentatives.replacement context :=
  universalNeutrality.equalInContext context

/-- The same finite certificate yields target-complete equivalence. -/
def completeTargetEquivalence :
    TargetCompleteEquivalence targetSemantics equalRepresentatives :=
  equalResponses.targetComplete (completeCoverage equalRepresentatives)
    targetSemantics

theorem completeTargetEquivalence_at (context : Bool) :
    targetSemantics.TargetResponse equalRepresentatives.source context <->
      targetSemantics.TargetResponse
        equalRepresentatives.replacement context :=
  completeTargetEquivalence.targetIff context

/-- Classification consumes the schedule through a typed residual query and
retains that exact ledger as predecessor. -/
def equalClassification :=
  FiniteTable.run boolResponses equalRepresentatives scheduleQuery scheduleLedger

theorem classification_retains_schedule :
    equalClassification.previous = scheduleLedger :=
  Residual.Decision.Node.run_previous
    (FiniteTable.classificationNode boolResponses equalRepresentatives
      scheduleQuery) scheduleLedger

def boolProgress : ProgressSystem Bool where
  Measure := Nat
  measure := fun value => if value then 1 else 0
  Strict := fun left right => left < right

def zeroIncrement : SignedIncrement boolProgress equalRepresentatives :=
  SignedIncrement.ofDifference Int 0
    (fun source replacement => Int.ofNat source - Int.ofNat replacement)

theorem zeroIncrement_exact : zeroIncrement.increment = zeroIncrement.zero := by
  rfl

theorem noNonzeroEvidence : Not (NonzeroEvidence zeroIncrement) := by
  intro evidence
  exact evidence.nonzero zeroIncrement_exact

/-- Response and target equality cannot fabricate either strict orientation. -/
theorem noFabricatedOrientation :
    Not (Nonempty (OrientedComparison targetSemantics equalRepresentatives
      boolProgress)) := by
  apply OrientedComparison.notNonempty
  intro direction
  cases direction <;>
    simp [StrictAt, boolProgress, equalRepresentatives]

#print axioms equalResponses
#print axioms firstDistinct_index
#print axioms firstDistinct_earlierEqual
#print axioms universalNeutrality_at
#print axioms completeTargetEquivalence_at
#print axioms classification_retains_schedule
#print axioms zeroIncrement_exact
#print axioms noFabricatedOrientation

end Hypostructure.Fixtures.Response
