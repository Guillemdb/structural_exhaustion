import Hypostructure.Core.Compactness.Extraction

/-!
# Eventually constant compact extraction

The concrete sequence is constant after its first two terms. Core selects and
records the tail, proves the descendant baseline, retains the obstruction, and
extends the exact predecessor ledger.
-/

namespace HypostructurePDEExamples.CompactExtraction

open Hypostructure

def problem : Core.Problem where
  Ambient := Nat
  Baseline := fun value => value = 7
  BranchState := fun _ => Unit

def sequenceTerm (_sequence : Unit) (index : Nat) : Nat :=
  if index < 2 then 0 else 7

def selectedIndex (_extraction : Unit) (index : Nat) : Nat :=
  index + 2

def selectedConvergence (_sequence : Unit) (extraction : Unit)
    (_topology : Unit) : Prop :=
  forall index, sequenceTerm () (selectedIndex extraction index) = 7

def extraction : Core.CompactExtraction problem where
  Sequence := Unit
  Limit := Nat
  Topology := Unit
  term := sequenceTerm
  realizeLimit := id
  Extracted := fun _ => Unit
  selector := selectedIndex
  selectorStrict := by
    intro sequence extracted first second less
    simpa [selectedIndex] using Nat.add_lt_add_right less 2
  limit := fun _ => 7
  topology := fun _ => ()
  Converges := selectedConvergence
  convergence := by
    intro sequence extracted index
    change sequenceTerm () (selectedIndex () index) = 7
    simp [sequenceTerm, selectedIndex]
  extract := fun _ => ()

def baselineClosed : extraction.BaselineClosed where
  closed := by
    intro sequence extracted selectedBaseline
    rfl

def obstruction (value : Nat) : Prop := 5 <= value

def obstructionPersistent : extraction.ObstructionPersistent obstruction where
  closed := by
    intro sequence extracted selectedObstruction
    change 5 ≤ (7 : Nat)
    norm_num

def retainedInput : extraction.RetainedInput obstruction () where
  baseline := by
    intro index
    change sequenceTerm () (selectedIndex () index) = 7
    simp [sequenceTerm, selectedIndex]
  obstruction := by
    intro index
    change 5 ≤ sequenceTerm () (selectedIndex () index)
    simp [sequenceTerm, selectedIndex]

def root : Core.Residual.Ledger Unit :=
  Core.Residual.Ledger.initial ()

def node := extraction.descendantNode baselineClosed obstructionPersistent
  (fun (_previous : Core.Residual.Ledger Unit) => ())
  (fun _previous => retainedInput)

def stage := node.run root

theorem stage_retains_predecessor : stage.previous = root := rfl

theorem selected_tail_is_constant (index : Nat) :
    stage.added.record.subsequence index = (7 : Nat) := by
  change sequenceTerm () (selectedIndex () index) = 7
  simp [sequenceTerm, selectedIndex]

theorem descendant_is_baseline :
    problem.Baseline stage.added.record.descendant :=
  stage.added.baseline

theorem descendant_retains_obstruction :
    obstruction stage.added.record.descendant :=
  stage.added.obstruction

theorem selector_is_strict :
    StrictMono (extraction.selector stage.added.record.extraction) :=
  stage.added.record.selectorStrict

theorem selected_sequence_converges :
    extraction.Converges () stage.added.record.extraction
      (extraction.topology stage.added.record.extraction) :=
  stage.added.record.converges

#print axioms stage_retains_predecessor
#print axioms selected_tail_is_constant
#print axioms descendant_is_baseline
#print axioms descendant_retains_obstruction
#print axioms selector_is_strict
#print axioms selected_sequence_converges

end HypostructurePDEExamples.CompactExtraction
