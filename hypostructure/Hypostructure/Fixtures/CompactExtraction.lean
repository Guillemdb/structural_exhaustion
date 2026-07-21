import Hypostructure.Core.Compactness.Extraction

/-!
# Compact-extraction fixture

An eventually constant sequence verifies selector identity, convergence,
baseline closure, retained-obstruction persistence, and exact predecessor
ledger extension.
-/

namespace Hypostructure.Fixtures.CompactExtraction

open Hypostructure.Core

def problem : Core.Problem where
  Ambient := Nat
  Baseline value := value = 1
  BranchState _ := Unit

def sequenceTerm (_sequence : Unit) (index : Nat) : Nat :=
  if index = 0 then 0 else 1

def selectedIndex (_selected : Unit) (index : Nat) : Nat :=
  index + 1

def sequenceConverges (_sequence : Unit) (selected : Unit)
    (_topology : Unit) : Prop :=
  forall index, sequenceTerm () (selectedIndex selected index) = 1

def extraction : Core.CompactExtraction problem where
  Sequence := Unit
  Limit := Nat
  Topology := Unit
  term := sequenceTerm
  realizeLimit := id
  Extracted _ := Unit
  selector := selectedIndex
  selectorStrict _ := by
    intro a b hab
    simpa [selectedIndex] using Nat.add_lt_add_right hab 1
  limit _ := 1
  topology _ := ()
  Converges := sequenceConverges
  convergence _selected := by
    intro index
    simp [sequenceTerm, selectedIndex]
  extract _ := ()

def baselineClosed : extraction.BaselineClosed where
  closed _selected _terms := by
    change (1 : Nat) = 1
    rfl

def obstruction (value : Nat) : Prop := value = 1

def obstructionPersistent : extraction.ObstructionPersistent obstruction where
  closed _selected _terms := by
    change (1 : Nat) = 1
    rfl

def retainedInput : extraction.RetainedInput obstruction () where
  baseline index := by
    change sequenceTerm () (selectedIndex () index) = 1
    simp [sequenceTerm, selectedIndex]
  obstruction index := by
    change sequenceTerm () (selectedIndex () index) = 1
    simp [sequenceTerm, selectedIndex]

def root : Core.Residual.Ledger Unit :=
  Core.Residual.Ledger.initial ()

def node := extraction.descendantNode baselineClosed obstructionPersistent
  (fun (_previous : Core.Residual.Ledger Unit) => ())
  (fun _previous => retainedInput)

def stage := node.run root

example : stage.previous = root := rfl

example : stage.added.record.subsequence 3 = (1 : Nat) := by
  rfl

example : stage.added.record.descendant = (1 : Nat) := rfl

example : problem.Baseline stage.added.record.descendant :=
  stage.added.baseline

example : obstruction stage.added.record.descendant :=
  stage.added.obstruction

example : StrictMono
    (extraction.selector stage.added.record.extraction) :=
  stage.added.record.selectorStrict

example : extraction.Converges (show extraction.Sequence from ())
    stage.added.record.extraction
    (extraction.topology stage.added.record.extraction) :=
  stage.added.record.converges

#print axioms Core.CompactExtraction.run
#print axioms Core.CompactExtraction.descend
#print axioms Core.CompactExtraction.descendantNode
#print axioms stage

end Hypostructure.Fixtures.CompactExtraction
