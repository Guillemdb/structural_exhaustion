import Hypostructure.Core.Problem
import Hypostructure.Core.Residual.Stage

/-!
# Compact extraction

Compactness is a registered semantic capability, not a search over an ambient
space.  A domain supplies a sequence type, a strictly increasing selector,
the selected limit, and its convergence theorem.  Core records that exact
extraction and can propagate baseline and retained-obstruction evidence to a
typed descendant without inspecting the domain.
-/

namespace Hypostructure.Core

universe uAmbient uBranch uSequence uLimit uTopology uExtracted uObstruction
  uPrevious

/-- Domain-supplied compact extraction data.  `extract` is a theorem-backed
choice of one selector; Core never enumerates candidate subsequences. -/
structure CompactExtraction
    (P : Problem.{uAmbient, uBranch}) where
  Sequence : Type uSequence
  Limit : Type uLimit
  Topology : Type uTopology
  term : Sequence -> Nat -> P.Ambient
  realizeLimit : Limit -> P.Ambient
  Extracted : Sequence -> Type uExtracted
  selector : {sequence : Sequence} -> Extracted sequence -> Nat -> Nat
  selectorStrict : forall {sequence : Sequence}
    (extraction : Extracted sequence), StrictMono (selector extraction)
  limit : {sequence : Sequence} -> Extracted sequence -> Limit
  topology : {sequence : Sequence} -> Extracted sequence -> Topology
  Converges : (sequence : Sequence) -> Extracted sequence -> Topology -> Prop
  convergence : forall {sequence : Sequence}
    (extraction : Extracted sequence),
    Converges sequence extraction (topology extraction)
  extract : (sequence : Sequence) -> Extracted sequence

namespace CompactExtraction

/-- The exact extraction selected by a registered compactness capability. -/
structure Record {P : Problem.{uAmbient, uBranch}}
    (X : CompactExtraction P) (sequence : X.Sequence) where
  extraction : X.Extracted sequence

/-- Execute the registered extraction. -/
def run {P : Problem.{uAmbient, uBranch}} (X : CompactExtraction P)
    (sequence : X.Sequence) : X.Record sequence where
  extraction := X.extract sequence

/-- The selected ambient subsequence, retaining its literal selector. -/
def Record.subsequence {P : Problem.{uAmbient, uBranch}}
    {X : CompactExtraction P} {sequence : X.Sequence}
    (record : X.Record sequence) (index : Nat) : P.Ambient :=
  X.term sequence (X.selector record.extraction index)

/-- The realized limit ambient object. -/
def Record.descendant {P : Problem.{uAmbient, uBranch}}
    {X : CompactExtraction P} {sequence : X.Sequence}
    (record : X.Record sequence) : P.Ambient :=
  X.realizeLimit (X.limit record.extraction)

@[simp] theorem Record.subsequence_eq {P : Problem.{uAmbient, uBranch}}
    {X : CompactExtraction P} {sequence : X.Sequence}
    (record : X.Record sequence) (index : Nat) :
    record.subsequence index =
      X.term sequence (X.selector record.extraction index) :=
  rfl

/-- The selector stored by every extraction record is strictly increasing. -/
theorem Record.selectorStrict {P : Problem.{uAmbient, uBranch}}
    {X : CompactExtraction P} {sequence : X.Sequence}
    (record : X.Record sequence) :
    StrictMono (X.selector record.extraction) :=
  X.selectorStrict record.extraction

/-- The stored extraction carries the domain's declared convergence theorem. -/
theorem Record.converges {P : Problem.{uAmbient, uBranch}}
    {X : CompactExtraction P} {sequence : X.Sequence}
    (record : X.Record sequence) :
    X.Converges sequence record.extraction (X.topology record.extraction) :=
  X.convergence record.extraction

/-- Baseline closure under one registered compact extraction. -/
structure BaselineClosed {P : Problem.{uAmbient, uBranch}}
    (X : CompactExtraction P) where
  closed : forall {sequence : X.Sequence} (extraction : X.Extracted sequence),
    (forall index,
      P.Baseline (X.term sequence (X.selector extraction index))) ->
    P.Baseline (X.realizeLimit (X.limit extraction))

/-- Persistence of a retained obstruction along the selected subsequence. -/
structure ObstructionPersistent {P : Problem.{uAmbient, uBranch}}
    (X : CompactExtraction P)
    (Obstruction : P.Ambient -> Sort uObstruction) where
  closed : forall {sequence : X.Sequence} (extraction : X.Extracted sequence),
    (forall index,
      Obstruction (X.term sequence (X.selector extraction index))) ->
    Obstruction (X.realizeLimit (X.limit extraction))

/-- Exact predecessor-owned evidence required to retain a baseline object and
an obstruction through the registered extraction. -/
structure RetainedInput {P : Problem.{uAmbient, uBranch}}
    (X : CompactExtraction P)
    (Obstruction : P.Ambient -> Sort uObstruction)
    (sequence : X.Sequence) where
  baseline : forall index,
    P.Baseline (X.term sequence (X.selector (X.extract sequence) index))
  obstruction : forall index,
    Obstruction (X.term sequence (X.selector (X.extract sequence) index))

/-- Framework-owned descendant emitted after compact extraction. -/
structure Descendant {P : Problem.{uAmbient, uBranch}}
    (X : CompactExtraction P)
    (Obstruction : P.Ambient -> Sort uObstruction)
    (sequence : X.Sequence) where
  record : X.Record sequence
  baseline : P.Baseline record.descendant
  obstruction : Obstruction record.descendant

/-- Execute compact extraction and retain the registered baseline and
obstruction. -/
def descend {P : Problem.{uAmbient, uBranch}}
    (X : CompactExtraction P)
    (baselineClosed : X.BaselineClosed)
    {Obstruction : P.Ambient -> Sort uObstruction}
    (obstructionPersistent : X.ObstructionPersistent Obstruction)
    (sequence : X.Sequence) (input : X.RetainedInput Obstruction sequence) :
    X.Descendant Obstruction sequence := by
  let record := X.run sequence
  refine {
    record := record
    baseline := ?_
    obstruction := ?_
  }
  · exact baselineClosed.closed record.extraction input.baseline
  · exact obstructionPersistent.closed record.extraction input.obstruction

/-- Register compact extraction as a data-bearing residual node.  The sequence
and all persistence evidence are computed from the literal predecessor. -/
def descendantNode {P : Problem.{uAmbient, uBranch}}
    (X : CompactExtraction P)
    (baselineClosed : X.BaselineClosed)
    {Obstruction : P.Ambient -> Sort uObstruction}
    (obstructionPersistent : X.ObstructionPersistent Obstruction)
    {Previous : Sort uPrevious}
    (sequence : Previous -> X.Sequence)
    (input : (previous : Previous) ->
      X.RetainedInput Obstruction (sequence previous)) :
    Residual.StageNode Previous (fun previous =>
      X.Descendant Obstruction (sequence previous)) :=
  Residual.StageNode.create fun previous =>
    X.descend baselineClosed obstructionPersistent
      (sequence previous) (input previous)

end CompactExtraction

end Hypostructure.Core
