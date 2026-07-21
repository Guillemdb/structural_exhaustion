import Hypostructure.CT8.State
import Hypostructure.Core.Finite.Accounting

/-!
# CT8 canonical finite scans

The first scan traverses all strict occurrence pairs in lexicographic order.
Only its first hit is passed to the second scan, which traverses the exact
complete response-context schedule.  Both branches are routed by Core.
-/

namespace Hypostructure.CT8

universe uPrevious uState uType uContext uValue uRemoval

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uState, uType, uContext, uValue, uRemoval}
    Previous}

/-- Primitive decidability of equal exact types at one ordered index pair. -/
def sameExactTypeDecidable (capability : Capability spec)
    (previous : Previous)
    (indices : OrderedIndexPair (capability.sequenceAt previous).length) :
    Decidable (SameExactType capability previous indices) :=
  capability.exactTypeDecEq previous
    (spec.exactType previous (capability.stateAt previous indices.1.1))
    (spec.exactType previous (capability.stateAt previous indices.1.2))

/-- Counted canonical repeated-type scan. -/
def countedRepetitionScan (capability : Capability spec)
    (previous : Previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.orderedPairsAt previous).toEnumeration
      (SameExactType capability previous)) :=
  Core.Finite.Accounting.countedRun
    (capability.orderedPairsAt previous).toEnumeration
    (SameExactType capability previous)
    (sameExactTypeDecidable capability previous)

/-- Proof-carrying repeated-type scan. -/
def repetitionScan (capability : Capability spec) (previous : Previous) :=
  (countedRepetitionScan capability previous).value

/-- Exact pair comparisons performed by the repeated-type scan. -/
def repetitionChecks (capability : Capability spec)
    (previous : Previous) : Nat :=
  (countedRepetitionScan capability previous).checks

/-- Route the repeated-type result through Core's first-hit decision. -/
def routeRepetition (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.route (repetitionScan capability previous)

/-- Primitive decidability of response inequality in one queried context. -/
def responseDiffersDecidable (capability : Capability spec)
    (previous : Previous) (pair : OrderedRepeatedPair capability previous)
    (context : spec.ResponseContext previous) :
    Decidable (ResponseDiffers capability previous pair context) := by
  letI : DecidableEq (spec.ResponseValue previous) :=
    capability.responseValueDecEq previous
  unfold ResponseDiffers
  infer_instance

/-- Counted canonical response-separation scan for the selected repeated pair. -/
def countedResponseScan (capability : Capability spec)
    (previous : Previous) (pair : OrderedRepeatedPair capability previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.responseContextsAt previous).toEnumeration
      (ResponseDiffers capability previous pair)) :=
  Core.Finite.Accounting.countedRun
    (capability.responseContextsAt previous).toEnumeration
    (ResponseDiffers capability previous pair)
    (responseDiffersDecidable capability previous pair)

/-- Proof-carrying response scan for the framework-selected pair. -/
def responseScan (capability : Capability spec) (previous : Previous)
    (pair : OrderedRepeatedPair capability previous) :=
  (countedResponseScan capability previous pair).value

/-- Exact response comparisons performed for the selected pair. -/
def responseChecks (capability : Capability spec) (previous : Previous)
    (pair : OrderedRepeatedPair capability previous) : Nat :=
  (countedResponseScan capability previous pair).checks

/-- Route response separation through Core's first-hit decision. -/
def routeResponse (capability : Capability spec) (previous : Previous)
    (pair : OrderedRepeatedPair capability previous) :=
  Core.Finite.Search.route (responseScan capability previous pair)

/-- Pair discovery never exceeds the exact framework-derived pair schedule. -/
theorem repetitionChecks_le_card (capability : Capability spec)
    (previous : Previous) :
    repetitionChecks capability previous <=
      (capability.orderedPairsAt previous).toEnumeration.card :=
  Core.Finite.Accounting.executionChecks_le_card
    (repetitionScan capability previous)

/-- Response comparison never exceeds the exact incoming context schedule. -/
theorem responseChecks_le_card (capability : Capability spec)
    (previous : Previous) (pair : OrderedRepeatedPair capability previous) :
    responseChecks capability previous pair <=
      (capability.responseContextsAt previous).toEnumeration.card :=
  Core.Finite.Accounting.executionChecks_le_card
    (responseScan capability previous pair)

end Hypostructure.CT8
