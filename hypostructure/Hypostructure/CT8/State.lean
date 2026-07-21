import Hypostructure.CT8.Capability
import Hypostructure.Core.Finite.Search

/-!
# CT8 generated proof states

Every certificate is indexed by the exact predecessor and by schedules read
from it.  Pair and separator witnesses are canonical Core first hits.  The
removal value is computed only after exhaustive response equality.
-/

namespace Hypostructure.CT8

universe uPrevious uState uType uContext uValue uRemoval

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uState, uType, uContext, uValue, uRemoval}
    Previous}

/-- Two positions of the incoming sequence have the same exact type. -/
def SameExactType (capability : Capability spec) (previous : Previous)
    (indices : OrderedIndexPair (capability.sequenceAt previous).length) : Prop :=
  spec.exactType previous (capability.stateAt previous indices.1.1) =
    spec.exactType previous (capability.stateAt previous indices.1.2)

/-- The canonical first repeated pair in lexicographic occurrence order. -/
abbrev OrderedRepeatedPair (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.IndexedHit
    (capability.orderedPairsAt previous).toEnumeration
    (SameExactType capability previous)

namespace OrderedRepeatedPair

/-- Selected strict index pair. -/
def indices {capability : Capability spec} {previous : Previous}
    (pair : OrderedRepeatedPair capability previous) :
    OrderedIndexPair (capability.sequenceAt previous).length :=
  pair.value

/-- Selected left occurrence. -/
def firstIndex {capability : Capability spec} {previous : Previous}
    (pair : OrderedRepeatedPair capability previous) :
    Fin (capability.sequenceAt previous).length :=
  pair.indices.1.1

/-- Selected right occurrence. -/
def secondIndex {capability : Capability spec} {previous : Previous}
    (pair : OrderedRepeatedPair capability previous) :
    Fin (capability.sequenceAt previous).length :=
  pair.indices.1.2

/-- State at the selected left occurrence. -/
def first {capability : Capability spec} {previous : Previous}
    (pair : OrderedRepeatedPair capability previous) : spec.State previous :=
  capability.stateAt previous pair.firstIndex

/-- State at the selected right occurrence. -/
def second {capability : Capability spec} {previous : Previous}
    (pair : OrderedRepeatedPair capability previous) : spec.State previous :=
  capability.stateAt previous pair.secondIndex

/-- The selected occurrences are strictly left-to-right. -/
theorem ordered {capability : Capability spec} {previous : Previous}
    (pair : OrderedRepeatedPair capability previous) :
    pair.firstIndex < pair.secondIndex :=
  pair.indices.2

/-- The selected states have equal exact type. -/
theorem typesEqual {capability : Capability spec} {previous : Previous}
    (pair : OrderedRepeatedPair capability previous) :
    spec.exactType previous pair.first =
      spec.exactType previous pair.second :=
  pair.sound

/-- Every pair preceding the selected pair in the framework schedule has a
different exact type. -/
theorem earlierDifferent {capability : Capability spec}
    {previous : Previous} (pair : OrderedRepeatedPair capability previous) :
    forall candidate,
      candidate ∈ (capability.orderedPairsAt previous).toEnumeration.values.take
        pair.index.1 ->
      Not (SameExactType capability previous candidate) :=
  Core.Finite.Search.IndexedHit.first pair

end OrderedRepeatedPair

/-- Exhaustive absence of repeated exact types in the incoming sequence. -/
structure NoRepetitionCertificate (capability : Capability spec)
    (previous : Previous) : Prop where
  private mk ::
  avoidance : Core.Finite.Search.Avoids
    (capability.orderedPairsAt previous).toEnumeration
    (SameExactType capability previous)

/-- Build the no-repetition certificate from Core's exhaustive pair scan. -/
def noRepetitionOfAvoidance (capability : Capability spec)
    (previous : Previous)
    (avoidance : Core.Finite.Search.Avoids
      (capability.orderedPairsAt previous).toEnumeration
      (SameExactType capability previous)) :
    NoRepetitionCertificate capability previous :=
  .mk avoidance

namespace NoRepetitionCertificate

/-- Every strict bounded occurrence pair has different exact type. -/
theorem typesDifferent {capability : Capability spec} {previous : Previous}
    (certificate : NoRepetitionCertificate capability previous)
    (indices : OrderedIndexPair (capability.sequenceAt previous).length) :
    Not (SameExactType capability previous indices) := by
  have member := (capability.orderedPairsAt previous).complete indices
  obtain ⟨index, equal⟩ :=
    ((capability.orderedPairsAt previous).toEnumeration.mem_iff_exists_index
      indices).mp member
  intro sameType
  exact certificate.avoidance index (by
    simpa [equal] using sameType)

end NoRepetitionCertificate

/-- The two repeated states respond differently in one supplied context. -/
def ResponseDiffers (capability : Capability spec) (previous : Previous)
    (pair : OrderedRepeatedPair capability previous)
    (context : spec.ResponseContext previous) : Prop :=
  spec.response previous pair.first context ≠
    spec.response previous pair.second context

/-- Equality of repeated-state responses in every semantic context. -/
def ResponsesEqual (capability : Capability spec) (previous : Previous)
    (pair : OrderedRepeatedPair capability previous) : Prop :=
  forall context,
    spec.response previous pair.first context =
      spec.response previous pair.second context

/-- Canonical first response context separating the selected repeated pair. -/
abbrev ResponseSeparator (capability : Capability spec)
    (previous : Previous) (pair : OrderedRepeatedPair capability previous) :=
  Core.Finite.Search.IndexedHit
    (capability.responseContextsAt previous).toEnumeration
    (ResponseDiffers capability previous pair)

namespace ResponseSeparator

/-- Selected distinguishing context. -/
def context {capability : Capability spec} {previous : Previous}
    {pair : OrderedRepeatedPair capability previous}
    (separator : ResponseSeparator capability previous pair) :
    spec.ResponseContext previous :=
  separator.value

/-- Exact response inequality at the selected context. -/
theorem differs {capability : Capability spec} {previous : Previous}
    {pair : OrderedRepeatedPair capability previous}
    (separator : ResponseSeparator capability previous pair) :
    ResponseDiffers capability previous pair separator.context :=
  separator.sound

/-- Every earlier scheduled context fails to distinguish the pair. -/
theorem earlierNotDiffers {capability : Capability spec}
    {previous : Previous} {pair : OrderedRepeatedPair capability previous}
    (separator : ResponseSeparator capability previous pair) :
    forall context,
      context ∈
        (capability.responseContextsAt previous).toEnumeration.values.take
          separator.index.1 ->
      Not (ResponseDiffers capability previous pair context) :=
  separator.first

end ResponseSeparator

/-- A repeated pair and its first response-separating context. -/
structure SeparationResidual (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  pair : OrderedRepeatedPair capability previous
  separator : ResponseSeparator capability previous pair

/-- Build the exact separation residual from the two Core first hits. -/
def separationOfHit (capability : Capability spec) (previous : Previous)
    (pair : OrderedRepeatedPair capability previous)
    (separator : ResponseSeparator capability previous pair) :
    SeparationResidual capability previous :=
  .mk pair separator

/-- A framework-computed removal with universal response equality and strict
progress. -/
structure RemovalCertificate (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  pair : OrderedRepeatedPair capability previous
  responsesEqual : ResponsesEqual capability previous pair
  replacement : spec.Removal previous
  replacement_exact : replacement = capability.remove previous
    pair.first pair.second pair.typesEqual responsesEqual
  smaller : spec.StrictlySmaller previous replacement

/-- Promote exhaustive failure of the response-difference scan to equality in
every context of the predecessor-owned complete universe. -/
def responsesEqualOfAvoidance (capability : Capability spec)
    (previous : Previous) (pair : OrderedRepeatedPair capability previous)
    (avoidance : Core.Finite.Search.Avoids
      (capability.responseContextsAt previous).toEnumeration
      (ResponseDiffers capability previous pair)) :
    ResponsesEqual capability previous pair := by
  intro context
  match capability.responseValueDecEq previous
      (spec.response previous pair.first context)
      (spec.response previous pair.second context) with
  | .isTrue equal => exact equal
  | .isFalse differs =>
      have member := (capability.responseContextsAt previous).complete context
      obtain ⟨index, equal⟩ :=
        ((capability.responseContextsAt previous).toEnumeration
          |>.mem_iff_exists_index context).mp member
      exact (avoidance index (by
        simpa [ResponseDiffers, equal] using differs)).elim

/-- Compute the unique certified removal from the selected pair and Core's
exhaustive response-equality branch. -/
def removalOfAvoidance (capability : Capability spec) (previous : Previous)
    (pair : OrderedRepeatedPair capability previous)
    (avoidance : Core.Finite.Search.Avoids
      (capability.responseContextsAt previous).toEnumeration
      (ResponseDiffers capability previous pair)) :
    RemovalCertificate capability previous :=
  let equalResponses := responsesEqualOfAvoidance capability previous pair
    avoidance
  .mk pair equalResponses
    (capability.remove previous pair.first pair.second pair.typesEqual
      equalResponses)
    rfl
    (capability.removeStrict previous pair.first pair.second pair.typesEqual
      equalResponses)

end Hypostructure.CT8
