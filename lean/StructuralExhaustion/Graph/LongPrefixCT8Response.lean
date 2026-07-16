import StructuralExhaustion.CT8.Automation
import StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier

namespace StructuralExhaustion.Graph.LongPrefixCT8Response

open StructuralExhaustion

universe u uAmbient uBranch

variable {V : Type u} {object : FiniteObject V}
variable {observed : LongPrefixObservedLabel.Input object}

abbrev Source (object : FiniteObject V)
    (observed : LongPrefixObservedLabel.Input object) :=
  LongPrefixCompatibleResponseFrontier.Source (input := observed)

/-- The response family is exactly the first thirty-six literal support
positions already inspected by the four predecessor blocks. -/
abbrev ResponseContext := Fin 36

@[implicit_reducible]
def responseContexts : FinEnum ResponseContext := by infer_instance

@[simp]
theorem responseContexts_card : responseContexts.card = 36 :=
  @FinEnum.card_fin 36 responseContexts

/-- The two states are occurrences, not a vertex set: even equal vertex
values retain their distinct left/right positions in the collision. -/
inductive RetainedOccurrence
  | first
  | second
  deriving DecidableEq

@[implicit_reducible]
def retainedOccurrences : FinEnum RetainedOccurrence :=
  @FinEnum.ofNodupList RetainedOccurrence inferInstance [.first, .second]
    (by intro occurrence; cases occurrence <;> simp)
    (by simp)

noncomputable def firstVertex (source : Source object observed) : V :=
  source.fourthSource.thirdSource.extendedSource.localSource.degreeSource.firstVertex

noncomputable def secondVertex (source : Source object observed) : V :=
  source.fourthSource.thirdSource.extendedSource.localSource.degreeSource.secondVertex

noncomputable def stateVertex (source : Source object observed) : RetainedOccurrence → V
  | .first => firstVertex source
  | .second => secondVertex source

def supportPosition (source : Source object observed) (context : ResponseContext) :
    Fin observed.support.length :=
  ⟨context.1, lt_of_lt_of_le context.2 source.fourthSource.firstThirtySix⟩

def responseVertex (source : Source object observed) (context : ResponseContext) : V :=
  observed.support.get (supportPosition source context)

/-- Exact Boolean adjacency response on one of the 36 literal contexts. -/
noncomputable def response (source : Source object observed)
    (state : RetainedOccurrence) (context : ResponseContext) : Bool :=
  @decide (object.graph.Adj (stateVertex source state)
    (responseVertex source context))
    (object.input.decideAdj (stateVertex source state)
      (responseVertex source context))

/-- Provenance for a distinguishing response.  Each constructor retains the
actual first-hit object from its predecessor block and the exact offset into
`Fin 36`. -/
inductive DistinguishingResponse (source : Source object observed) where
  | first
      (mismatch : LongPrefixLocalClauseAlignment.FirstMismatch
        source.fourthSource.thirdSource.extendedSource.localSource)
      (context : ResponseContext)
      (contextExact : context.1 = mismatch.hit.value.1)
      (differs : response source .first context ≠ response source .second context)
  | second
      (mismatch : LongPrefixExtendedClauseAlignment.SecondMismatch
        source.fourthSource.thirdSource.extendedSource)
      (context : ResponseContext)
      (contextExact : context.1 = mismatch.hit.value.1 + 9)
      (differs : response source .first context ≠ response source .second context)
  | third
      (mismatch : LongPrefixThirdBlockClauseAlignment.ThirdMismatch
        source.fourthSource.thirdSource)
      (context : ResponseContext)
      (contextExact : context.1 = mismatch.hit.value.1 + 18)
      (differs : response source .first context ≠ response source .second context)
  | fourth
      (mismatch : LongPrefixFourthBlockClauseAlignment.FourthMismatch
        source.fourthSource)
      (context : ResponseContext)
      (contextExact : context.1 = mismatch.hit.value.1 + 27)
      (differs : response source .first context ≠ response source .second context)

private theorem decide_ne_of_not_iff {left right : Prop}
    (leftDecidable : Decidable left) (rightDecidable : Decidable right)
    (different : ¬(left ↔ right)) :
    @decide left leftDecidable ≠ @decide right rightDecidable := by
  simpa only [Bool.decide_coe, ne_eq, decide_eq_decide] using different

noncomputable def ofFirstMismatch (source : Source object observed)
    (mismatch : LongPrefixLocalClauseAlignment.FirstMismatch
      source.fourthSource.thirdSource.extendedSource.localSource) :
    DistinguishingResponse source := by
  let context : ResponseContext := ⟨mismatch.hit.value.1,
    lt_trans mismatch.hit.value.2 (by decide : 9 < 36)⟩
  refine .first mismatch context rfl ?_
  unfold response
  apply decide_ne_of_not_iff
  simpa [response, stateVertex, firstVertex, secondVertex, responseVertex,
    supportPosition, LongPrefixLocalClauseAlignment.profile,
    LongPrefixObservedLabel.vertex, LongPrefixObservedLabel.supportPosition]
    using mismatch.sound

noncomputable def ofSecondMismatch (source : Source object observed)
    (mismatch : LongPrefixExtendedClauseAlignment.SecondMismatch
      source.fourthSource.thirdSource.extendedSource) :
    DistinguishingResponse source := by
  let context : ResponseContext := ⟨mismatch.hit.value.1 + 9, by omega⟩
  refine .second mismatch context rfl ?_
  unfold response
  apply decide_ne_of_not_iff
  simpa [response, stateVertex, firstVertex, secondVertex, responseVertex,
    supportPosition, LongPrefixExtendedClauseAlignment.profile,
    LongPrefixExtendedClauseAlignment.vertex,
    LongPrefixExtendedClauseAlignment.supportPosition]
    using mismatch.sound

noncomputable def ofThirdMismatch (source : Source object observed)
    (mismatch : LongPrefixThirdBlockClauseAlignment.ThirdMismatch
      source.fourthSource.thirdSource) : DistinguishingResponse source := by
  let context : ResponseContext := ⟨mismatch.hit.value.1 + 18, by omega⟩
  refine .third mismatch context rfl ?_
  unfold response
  apply decide_ne_of_not_iff
  simpa [response, stateVertex, firstVertex, secondVertex, responseVertex,
    supportPosition, LongPrefixThirdBlockClauseAlignment.profile,
    LongPrefixThirdBlockClauseAlignment.vertex,
    LongPrefixThirdBlockClauseAlignment.supportPosition]
    using mismatch.sound

noncomputable def ofFourthMismatch (source : Source object observed)
    (mismatch : LongPrefixFourthBlockClauseAlignment.FourthMismatch
      source.fourthSource) : DistinguishingResponse source := by
  let context : ResponseContext := ⟨mismatch.hit.value.1 + 27, by omega⟩
  refine .fourth mismatch context rfl ?_
  unfold response
  apply decide_ne_of_not_iff
  simpa [response, stateVertex, firstVertex, secondVertex, responseVertex,
    supportPosition, LongPrefixFourthBlockClauseAlignment.profile,
    LongPrefixFourthBlockClauseAlignment.vertex,
    LongPrefixFourthBlockClauseAlignment.supportPosition]
    using mismatch.sound

/-- The exact full local type that a later CT8 capability must use.  Unlike
the coarse predecessor label, it retains the full ambient degree and marked
bit. -/
abbrev ExactType := Fin object.input.vertices.card × Bool

@[implicit_reducible]
def exactTypes : FinEnum (ExactType (object := object)) :=
  Core.Enumeration.prod (by infer_instance) Core.Enumeration.bool

noncomputable def markedBit (state : RetainedOccurrence)
    (source : Source object observed) : Bool := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact decide (stateVertex source state ∈ observed.marked)

noncomputable def exactType (source : Source object observed)
    (state : RetainedOccurrence) : ExactType (object := object) :=
  (⟨object.degree (stateVertex source state),
      object.degree_lt_vertexCount (stateVertex source state)⟩,
    markedBit state source)

inductive AlignedMissingProducer
  | completeD4D7ResponseSemantics
  | exactPairCertifiedReduction
  deriving DecidableEq, Repr

/-- Honest aligned-leaf boundary.  The four proofs establish equality on the
36 literal adjacency clauses only.  CT8 execution remains unavailable until
the manuscript-complete response semantics and a certified reduction indexed
by this exact retained pair are supplied. -/
structure AlignedCT8Requirement (source : Source object observed) where
  first : LongPrefixLocalClauseAlignment.Aligned
    source.fourthSource.thirdSource.extendedSource.localSource
  second : LongPrefixExtendedClauseAlignment.SecondAligned
    source.fourthSource.thirdSource.extendedSource
  third : LongPrefixThirdBlockClauseAlignment.ThirdAligned
    source.fourthSource.thirdSource
  fourth : LongPrefixFourthBlockClauseAlignment.FourthAligned
    source.fourthSource
  missing : List AlignedMissingProducer
  missingExact : missing =
    [.completeD4D7ResponseSemantics, .exactPairCertifiedReduction]

/-- Exact consumer of the five node-195 constructors.  All four mismatch
leaves become proved local separators; the aligned leaf stops at its two
honest CT8 producer requirements. -/
inductive Resolution (source : Source object observed)
  | distinguishing (result : DistinguishingResponse source)
  | aligned (requirement : AlignedCT8Requirement source)

noncomputable def resolve (source : Source object observed) :
    LongPrefixCompatibleResponseFrontier.Result source → Resolution source
  | .inheritedFirstMismatch mismatch _ =>
      .distinguishing (ofFirstMismatch source mismatch)
  | .inheritedSecondMismatch _first second _ =>
      .distinguishing (ofSecondMismatch source second)
  | .inheritedThirdMismatch _first _second third _ =>
      .distinguishing (ofThirdMismatch source third)
  | .fourthMismatch _first _second _third fourth _ =>
      .distinguishing (ofFourthMismatch source fourth)
  | .firstThirtySixAligned first second third fourth _ =>
      .aligned {
        first := first
        second := second
        third := third
        fourth := fourth
        missing := [.completeD4D7ResponseSemantics,
          .exactPairCertifiedReduction]
        missingExact := rfl
      }

/-- Reserved cost of the future aligned CT8 execution: one repeated-type
comparison and two adjacency evaluations at each of 36 literal contexts.
The present resolver does not execute this work. -/
def alignedReservedChecks : Nat := 73

theorem alignedReservedChecks_polynomial :
    alignedReservedChecks ≤ 73 * (object.input.vertices.card + 1) := by
  unfold alignedReservedChecks
  omega

end StructuralExhaustion.Graph.LongPrefixCT8Response
