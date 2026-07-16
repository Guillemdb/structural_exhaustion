import StructuralExhaustion.Graph.LongPrefixCT8Response

namespace StructuralExhaustion.Graph.LongPrefixAlignedDegreeGate

open StructuralExhaustion

universe u uAmbient uBranch

variable {V : Type u} {object : FiniteObject V}
variable {observed : LongPrefixObservedLabel.Input object}

abbrev Source := LongPrefixCT8Response.Source object observed

noncomputable abbrev degreeSource (source : Source (object := object)
    (observed := observed)) :=
  source.fourthSource.thirdSource.extendedSource.localSource.degreeSource

noncomputable abbrev degreeResult (source : Source (object := object)
    (observed := observed)) :=
  source.fourthSource.thirdSource.extendedSource.localSource.degreeResult

/-- The two retained occurrences in their inherited left-to-right order. -/
def sequence : List LongPrefixCT8Response.RetainedOccurrence :=
  [.first, .second]

/-- CT8 capability for the literal 36-clause response only.  This capability
does not assert that those clauses are the manuscript's complete D4--D7
semantics and is not executable until a certified removal is supplied. -/
noncomputable abbrev literalCapability
    (P : Core.Problem.{uAmbient, uBranch})
    (source : Source (object := object) (observed := observed)) :
    CT8.Capability P where
  State := LongPrefixCT8Response.RetainedOccurrence
  ExactType := LongPrefixCT8Response.ExactType (object := object)
  ResponseContext := LongPrefixCT8Response.ResponseContext
  exactTypes := LongPrefixCT8Response.exactTypes
  responseContexts := LongPrefixCT8Response.responseContexts
  exactType := LongPrefixCT8Response.exactType source
  response := LongPrefixCT8Response.response source

/-- On the exact-degree constructor, the already retained marked-bit equality
upgrades the coarse collision to equality of the full CT8 exact type. -/
theorem exactType_eq_of_exactDegree
    (source : Source (object := object) (observed := observed))
    (residual : LongPrefixDegreeRefinement.ExactDegreeResidual
      (degreeSource source)) :
    LongPrefixCT8Response.exactType source .first =
      LongPrefixCT8Response.exactType source .second := by
  apply Prod.ext
  · apply Fin.ext
    exact residual.degreeEqual
  · simpa [LongPrefixCT8Response.exactType,
      LongPrefixCT8Response.markedBit, LongPrefixCT8Response.stateVertex,
      LongPrefixCT8Response.firstVertex, LongPrefixCT8Response.secondVertex,
      LongPrefixDegreeRefinement.Source.firstVertex,
      LongPrefixDegreeRefinement.Source.secondVertex,
      LongPrefixObservedLabel.markedBit] using residual.markedEqual

/-- A genuine full-degree gap prevents the retained pair from being a CT8
exact-type repetition, independently of its marked bit. -/
theorem exactType_ne_of_degreeGap
    (source : Source (object := object) (observed := observed))
    (residual : LongPrefixDegreeRefinement.CongruentDegreeGapResidual
      (degreeSource source)) :
    LongPrefixCT8Response.exactType source .first ≠
      LongPrefixCT8Response.exactType source .second := by
  intro equal
  apply residual.degreeNotEqual
  exact congrArg (fun exact : LongPrefixCT8Response.ExactType (object := object) =>
    exact.1.1) equal

/-- Exact CT8 repetition data available only on the exact-degree branch. -/
structure ExactPair
    (P : Core.Problem.{uAmbient, uBranch})
    (source : Source (object := object) (observed := observed))
    (requirement : LongPrefixCT8Response.AlignedCT8Requirement source) where
  aligned : LongPrefixCT8Response.AlignedCT8Requirement source
  alignedExact : aligned = requirement
  degree : LongPrefixDegreeRefinement.ExactDegreeResidual (degreeSource source)
  exactTypeEqual :
    LongPrefixCT8Response.exactType source .first =
      LongPrefixCT8Response.exactType source .second
  pair : CT8.OrderedRepeatedPair (literalCapability P source) sequence

/-- The degree-gap branch is not a repeated exact type and must leave CT8.
All four local alignment proofs remain available through `aligned`. -/
structure DegreeGap
    (source : Source (object := object) (observed := observed))
    (requirement : LongPrefixCT8Response.AlignedCT8Requirement source) where
  aligned : LongPrefixCT8Response.AlignedCT8Requirement source
  alignedExact : aligned = requirement
  gap : LongPrefixDegreeRefinement.CongruentDegreeGapResidual
    (degreeSource source)
  exactTypeNotEqual :
    LongPrefixCT8Response.exactType source .first ≠
      LongPrefixCT8Response.exactType source .second

inductive Result
    (P : Core.Problem.{uAmbient, uBranch})
    (source : Source (object := object) (observed := observed))
    (requirement : LongPrefixCT8Response.AlignedCT8Requirement source) where
  | degreeGap (residual : DegreeGap source requirement)
  | exactPair (residual : ExactPair P source requirement)

/-- Inspect exactly the retained node-179 constructor.  No response coordinate
is evaluated and neither D4--D7 semantics nor a removal is constructed. -/
noncomputable def run
    (P : Core.Problem.{uAmbient, uBranch})
    (source : Source (object := object) (observed := observed))
    (requirement : LongPrefixCT8Response.AlignedCT8Requirement source) :
    Result P source requirement := by
  cases result : degreeResult source with
  | congruentDegreeGap gap =>
      exact .degreeGap
        ⟨requirement, rfl, gap, exactType_ne_of_degreeGap source gap⟩
  | exactDegree degree =>
      have equal := exactType_eq_of_exactDegree source degree
      let pair : CT8.OrderedRepeatedPair (literalCapability P source) sequence :=
        .here .second (by simp) equal
      exact .exactPair ⟨requirement, rfl, degree, equal, pair⟩

theorem run_exhaustive
    (P : Core.Problem.{uAmbient, uBranch})
    (source : Source (object := object) (observed := observed))
    (requirement : LongPrefixCT8Response.AlignedCT8Requirement source) :
    (∃ residual, run P source requirement = .degreeGap residual) ∨
      (∃ residual, run P source requirement = .exactPair residual) := by
  cases equation : run P source requirement with
  | degreeGap residual => exact Or.inl ⟨residual, rfl⟩
  | exactPair residual => exact Or.inr ⟨residual, rfl⟩

/-- One constructor inspection; no finite response scan is performed. -/
def visibleChecks : Nat := 1

theorem visibleChecks_polynomial :
    visibleChecks ≤ object.input.vertices.card + 1 := by
  unfold visibleChecks
  omega

end StructuralExhaustion.Graph.LongPrefixAlignedDegreeGate
