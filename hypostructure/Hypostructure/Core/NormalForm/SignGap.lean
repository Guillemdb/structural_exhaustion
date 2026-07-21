import Hypostructure.Core.Budget.Resource
import Hypostructure.Core.Closure
import Hypostructure.Core.Compactness.Extraction
import Hypostructure.Core.Residual.Decision

/-!
# Sign/gap normal form

The sign/gap executor owns the exhaustive four-way classification of one
normalized predecessor-owned family.  The domain registers scalar forms, an
exact comparison partition, and compactness persistence.  Core selects the
branch, closes the strict estimate directly, or emits the exact feeding,
equality, or minimizing residual without an application-authored outcome.
-/

namespace Hypostructure.Core.NormalForm.SignGap

open Hypostructure.Core

universe uAmbient uBranch uSequence uLimit uTopology uExtracted uResource
  uPrevious uEquality uMinimizing

/-- Strict comparison in the preorder registered by a resource budget. -/
def StrictlyBelow (budget : ResourceBudget) (lower upper : budget.Resource) :
    Prop :=
  budget.le lower upper ∧ Not (budget.le upper lower)

/-- Scalar forms and normalization evidence read from one literal predecessor
family. -/
structure Data {P : Problem.{uAmbient, uBranch}}
    (extraction : CompactExtraction.{uAmbient, uBranch, uSequence, uLimit,
      uTopology, uExtracted} P)
    (budget : ResourceBudget.{uResource}) (Previous : Type uPrevious) where
  family : Residual.Query Previous fun _previous => extraction.Sequence
  loss : (previous : Previous) -> extraction.Sequence -> budget.Resource
  readout : (previous : Previous) -> extraction.Sequence -> budget.Resource
  gap : (previous : Previous) -> extraction.Sequence -> budget.Resource
  Normalized : (previous : Previous) -> extraction.Sequence -> Prop
  normalized : forall previous,
    Normalized previous (family.read previous)
  lossNonnegative : forall previous,
    budget.le budget.zero (loss previous (family.read previous))
  readoutPositive : forall previous,
    StrictlyBelow budget budget.zero
      (readout previous (family.read previous))
  gapNonnegative : forall previous,
    budget.le budget.zero (gap previous (family.read previous))

namespace Data

variable {P : Problem.{uAmbient, uBranch}}
  {extraction : CompactExtraction.{uAmbient, uBranch, uSequence, uLimit,
    uTopology, uExtracted} P}
  {budget : ResourceBudget.{uResource}} {Previous : Type uPrevious}
  (data : Data extraction budget Previous)

/-- The exact represented family queried from the predecessor ledger. -/
abbrev familyAt (previous : Previous) : extraction.Sequence :=
  data.family.read previous

/-- Canonical scalar evidence for a strict/subcritical comparison. -/
def SubcriticalScalarEvidence (previous : Previous) : Prop :=
  StrictlyBelow budget
      (data.readout previous (data.familyAt previous))
      (data.loss previous (data.familyAt previous)) ∨
    StrictlyBelow budget budget.zero
      (data.gap previous (data.familyAt previous))

/-- Canonical scalar evidence for supercritical feeding. -/
def FeedingScalarEvidence (previous : Previous) : Prop :=
  StrictlyBelow budget
    (data.loss previous (data.familyAt previous))
    (data.readout previous (data.familyAt previous))

/-- Canonical scalar equality evidence. -/
def EqualityScalarEvidence (previous : Previous) : Prop :=
  data.loss previous (data.familyAt previous) =
    data.readout previous (data.familyAt previous)

/-- Canonical zero lower-gap evidence. -/
def ZeroGapScalarEvidence (previous : Previous) : Prop :=
  data.gap previous (data.familyAt previous) = budget.zero

end Data

/-- An exact, disjoint, exhaustive comparison theorem for the registered
forms.  Deciders are supplied for the first three propositions; the final
zero-gap branch is derived from exhaustiveness, never selected by a caller. -/
structure ExactComparison
    {P : Problem.{uAmbient, uBranch}}
    {extraction : CompactExtraction.{uAmbient, uBranch, uSequence, uLimit,
      uTopology, uExtracted} P}
    {budget : ResourceBudget.{uResource}} {Previous : Type uPrevious}
    (data : Data extraction budget Previous) where
  Subcritical : Previous -> Prop
  Feeding : Previous -> Prop
  Equality : Previous -> Prop
  ZeroGap : Previous -> Prop
  subcriticalDecidable : (previous : Previous) ->
    Decidable (Subcritical previous)
  feedingDecidable : (previous : Previous) -> Decidable (Feeding previous)
  equalityDecidable : (previous : Previous) -> Decidable (Equality previous)
  subcriticalSound : forall {previous}, Subcritical previous ->
    data.SubcriticalScalarEvidence previous
  feedingSound : forall {previous}, Feeding previous ->
    data.FeedingScalarEvidence previous
  equalitySound : forall {previous}, Equality previous ->
    data.EqualityScalarEvidence previous
  zeroGapSound : forall {previous}, ZeroGap previous ->
    data.ZeroGapScalarEvidence previous
  exhaustive : forall previous,
    Subcritical previous ∨ Feeding previous ∨ Equality previous ∨
      ZeroGap previous
  subcriticalDisjoint : forall {previous}, Subcritical previous ->
    Not (Feeding previous ∨ Equality previous ∨ ZeroGap previous)
  feedingDisjoint : forall {previous}, Feeding previous ->
    Not (Equality previous ∨ ZeroGap previous)
  equalityDisjoint : forall {previous}, Equality previous ->
    Not (ZeroGap previous)

namespace ExactComparison

variable {P : Problem.{uAmbient, uBranch}}
  {extraction : CompactExtraction.{uAmbient, uBranch, uSequence, uLimit,
    uTopology, uExtracted} P}
  {budget : ResourceBudget.{uResource}} {Previous : Type uPrevious}
  {data : Data extraction budget Previous}
  (comparison : ExactComparison data)

/-- The fourth branch follows from the exact partition after three Core
decisions miss. -/
theorem zeroGap_of_remainder {previous : Previous}
    (notSubcritical : Not (comparison.Subcritical previous))
    (notFeeding : Not (comparison.Feeding previous))
    (notEquality : Not (comparison.Equality previous)) :
    comparison.ZeroGap previous := by
  rcases comparison.exhaustive previous with
      subcritical | feeding | equality | zeroGap
  · exact (notSubcritical subcritical).elim
  · exact (notFeeding feeding).elim
  · exact (notEquality equality).elim
  · exact zeroGap

end ExactComparison

/-- Complete registered capability for one sign/gap module.  Equality and
zero-gap branches retain distinct obstruction predicates through the same
registered compact extraction. -/
structure Profile
    {P : Problem.{uAmbient, uBranch}}
    (extraction : CompactExtraction.{uAmbient, uBranch, uSequence, uLimit,
      uTopology, uExtracted} P)
    (budget : ResourceBudget.{uResource}) (Previous : Type uPrevious) where
  data : Data extraction budget Previous
  comparison : ExactComparison data
  Estimate : Previous -> Prop
  estimate : forall {previous}, comparison.Subcritical previous ->
    Estimate previous
  EqualityRetained : P.Ambient -> Sort uEquality
  MinimizingRetained : P.Ambient -> Sort uMinimizing
  baselineClosed : extraction.BaselineClosed
  equalityPersistent :
    extraction.ObstructionPersistent EqualityRetained
  minimizingPersistent :
    extraction.ObstructionPersistent MinimizingRetained
  equalityInput : forall (previous : Previous),
    comparison.Equality previous ->
      extraction.RetainedInput EqualityRetained (data.familyAt previous)
  minimizingInput : forall (previous : Previous),
    comparison.ZeroGap previous ->
      extraction.RetainedInput MinimizingRetained (data.familyAt previous)

/-- Framework evidence selected by the nested Core decisions. -/
inductive Evidence
    {P : Problem.{uAmbient, uBranch}}
    {extraction : CompactExtraction.{uAmbient, uBranch, uSequence, uLimit,
      uTopology, uExtracted} P}
    {budget : ResourceBudget.{uResource}} {Previous : Type uPrevious}
    {data : Data extraction budget Previous}
    (comparison : ExactComparison data) (previous : Previous) where
  | subcritical (proof : comparison.Subcritical previous)
  | feeding (proof : comparison.Feeding previous)
  | equality (proof : comparison.Equality previous)
  | zeroGap (proof : comparison.ZeroGap previous)

/-- Classify by three framework decisions and the certified exhaustive
remainder. -/
def classify
    {P : Problem.{uAmbient, uBranch}}
    {extraction : CompactExtraction.{uAmbient, uBranch, uSequence, uLimit,
      uTopology, uExtracted} P}
    {budget : ResourceBudget.{uResource}} {Previous : Type uPrevious}
    {data : Data extraction budget Previous}
    (comparison : ExactComparison data) (previous : Previous) :
    Evidence comparison previous := by
  let subcriticalDecision :=
    (Residual.Decision.Node.complement comparison.Subcritical
      comparison.subcriticalDecidable).run previous
  match subcriticalBranch : subcriticalDecision.added with
  | .yesBranch subcritical => exact .subcritical subcritical
  | .noBranch notSubcritical =>
      let feedingDecision :=
        (Residual.Decision.Node.complement comparison.Feeding
          comparison.feedingDecidable).run previous
      match feedingBranch : feedingDecision.added with
      | .yesBranch feeding => exact .feeding feeding
      | .noBranch notFeeding =>
          let equalityDecision :=
            (Residual.Decision.Node.complement comparison.Equality
              comparison.equalityDecidable).run previous
          match equalityBranch : equalityDecision.added with
          | .yesBranch equality => exact .equality equality
          | .noBranch notEquality =>
              exact .zeroGap
                (comparison.zeroGap_of_remainder notSubcritical notFeeding
                  notEquality)

/-- Branch payloads are indexed by the evidence selected by Core. -/
inductive Payload
    {P : Problem.{uAmbient, uBranch}}
    {extraction : CompactExtraction.{uAmbient, uBranch, uSequence, uLimit,
      uTopology, uExtracted} P}
    {budget : ResourceBudget.{uResource}} {Previous : Type uPrevious}
    (profile : Profile.{uAmbient, uBranch, uSequence, uLimit, uTopology,
      uExtracted, uResource, uPrevious, uEquality, uMinimizing}
      extraction budget Previous)
    (previous : Previous) : Evidence profile.comparison previous ->
      Type (max (max uEquality uExtracted) uMinimizing) where
  | subcritical {proof : profile.comparison.Subcritical previous}
      (result : Closure.Result (profile.Estimate previous)) :
      Payload profile previous (.subcritical proof)
  | feeding {proof : profile.comparison.Feeding previous} :
      Payload profile previous (.feeding proof)
  | equality {proof : profile.comparison.Equality previous}
      (descendant : extraction.Descendant profile.EqualityRetained
        (profile.data.familyAt previous)) :
      Payload profile previous (.equality proof)
  | zeroGap {proof : profile.comparison.ZeroGap previous}
      (descendant : extraction.Descendant profile.MinimizingRetained
        (profile.data.familyAt previous)) :
      Payload profile previous (.zeroGap proof)

/-- The sole value appended by a sign/gap node.  Its constructor is private,
so applications cannot pair a selected branch with an unrelated payload. -/
structure Output
    {P : Problem.{uAmbient, uBranch}}
    {extraction : CompactExtraction.{uAmbient, uBranch, uSequence, uLimit,
      uTopology, uExtracted} P}
    {budget : ResourceBudget.{uResource}} {Previous : Type uPrevious}
    (profile : Profile.{uAmbient, uBranch, uSequence, uLimit, uTopology,
      uExtracted, uResource, uPrevious, uEquality, uMinimizing}
      extraction budget Previous)
    (previous : Previous) where
  private mk ::
  evidence : Evidence profile.comparison previous
  payload : Payload profile previous evidence

/-- Build the branch payload selected by the exact comparison executor. -/
def output
    {P : Problem.{uAmbient, uBranch}}
    {extraction : CompactExtraction.{uAmbient, uBranch, uSequence, uLimit,
      uTopology, uExtracted} P}
    {budget : ResourceBudget.{uResource}} {Previous : Type uPrevious}
    (profile : Profile.{uAmbient, uBranch, uSequence, uLimit, uTopology,
      uExtracted, uResource, uPrevious, uEquality, uMinimizing}
      extraction budget Previous)
    (previous : Previous) : Output profile previous := by
  let evidence := classify profile.comparison previous
  refine ⟨evidence, ?_⟩
  cases evidence with
  | subcritical proof =>
      exact .subcritical
        (Closure.Result.direct
          (.certificate (profile.estimate proof)))
  | feeding _proof =>
      exact .feeding
  | equality proof =>
      exact .equality
        (extraction.descend profile.baselineClosed
          profile.equalityPersistent (profile.data.familyAt previous)
          (profile.equalityInput previous proof))
  | zeroGap proof =>
      exact .zeroGap
        (extraction.descend profile.baselineClosed
          profile.minimizingPersistent (profile.data.familyAt previous)
          (profile.minimizingInput previous proof))

/-- The four semantic terminals of the sign/gap normal form. -/
inductive Terminal where
  | subcritical
  | feeding
  | equality
  | zeroGap
  deriving DecidableEq, Repr

namespace Output

variable {P : Problem.{uAmbient, uBranch}}
  {extraction : CompactExtraction.{uAmbient, uBranch, uSequence, uLimit,
    uTopology, uExtracted} P}
  {budget : ResourceBudget.{uResource}} {Previous : Type uPrevious}
  {profile : Profile.{uAmbient, uBranch, uSequence, uLimit, uTopology,
    uExtracted, uResource, uPrevious, uEquality, uMinimizing}
    extraction budget Previous}
  {previous : Previous}

/-- Observable terminal derived from the framework-owned evidence. -/
def terminal (result : Output profile previous) : Terminal :=
  match result.evidence with
  | .subcritical _ => .subcritical
  | .feeding _ => .feeding
  | .equality _ => .equality
  | .zeroGap _ => .zeroGap

end Output

/-- Sign/gap execution is an ordinary Core data-bearing node. -/
def node
    {P : Problem.{uAmbient, uBranch}}
    {extraction : CompactExtraction.{uAmbient, uBranch, uSequence, uLimit,
      uTopology, uExtracted} P}
    {budget : ResourceBudget.{uResource}} {Previous : Type uPrevious}
    (profile : Profile.{uAmbient, uBranch, uSequence, uLimit, uTopology,
      uExtracted, uResource, uPrevious, uEquality, uMinimizing}
      extraction budget Previous) :
    Residual.StageNode Previous fun previous => Output profile previous :=
  Residual.StageNode.create (output profile)

/-- Execute the sign/gap normal form on the literal incoming ledger. -/
def run
    {P : Problem.{uAmbient, uBranch}}
    {extraction : CompactExtraction.{uAmbient, uBranch, uSequence, uLimit,
      uTopology, uExtracted} P}
    {budget : ResourceBudget.{uResource}} {Previous : Type uPrevious}
    (profile : Profile.{uAmbient, uBranch, uSequence, uLimit, uTopology,
      uExtracted, uResource, uPrevious, uEquality, uMinimizing}
      extraction budget Previous)
    (previous : Previous) :
    Residual.Ledger.Extension Previous fun current => Output profile current :=
  (node profile).run previous

@[simp] theorem run_previous
    {P : Problem.{uAmbient, uBranch}}
    {extraction : CompactExtraction.{uAmbient, uBranch, uSequence, uLimit,
      uTopology, uExtracted} P}
    {budget : ResourceBudget.{uResource}} {Previous : Type uPrevious}
    (profile : Profile.{uAmbient, uBranch, uSequence, uLimit, uTopology,
      uExtracted, uResource, uPrevious, uEquality, uMinimizing}
      extraction budget Previous)
    (previous : Previous) : (run profile previous).previous = previous :=
  rfl

end Hypostructure.Core.NormalForm.SignGap
