import StructuralExhaustion.Graph.LongPrefixFourthBlockClauseAlignment

namespace StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier

open StructuralExhaustion

universe u

/-!
# Honest semantic frontier after thirty-six literal adjacency clauses

The predecessor has compared only four fixed blocks of actual adjacency
clauses.  A mismatch is not yet a distinguishing response context, and full
agreement is not yet a compatible response family or a CT8 input.  This file
therefore retains the exact dependent predecessor constructor and records the
missing graph-owned obligations.  It accepts no response function, Boolean,
context family, removal operation, or smaller-object certificate.
-/

variable {V : Type u} {object : FiniteObject V}
variable {input : LongPrefixObservedLabel.Input object}

namespace Fourth
export LongPrefixFourthBlockClauseAlignment
  (Source Result FourthMismatch FourthAligned)
end Fourth

structure Source where
  fourthSource : Fourth.Source (input := input)
  fourthResult : Fourth.Result fourthSource
  fourthResultExact : fourthResult =
    LongPrefixFourthBlockClauseAlignment.run fourthSource

inductive Requirement
  | localMismatchToDistinguishingContext
  | distinguishingContextProvenance
  | compatibleResponseFamily
  | responseProvenance
  | certifiedCT8InputOrDistinguishingContext
  deriving DecidableEq, Repr

def required {source : Source (input := input)} :
    Fourth.Result source.fourthSource → List Requirement
  | .inheritedFirstMismatch .. =>
      [.localMismatchToDistinguishingContext, .distinguishingContextProvenance]
  | .inheritedSecondMismatch .. =>
      [.localMismatchToDistinguishingContext, .distinguishingContextProvenance]
  | .inheritedThirdMismatch .. =>
      [.localMismatchToDistinguishingContext, .distinguishingContextProvenance]
  | .fourthMismatch .. =>
      [.localMismatchToDistinguishingContext, .distinguishingContextProvenance]
  | .firstThirtySixAligned .. =>
      [.compatibleResponseFamily, .responseProvenance,
        .certifiedCT8InputOrDistinguishingContext]

theorem required_nodup {source : Source (input := input)}
    (result : Fourth.Result source.fourthSource) :
    (required result).Nodup := by
  cases result <;> simp [required]

/-- An exact predecessor payload together with only its still-open semantic
requirements. -/
structure Pending (source : Source (input := input))
    (result : Fourth.Result source.fourthSource) where
  retained : Fourth.Result source.fourthSource
  retainedExact : retained = result
  needs : List Requirement
  needsExact : needs = required result
  needsNodup : needs.Nodup

def pending (source : Source (input := input))
    (result : Fourth.Result source.fourthSource) : Pending source result where
  retained := result
  retainedExact := rfl
  needs := required result
  needsExact := rfl
  needsNodup := required_nodup result

inductive Result (source : Source (input := input)) where
  | inheritedFirstMismatch
      (mismatch : LongPrefixLocalClauseAlignment.FirstMismatch
        source.fourthSource.thirdSource.extendedSource.localSource)
      (obligation : Pending source (.inheritedFirstMismatch mismatch))
  | inheritedSecondMismatch
      (first : LongPrefixLocalClauseAlignment.Aligned
        source.fourthSource.thirdSource.extendedSource.localSource)
      (second : LongPrefixExtendedClauseAlignment.SecondMismatch
        source.fourthSource.thirdSource.extendedSource)
      (obligation : Pending source (.inheritedSecondMismatch first second))
  | inheritedThirdMismatch
      (first : LongPrefixLocalClauseAlignment.Aligned
        source.fourthSource.thirdSource.extendedSource.localSource)
      (second : LongPrefixExtendedClauseAlignment.SecondAligned
        source.fourthSource.thirdSource.extendedSource)
      (third : LongPrefixThirdBlockClauseAlignment.ThirdMismatch
        source.fourthSource.thirdSource)
      (obligation : Pending source (.inheritedThirdMismatch first second third))
  | fourthMismatch
      (first : LongPrefixLocalClauseAlignment.Aligned
        source.fourthSource.thirdSource.extendedSource.localSource)
      (second : LongPrefixExtendedClauseAlignment.SecondAligned
        source.fourthSource.thirdSource.extendedSource)
      (third : LongPrefixThirdBlockClauseAlignment.ThirdAligned
        source.fourthSource.thirdSource)
      (fourth : Fourth.FourthMismatch source.fourthSource)
      (obligation : Pending source (.fourthMismatch first second third fourth))
  | firstThirtySixAligned
      (first : LongPrefixLocalClauseAlignment.Aligned
        source.fourthSource.thirdSource.extendedSource.localSource)
      (second : LongPrefixExtendedClauseAlignment.SecondAligned
        source.fourthSource.thirdSource.extendedSource)
      (third : LongPrefixThirdBlockClauseAlignment.ThirdAligned
        source.fourthSource.thirdSource)
      (fourth : Fourth.FourthAligned source.fourthSource)
      (obligation : Pending source (.firstThirtySixAligned first second third fourth))

def Result.predecessor {source : Source (input := input)} :
    Result source → Fourth.Result source.fourthSource
  | .inheritedFirstMismatch mismatch _ => .inheritedFirstMismatch mismatch
  | .inheritedSecondMismatch first second _ =>
      .inheritedSecondMismatch first second
  | .inheritedThirdMismatch first second third _ =>
      .inheritedThirdMismatch first second third
  | .fourthMismatch first second third fourth _ =>
      .fourthMismatch first second third fourth
  | .firstThirtySixAligned first second third fourth _ =>
      .firstThirtySixAligned first second third fourth

def lift (source : Source (input := input))
    (result : Fourth.Result source.fourthSource) : Result source :=
  match result with
  | .inheritedFirstMismatch mismatch =>
      .inheritedFirstMismatch mismatch (pending source _)
  | .inheritedSecondMismatch first second =>
      .inheritedSecondMismatch first second (pending source _)
  | .inheritedThirdMismatch first second third =>
      .inheritedThirdMismatch first second third (pending source _)
  | .fourthMismatch first second third fourth =>
      .fourthMismatch first second third fourth (pending source _)
  | .firstThirtySixAligned first second third fourth =>
      .firstThirtySixAligned first second third fourth (pending source _)

def run (source : Source (input := input)) : Result source :=
  lift source source.fourthResult

theorem lift_predecessor (source : Source (input := input))
    (result : Fourth.Result source.fourthSource) :
    (lift source result).predecessor = result := by
  cases result <;> rfl

theorem run_predecessor (source : Source (input := input)) :
    (run source).predecessor = source.fourthResult :=
  lift_predecessor source source.fourthResult

theorem run_exhaustive (source : Source (input := input)) :
    (∃ mismatch obligation,
      run source = .inheritedFirstMismatch mismatch obligation) ∨
    (∃ first second obligation,
      run source = .inheritedSecondMismatch first second obligation) ∨
    (∃ first second third obligation,
      run source = .inheritedThirdMismatch first second third obligation) ∨
    (∃ first second third fourth obligation,
      run source = .fourthMismatch first second third fourth obligation) ∨
    (∃ first second third fourth obligation,
      run source = .firstThirtySixAligned first second third fourth obligation) := by
  cases equation : run source with
  | inheritedFirstMismatch mismatch obligation =>
      exact Or.inl ⟨mismatch, obligation, rfl⟩
  | inheritedSecondMismatch first second obligation =>
      exact Or.inr (Or.inl ⟨first, second, obligation, rfl⟩)
  | inheritedThirdMismatch first second third obligation =>
      exact Or.inr (Or.inr (Or.inl ⟨first, second, third, obligation, rfl⟩))
  | fourthMismatch first second third fourth obligation =>
      exact Or.inr (Or.inr (Or.inr
        (Or.inl ⟨first, second, third, fourth, obligation, rfl⟩)))
  | firstThirtySixAligned first second third fourth obligation =>
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨first, second, third, fourth, obligation, rfl⟩)))

theorem source_fourth_exact (source : Source (input := input)) :
    source.fourthResult =
      LongPrefixFourthBlockClauseAlignment.run source.fourthSource :=
  source.fourthResultExact

def requiredInputs (source : Source (input := input)) : Nat :=
  (required source.fourthResult).length

theorem required_length_le_three {source : Source (input := input)}
    (result : Fourth.Result source.fourthSource) :
    (required result).length ≤ 3 := by
  cases result <;> simp [required]

theorem requiredInputs_le_three (source : Source (input := input)) :
    requiredInputs source ≤ 3 :=
  required_length_le_three source.fourthResult

/-- Only the already-computed predecessor constructor is inspected. -/
def visibleChecks : Nat := 1

theorem visibleChecks_constant : visibleChecks ≤ 1 := le_rfl

end StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier
