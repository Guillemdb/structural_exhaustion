import StructuralExhaustion.Core.LocalBooleanRealization

namespace StructuralExhaustion.Core.FiniteEntropyRankRouting

universe uCoordinate uState uRank

/-!
# Finite realization/rank/large-budget routing

This runner keeps three logically different conclusions separate.  Complete
Boolean realization is accepted only from the exhaustive local classifier.
If realization fails, an independently decidable repetition predicate may
produce its own rank payload.  Otherwise the exact missing assignment and the
failure of repetition are retained as the large-budget residual.
-/

/-- Author data for one already-defined finite response system.  The rank
bridge is used only after `Repetitive` has been decided true. -/
structure Profile where
  system : LocalBooleanRealization.System.{uCoordinate, uState}
  Repetitive : Prop
  repetitiveDecidable : Decidable Repetitive
  RankPayload : Type uRank
  rankOfRepetitive : Repetitive → RankPayload

namespace Profile

variable (profile : Profile)

structure EntropyRoute where
  certificate : profile.system.HotCertificate
  stateBound :
    2 ^ profile.system.coordinates.card ≤ profile.system.states.card

structure RepetitiveRankRoute where
  repetitive : profile.Repetitive
  rank : profile.RankPayload

structure LargeBudgetResidual where
  cold : profile.system.ColdResidual
  notRepetitive : ¬profile.Repetitive

inductive Outcome where
  | entropy (route : profile.EntropyRoute)
  | repetitiveRank (route : profile.RepetitiveRankRoute)
  | largeBudget (residual : profile.LargeBudgetResidual)

/-- Constructor-indexed semantics of one routing outcome.  Keeping this as a
named predicate lets applications retain totality without repeatedly
normalizing a large concrete profile inside a dependent `match`. -/
def Outcome.Valid : profile.Outcome → Prop
  | .entropy _route =>
      2 ^ profile.system.coordinates.card ≤ profile.system.states.card
  | .repetitiveRank _route => profile.Repetitive
  | .largeBudget residual =>
      (∀ state, profile.system.value state ≠ residual.cold.assignment) ∧
        ¬profile.Repetitive

/-- Execute the Boolean classifier first, and inspect repetition only on its
cold side.  No caller supplies a terminal tag. -/
def run : profile.Outcome :=
  match profile.system.classify with
  | .hot certificate =>
      .entropy ⟨certificate, certificate.two_pow_coordinateCard_le_stateCard⟩
  | .cold cold =>
      match profile.repetitiveDecidable with
      | .isTrue repetitive =>
          .repetitiveRank ⟨repetitive, profile.rankOfRepetitive repetitive⟩
      | .isFalse notRepetitive =>
          .largeBudget ⟨cold, notRepetitive⟩

/-- Semantic totality of the computed three-way route. -/
theorem run_total :
    match profile.run with
    | .entropy route =>
        2 ^ profile.system.coordinates.card ≤ profile.system.states.card
    | .repetitiveRank route => profile.Repetitive
    | .largeBudget residual =>
        (∀ state, profile.system.value state ≠ residual.cold.assignment) ∧
          ¬profile.Repetitive := by
  unfold run
  cases profile.system.classify with
  | hot certificate => exact certificate.two_pow_coordinateCard_le_stateCard
  | cold cold =>
      cases profile.repetitiveDecidable with
      | isTrue repetitive => exact repetitive
      | isFalse notRepetitive => exact ⟨cold.noState, notRepetitive⟩

/-- Predicate-packaged form of `run_total`, intended for concrete profiles
whose definitions are expensive to normalize. -/
theorem run_valid : profile.run.Valid :=
  profile.run_total

/-- The two surviving outcomes when an application proves that its concrete
entropy-certificate type is empty. -/
inductive NonEntropyOutcome where
  | repetitiveRank (route : profile.RepetitiveRankRoute)
  | largeBudget (residual : profile.LargeBudgetResidual)

/-- Eliminate the entropy constructor without exposing dependent equalities
between a large concrete runner and its constructors. -/
def runWithoutEntropy (entropyImpossible : profile.EntropyRoute → False) :
    profile.NonEntropyOutcome :=
  match profile.run with
  | .entropy route => (entropyImpossible route).elim
  | .repetitiveRank route => .repetitiveRank route
  | .largeBudget residual => .largeBudget residual

end Profile

end StructuralExhaustion.Core.FiniteEntropyRankRouting
