import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Core.WorkBudget

namespace StructuralExhaustion.Core.FiniteBlockerLedger

universe uPair uCandidate

/-!
# Local canonical blocker search

This layer is intentionally pair-local.  An application supplies one finite
candidate list for one pair and a decidable blocker predicate.  The framework
returns the first blocker in that declared order, or a proof that every
declared candidate is absent.  It never constructs the ambient pair universe.
-/

structure Profile (Pair : Type uPair) (Candidate : Type uCandidate) where
  candidates : Pair → Core.OrderedCollection Candidate
  Blocks : Pair → Candidate → Prop
  blocksDecidable : (pair : Pair) → (candidate : Candidate) →
    Decidable (Blocks pair candidate)

namespace Profile

variable {Pair : Type uPair} {Candidate : Type uCandidate}
variable (profile : Profile Pair Candidate)

/-- Execute the canonical first-blocker scan for one supplied pair. -/
def run (pair : Pair) :=
  Core.FiniteSearch.firstOnList (profile.candidates pair).values
    (profile.Blocks pair) (profile.blocksDecidable pair)

/-- Every blocked result carries the first valid blocker and a proof that all
earlier declared candidates fail. -/
theorem found_sound (pair : Pair)
    (hit : Core.FiniteSearch.FirstHit (profile.candidates pair).values
      (profile.Blocks pair)) :
    hit.value ∈ (profile.candidates pair).values ∧
      profile.Blocks pair hit.value ∧
      ∀ candidate ∈ hit.before, ¬profile.Blocks pair candidate :=
  ⟨hit.member, hit.holds, hit.beforeAbsent⟩

/-- The clear residual excludes every candidate in the exact local list. -/
theorem absent_sound (pair : Pair)
    (none : ∀ candidate : Candidate,
      candidate ∈ (profile.candidates pair).values →
        ¬profile.Blocks pair candidate) :
    ∀ candidate : Candidate,
      candidate ∈ (profile.candidates pair).values →
        ¬profile.Blocks pair candidate :=
  none

/-- Exhaustive local state space: a canonical first blocker or a clean local
residual. -/
theorem stateSpace (pair : Pair) :
    (∃ hit : Core.FiniteSearch.FirstHit (profile.candidates pair).values
        (profile.Blocks pair), profile.run pair = .found hit) ∨
      (∃ none : ∀ candidate : Candidate,
          candidate ∈ (profile.candidates pair).values →
            ¬profile.Blocks pair candidate,
        profile.run pair = .absent none) := by
  cases equation : profile.run pair with
  | found hit => exact Or.inl ⟨hit, rfl⟩
  | absent none => exact Or.inr ⟨none, rfl⟩

/-- One predicate check per declared local candidate. -/
def checks (pair : Pair) : Nat := (profile.candidates pair).values.length

theorem checks_linear (pair : Pair) :
    profile.checks pair ≤ (profile.candidates pair).values.length + 1 := by
  simp [checks]

end Profile

/-! ## Exact partition of a finite local-pair schedule -/

/-- A finite family of local blocker scans.  The candidate universe may vary
with the pair through `local.candidates`; no ambient graph or context universe
is part of this contract. -/
structure FamilyProfile (Pair : Type uPair) (Candidate : Type uCandidate) where
  pairs : FinEnum Pair
  scan : Profile Pair Candidate

namespace FamilyProfile

variable {Pair : Type uPair} {Candidate : Type uCandidate}
variable (family : FamilyProfile Pair Candidate)

/-- A pair is blocked exactly when one candidate in its declared local list
satisfies the blocker predicate. -/
def HasBlocker (pair : Pair) : Prop :=
  ∃ candidate, candidate ∈ (family.scan.candidates pair).values ∧
    family.scan.Blocks pair candidate

def hasBlockerDecidable (pair : Pair) : Decidable (family.HasBlocker pair) :=
by
  cases equation : family.scan.run pair with
  | found hit => exact .isTrue ⟨hit.value, hit.member, hit.holds⟩
  | absent absentProof => exact .isFalse (by
      rintro ⟨candidate, member, blocks⟩
      exact absentProof candidate member blocks)

/-- A blocked pair has a first blocker in the candidate order declared by its
pair-local profile. -/
theorem firstBlocker_nonempty
    (blocked : {pair : Pair // family.HasBlocker pair}) :
    Nonempty (Core.FiniteSearch.FirstHit
      (family.scan.candidates blocked.1).values
      (family.scan.Blocks blocked.1)) := by
  cases equation : family.scan.run blocked.1 with
  | found hit => exact ⟨hit⟩
  | absent absentProof =>
      rcases blocked.2 with ⟨candidate, member, blocks⟩
      exact (absentProof candidate member blocks).elim

/-- The canonical first blocker of a blocked pair, in the candidate order
declared by the pair-local profile. -/
def firstBlocker
    (blocked : {pair : Pair // family.HasBlocker pair}) :
    Core.FiniteSearch.FirstHit
      (family.scan.candidates blocked.1).values
      (family.scan.Blocks blocked.1) := by
  cases equation : family.scan.run blocked.1 with
  | found hit => exact hit
  | absent absentProof =>
      have impossible : False := by
        rcases blocked.2 with ⟨candidate, member, blocks⟩
        exact absentProof candidate member blocks
      exact impossible.elim

theorem firstBlocker_sound
    (blocked : {pair : Pair // family.HasBlocker pair}) :
    (family.firstBlocker blocked).value ∈
        (family.scan.candidates blocked.1).values ∧
      family.scan.Blocks blocked.1 (family.firstBlocker blocked).value ∧
      ∀ candidate ∈ (family.firstBlocker blocked).before,
        ¬family.scan.Blocks blocked.1 candidate :=
  ⟨(family.firstBlocker blocked).member,
    (family.firstBlocker blocked).holds,
    (family.firstBlocker blocked).beforeAbsent⟩

/-- Exact blocked-pair enumeration, preserving the source pair order. -/
@[implicit_reducible]
def blockedPairs : FinEnum {pair : Pair // family.HasBlocker pair} :=
  Core.Enumeration.subtype family.pairs family.HasBlocker
    family.hasBlockerDecidable

/-- Exact blocker-free pair enumeration, preserving the source pair order. -/
@[implicit_reducible]
def freePairs : FinEnum {pair : Pair // ¬family.HasBlocker pair} :=
  Core.Enumeration.subtype family.pairs (fun pair ↦ ¬family.HasBlocker pair)
    (fun pair ↦
      match family.hasBlockerDecidable pair with
      | .isTrue blocks => .isFalse fun notBlocks ↦ notBlocks blocks
      | .isFalse notBlocks => .isTrue notBlocks)

/-- Every supplied pair lies in exactly one side of the split. -/
theorem pair_split (pair : Pair) :
    family.HasBlocker pair ∨ ¬family.HasBlocker pair :=
  Classical.em _

/-- The free and blocked subtypes are disjoint. -/
theorem free_blocked_disjoint
    (free : {pair : Pair // ¬family.HasBlocker pair})
    (blocked : {pair : Pair // family.HasBlocker pair}) :
    free.1 ≠ blocked.1 := by
  intro equal
  exact free.2 (equal ▸ blocked.2)

/-- Exact no-loss/no-overcounting cardinality identity for the pair split. -/
theorem blocked_card_add_free_card :
    family.blockedPairs.card + family.freePairs.card = family.pairs.card := by
  letI : FinEnum Pair := family.pairs
  letI : Fintype {pair : Pair // family.HasBlocker pair} :=
    @FinEnum.instFintype _ family.blockedPairs
  letI : Fintype {pair : Pair // ¬family.HasBlocker pair} :=
    @FinEnum.instFintype _ family.freePairs
  calc
    family.blockedPairs.card + family.freePairs.card =
        Fintype.card {pair : Pair // family.HasBlocker pair} +
          Fintype.card {pair : Pair // ¬family.HasBlocker pair} :=
      congrArg₂ (· + ·)
        (@FinEnum.card_eq_fintypeCard _ family.blockedPairs inferInstance)
        (@FinEnum.card_eq_fintypeCard _ family.freePairs inferInstance)
    _ = Fintype.card {pair : Pair // family.HasBlocker pair} +
        (Fintype.card Pair -
          Fintype.card {pair : Pair // family.HasBlocker pair}) := by
      rw [Fintype.card_subtype_compl]
    _ = Fintype.card Pair :=
      Nat.add_sub_of_le (Fintype.card_subtype_le _)
    _ = family.pairs.card :=
      (@FinEnum.card_eq_fintypeCard _ family.pairs inferInstance).symm

/-- The family runner performs one exact local scan for each pair. -/
def checks : Nat :=
  family.pairs.orderedValues.map family.scan.checks |>.sum

theorem checks_eq_sum :
    family.checks =
      (family.pairs.orderedValues.map fun pair ↦
        (family.scan.candidates pair).values.length).sum :=
  rfl

end FamilyProfile

end StructuralExhaustion.Core.FiniteBlockerLedger
