import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.Routes.LongFiniteSupportHandoff

open StructuralExhaustion

universe uAmbient uBranch

/-!
# Long finite-support handoff

This is the exact interface available before a CT17 target-thickening run.
It records a finite support whose length exceeds a checked scale and preserves
the inherited branch context by type index.  It intentionally does not call
the support positions CT17 survivors and does not manufacture targets,
offsets, compatibility, block values, orbit values, or a finite-scale bound.

A later CT17 adapter must construct those semantic objects from its graph
theorems.  Finiteness of the support alone only supplies the position
enumeration below.
-/

variable {P : Core.Problem.{uAmbient, uBranch}}

/-- Exact data retained from a computed long-support branch. -/
structure Source (ctx : Core.BranchContext P) where
  supportLength : Nat
  scale : Nat
  exceeds : scale < supportLength

/-- The only CT17 author universe forced by a finite support: its positions. -/
abbrev Position {ctx : Core.BranchContext P} (source : Source ctx) :=
  Fin source.supportLength

/-- Canonical exhaustive enumeration of the literal support positions. -/
@[implicit_reducible]
def positions {ctx : Core.BranchContext P} (source : Source ctx) :
    FinEnum (Position source) :=
  inferInstance

@[simp]
theorem positions_card {ctx : Core.BranchContext P} (source : Source ctx) :
    (positions source).card = source.supportLength := by
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_fin]

/-- The literal initial segment forced by `scale < supportLength`.  It has
exactly `scale + 1` positions; no repetition or semantic state is attached to
these indices. -/
abbrev PrefixPosition {ctx : Core.BranchContext P} (source : Source ctx) :=
  Fin (source.scale + 1)

/-- Canonical exhaustive enumeration of the forced initial segment. -/
@[implicit_reducible]
def prefixPositions {ctx : Core.BranchContext P} (source : Source ctx) :
    FinEnum (PrefixPosition source) :=
  inferInstance

@[simp]
theorem prefixPositions_card {ctx : Core.BranchContext P} (source : Source ctx) :
    (prefixPositions source).card = source.scale + 1 := by
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_fin]

/-- The exact order-preserving inclusion of the first `scale + 1` positions
into the supplied finite support. -/
def prefixEmbedding {ctx : Core.BranchContext P} (source : Source ctx) :
    PrefixPosition source → Position source :=
  fun position =>
    ⟨position.1, lt_of_lt_of_le position.2 (Nat.succ_le_iff.mpr source.exceeds)⟩

@[simp]
theorem prefixEmbedding_val {ctx : Core.BranchContext P}
    (source : Source ctx) (position : PrefixPosition source) :
    (prefixEmbedding source position).1 = position.1 :=
  rfl

theorem prefixEmbedding_injective {ctx : Core.BranchContext P}
    (source : Source ctx) : Function.Injective (prefixEmbedding source) := by
  intro left right equal
  apply Fin.ext
  simpa only [prefixEmbedding_val] using congrArg (fun position => position.1) equal

/-- The base part of the forced prefix, before its unique extra position. -/
abbrev BasePosition {ctx : Core.BranchContext P} (source : Source ctx) :=
  Fin source.scale

/-- Canonical inclusion of the first `scale` positions into the forced
`scale + 1` prefix. -/
def baseEmbedding {ctx : Core.BranchContext P} (source : Source ctx) :
    BasePosition source → PrefixPosition source :=
  fun position => ⟨position.1, lt_trans position.2 (Nat.lt_succ_self source.scale)⟩

/-- The unique extra prefix index forced by the strict long inequality. -/
def overflow {ctx : Core.BranchContext P} (source : Source ctx) :
    PrefixPosition source :=
  ⟨source.scale, Nat.lt_succ_self source.scale⟩

/-- Image of the unique overflow index in the literal support. -/
def overflowImage {ctx : Core.BranchContext P} (source : Source ctx) :
    Position source :=
  prefixEmbedding source (overflow source)

@[simp]
theorem overflowImage_val {ctx : Core.BranchContext P} (source : Source ctx) :
    (overflowImage source).1 = source.scale :=
  rfl

/-- Exact decomposition of a forced-prefix position into a base index or the
unique overflow index. -/
inductive PrefixClass {ctx : Core.BranchContext P} (source : Source ctx)
    (position : PrefixPosition source) where
  | base (index : BasePosition source)
      (embeddingExact : baseEmbedding source index = position)
  | overflow (overflowExact : position = overflow source)

/-- Classify one prefix index by one comparison with `scale`. -/
def classifyPrefixPosition {ctx : Core.BranchContext P} (source : Source ctx)
    (position : PrefixPosition source) : PrefixClass source position := by
  by_cases before : position.1 < source.scale
  · exact .base ⟨position.1, before⟩ (Fin.ext rfl)
  · exact PrefixClass.overflow (Fin.ext
      (Nat.le_antisymm (Nat.le_of_lt_succ position.2)
        (Nat.le_of_not_gt before)))

/-- The exact base/overflow split exhausts the forced prefix. -/
theorem classifyPrefixPosition_exhaustive {ctx : Core.BranchContext P}
    (source : Source ctx) (position : PrefixPosition source) :
    (∃ index embeddingExact,
      classifyPrefixPosition source position = .base index embeddingExact) ∨
    (∃ overflowExact,
      classifyPrefixPosition source position = .overflow overflowExact) := by
  cases equation : classifyPrefixPosition source position with
  | base index embeddingExact =>
      exact Or.inl ⟨index, embeddingExact, rfl⟩
  | overflow overflowExact =>
      exact Or.inr ⟨overflowExact, rfl⟩

/-- A prefix position is classified as overflow exactly when it is the
canonical index `scale`. -/
theorem classifyPrefixPosition_overflow_iff {ctx : Core.BranchContext P}
    (source : Source ctx) (position : PrefixPosition source) :
    (∃ overflowExact,
      classifyPrefixPosition source position = .overflow overflowExact) ↔
      position = overflow source := by
  by_cases before : position.1 < source.scale
  · have notOverflow : position ≠ overflow source := by
      intro equal
      have valueEqual : position.1 = source.scale :=
        congrArg (fun index => index.1) equal
      exact (Nat.ne_of_lt before) valueEqual
    simp [classifyPrefixPosition, before, notOverflow]
  · have exactPosition : position = overflow source := by
      apply Fin.ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ position.2)
        (Nat.le_of_not_gt before)
    subst position
    simp [classifyPrefixPosition, overflow]

/-- A prefix position is in the base part exactly when its literal index is
strictly below `scale`. -/
theorem classifyPrefixPosition_base_iff {ctx : Core.BranchContext P}
    (source : Source ctx) (position : PrefixPosition source) :
    (∃ index embeddingExact,
      classifyPrefixPosition source position = .base index embeddingExact) ↔
      position.1 < source.scale := by
  by_cases before : position.1 < source.scale
  · constructor
    · intro _classified
      exact before
    · intro _before
      let index : BasePosition source := ⟨position.1, before⟩
      have embeddingExact : baseEmbedding source index = position := Fin.ext rfl
      refine ⟨index, embeddingExact, ?_⟩
      simp [classifyPrefixPosition, before, index]
  · simp [classifyPrefixPosition, before]

/-- Exact local classification of one supplied support position relative to
the forced initial segment. -/
inductive PositionClass {ctx : Core.BranchContext P} (source : Source ctx)
    (position : Position source) where
  | inPrefix (index : PrefixPosition source)
      (embeddingExact : prefixEmbedding source index = position)
  | afterPrefix (lowerBound : source.scale + 1 ≤ position.1)

/-- Classify one literal position.  This performs one natural-number
comparison and never enumerates an ambient universe. -/
def classifyPosition {ctx : Core.BranchContext P} (source : Source ctx)
    (position : Position source) : PositionClass source position := by
  by_cases before : position.1 < source.scale + 1
  · exact .inPrefix ⟨position.1, before⟩ (Fin.ext rfl)
  · exact .afterPrefix (Nat.le_of_not_gt before)

/-- The position classifier has exactly the two advertised outcomes. -/
theorem classifyPosition_exhaustive {ctx : Core.BranchContext P}
    (source : Source ctx) (position : Position source) :
    (∃ index embeddingExact,
      classifyPosition source position = .inPrefix index embeddingExact) ∨
    (∃ lowerBound, classifyPosition source position = .afterPrefix lowerBound) := by
  cases equation : classifyPosition source position with
  | inPrefix index embeddingExact =>
      exact Or.inl ⟨index, embeddingExact, rfl⟩
  | afterPrefix lowerBound => exact Or.inr ⟨lowerBound, rfl⟩

/-- Consumer residual.  The exact source is retained rather than rebuilt. -/
structure Residual (ctx : Core.BranchContext P) where
  source : Source ctx

/-- Forced identity handoff on the computed long branch. -/
def handoff {ctx : Core.BranchContext P} (source : Source ctx) : Residual ctx :=
  ⟨source⟩

@[simp]
theorem handoff_source {ctx : Core.BranchContext P} (source : Source ctx) :
    (handoff source).source = source :=
  rfl

theorem routed_exceeds {ctx : Core.BranchContext P} (source : Source ctx) :
    (handoff source).source.scale < (handoff source).source.supportLength :=
  source.exceeds

/-- Stable provenance identifier for graph and application audits. -/
def handoffId : String :=
  "finite-long-support->typed-scale-handoff"

end StructuralExhaustion.Routes.LongFiniteSupportHandoff
