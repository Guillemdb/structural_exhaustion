import StructuralExhaustion.CT15.State

namespace StructuralExhaustion.CT15

universe uAmbient uBranch uCoordinate

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (S : Spec P) (capability : Capability S) (input : Input P)

theorem rankContribution_independent (coordinate : S.Coordinate)
    (independent : ¬ S.TargetDependent input coordinate) :
    rankContribution S capability input coordinate = 1 := by
  unfold rankContribution
  cases decision : capability.targetDependentDecidable input coordinate with
  | isTrue dependent => exact (independent dependent).elim
  | isFalse _ => rfl

/-- Exhaustive absence of target-relative dependence forces literal full
rank. -/
theorem computedRank_eq_targetRank
    (noDrop : ∀ coordinate, ¬ S.TargetDependent input coordinate) :
    computedRank S capability input = targetRank S capability := by
  unfold computedRank targetRank
  let elements := capability.coordinates.orderedValues
  change (elements.map (rankContribution S capability input)).sum =
    elements.length
  induction elements with
  | nil => rfl
  | cons head tail ih =>
      simp [rankContribution_independent S capability input head
        (noDrop head), ih, Nat.add_comm]

inductive RankSplitDecision (rank : RankState S capability input) where
  | dropped (residual : RankDropResidual S capability input rank)
  | full (state : FullRankState S capability input rank)

/-- Deterministic first-drop search in exact enumeration order. -/
def splitRank (rank : RankState S capability input) :
    RankSplitDecision S capability input rank :=
  match Core.FiniteSearch.first capability.coordinates
      (S.TargetDependent input)
      (capability.targetDependentDecidable input) with
  | .found hit => .dropped ⟨hit⟩
  | .absent absent =>
      have noDrop : ∀ coordinate, ¬ S.TargetDependent input coordinate :=
        fun coordinate => absent coordinate
          (capability.coordinates.mem_orderedValues coordinate)
      .full ⟨noDrop,
        rank.computed.trans
          (computedRank_eq_targetRank S capability input noDrop)⟩

inductive LedgerComparison
    {rank : RankState S capability input}
    {full : FullRankState S capability input rank}
    (ledger : LedgerState S capability input full) where
  | closes (certificate : C4Certificate S capability input ledger)
  | residual (residual : FullRankLedgerResidual S capability input ledger)

/-- Exact arithmetic split with no proof-instance comparison callback. -/
def compareLedger
    {rank : RankState S capability input}
    {full : FullRankState S capability input rank}
    (ledger : LedgerState S capability input full) :
    LedgerComparison S capability input ledger :=
  match Nat.decLt (S.capacity input) ledger.total with
  | .isTrue exceeds => .closes ⟨exceeds⟩
  | .isFalse notExceeds => .residual ⟨Nat.le_of_not_gt notExceeds⟩

theorem splitRank_sound (rank : RankState S capability input) :
    match splitRank S capability input rank with
    | .dropped residual =>
        S.TargetDependent input residual.hit.value ∧
          ∀ coordinate, coordinate ∈ residual.hit.before →
            ¬ S.TargetDependent input coordinate
    | .full _ =>
        (∀ coordinate, ¬ S.TargetDependent input coordinate) ∧
          rank.value = targetRank S capability := by
  cases splitRank S capability input rank with
  | dropped residual => exact ⟨residual.hit.holds, residual.hit.beforeAbsent⟩
  | full state => exact ⟨state.noDrop, state.full⟩

end StructuralExhaustion.CT15
