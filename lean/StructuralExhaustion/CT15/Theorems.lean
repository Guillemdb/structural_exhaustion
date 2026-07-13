import StructuralExhaustion.CT15.Execution

namespace StructuralExhaustion.CT15

universe uAmbient uBranch uCoordinate

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (S : Spec.{uAmbient, uBranch, uCoordinate} P)
variable (capability : Capability S) (input : Input P)

namespace RawOutcome

/-- Exact semantic meaning of every terminal. -/
def Valid {terminal : Graph.Terminal} :
    RawOutcome S capability input terminal → Prop
  | .rankDrop residual =>
      S.TargetDependent input residual.hit.value ∧
        ∀ coordinate, coordinate ∈ residual.hit.before →
          ¬ S.TargetDependent input coordinate
  | .c4 _ =>
      (∀ coordinate, ¬ S.TargetDependent input coordinate) ∧
        computedRank S capability input = targetRank S capability ∧
        S.capacity input < ledgerTotal S capability input
  | .fullRankLedger _ =>
      (∀ coordinate, ¬ S.TargetDependent input coordinate) ∧
        computedRank S capability input = targetRank S capability ∧
        ledgerTotal S capability input ≤ S.capacity input

theorem verified {terminal : Graph.Terminal}
    (outcome : RawOutcome S capability input terminal) : outcome.Valid := by
  cases outcome with
  | rankDrop residual =>
      exact ⟨residual.hit.holds, residual.hit.beforeAbsent⟩
  | @c4 rank full ledger certificate =>
      change (∀ coordinate, ¬ S.TargetDependent input coordinate) ∧
        computedRank S capability input = targetRank S capability ∧
        S.capacity input < ledgerTotal S capability input
      refine ⟨full.noDrop,
        computedRank_eq_targetRank S capability input full.noDrop, ?_⟩
      rw [← ledger.summed]
      exact certificate.capacity_lt_total
  | @fullRankLedger rank full ledger residual =>
      change (∀ coordinate, ¬ S.TargetDependent input coordinate) ∧
        computedRank S capability input = targetRank S capability ∧
        ledgerTotal S capability input ≤ S.capacity input
      refine ⟨full.noDrop,
        computedRank_eq_targetRank S capability input full.noDrop, ?_⟩
      rw [← ledger.summed]
      exact residual.total_le_capacity

end RawOutcome

namespace ExecutionResult

theorem verified (result : ExecutionResult S capability input) :
    result.outcome.Valid :=
  result.outcome.verified

theorem traceValid (result : ExecutionResult S capability input) :
    @Graph.ValidTrace P S capability input result.trace :=
  ⟨result.terminal, result.path, rfl⟩

end ExecutionResult

theorem run_verified :
    (run S capability input).outcome.Valid :=
  (run S capability input).verified

theorem run_trace_valid :
    @Graph.ValidTrace P S capability input (run S capability input).trace :=
  (run S capability input).traceValid

theorem run_total :
    ∃ result : ExecutionResult S capability input,
      result.outcome.Valid ∧
        @Graph.ValidTrace P S capability input result.trace :=
  ⟨run S capability input,
    run_verified S capability input,
    run_trace_valid S capability input⟩

theorem run_deterministic
    (left right : ExecutionResult S capability input)
    (leftIsRun : left = run S capability input)
    (rightIsRun : right = run S capability input) : left = right :=
  leftIsRun.trans rightIsRun.symm

theorem outcome_exhaustive
    (result : ExecutionResult S capability input) :
    result.terminal = .rankDrop ∨
      result.terminal = .c4 ∨
      result.terminal = .fullRankLedger := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | rankDrop _ => exact Or.inl rfl
      | c4 _ => exact Or.inr (Or.inl rfl)
      | fullRankLedger _ => exact Or.inr (Or.inr rfl)

/-- A full-rank state certifies both exhaustive independence and the exact
target-rank equality. -/
theorem full_rank_sound {rank : RankState S capability input}
    (full : FullRankState S capability input rank) :
    (∀ coordinate, ¬ S.TargetDependent input coordinate) ∧
      rank.value = targetRank S capability :=
  ⟨full.noDrop, full.full⟩

/-- Every ledger is the complete declared coordinate ledger, with no omitted
or duplicated coordinate. -/
theorem ledger_exact {rank : RankState S capability input}
    {full : FullRankState S capability input rank}
    (ledger : LedgerState S capability input full) :
    ledger.entries = ledgerEntries S capability input ∧
      ledger.total = ledgerTotal S capability input :=
  ⟨ledger.exact, ledger.summed⟩

end StructuralExhaustion.CT15
