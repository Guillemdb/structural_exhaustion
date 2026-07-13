import StructuralExhaustion.CT10.Execution

namespace StructuralExhaustion.CT10

universe uAmbient uBranch uDatum uClass uPromotion
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uDatum, uClass, uPromotion} P)
variable (input : Input capability)

namespace Outcome
def Valid {t} : Outcome capability input t → Prop
  | .direct r => capability.Direct r.cls
  | .promoted r => row capability input r.missing.cls = [] ∧
      r.promotion = capability.promote r.missing.cls
  | .exhaustive c => (∀ cls, ¬ capability.Direct cls) ∧
      (∀ cls, ∃ datum, datum ∈ row capability input cls)
theorem verified {t} (o : Outcome capability input t) : o.Valid := by
  cases o with
  | direct r => exact r.direct
  | promoted r => exact ⟨r.missing.empty, r.exact⟩
  | exhaustive c => exact ⟨c.directAbsent.absent, c.populated⟩
end Outcome

namespace ExecutionResult
theorem verified (r : ExecutionResult capability input) : r.outcome.Valid :=
  r.outcome.verified
theorem traceValid (r : ExecutionResult capability input) :
    Graph.ValidTrace capability input r.trace := ⟨r.terminal, r.path, rfl⟩
end ExecutionResult

theorem run_verified : (run capability input).outcome.Valid :=
  (run capability input).verified
theorem run_trace_valid : Graph.ValidTrace capability input (run capability input).trace :=
  (run capability input).traceValid
theorem run_total : ∃ r : ExecutionResult capability input,
    r.outcome.Valid ∧ Graph.ValidTrace capability input r.trace :=
  ⟨run capability input, run_verified capability input, run_trace_valid capability input⟩
theorem run_deterministic (l r : ExecutionResult capability input)
    (hl : l = run capability input) (hr : r = run capability input) : l = r :=
  hl.trans hr.symm
theorem outcome_exhaustive (result : ExecutionResult capability input) :
    result.terminal = .direct ∨ result.terminal = .promoted ∨
      result.terminal = .exhaustive := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | direct _ => exact Or.inl rfl
      | promoted _ => exact Or.inr (Or.inl rfl)
      | exhaustive _ => exact Or.inr (Or.inr rfl)

/-- A complete class table with no direct exception reaches CT10's
exhaustive certificate terminal. -/
theorem run_terminal_exhaustive_of_noDirect_of_populated
    (noDirect : ∀ cls : capability.Class, ¬ capability.Direct cls)
    (populated : ∀ cls : capability.Class,
      ∃ datum : capability.Datum, datum ∈ row capability input cls) :
    (run capability input).terminal = .exhaustive := by
  unfold run runReference
  cases directEquation : analyzeDirect capability with
  | found residual => exact (noDirect residual.cls residual.direct).elim
  | absent directAbsent =>
      cases missingEquation : analyzeMissing capability input directAbsent with
      | promoted residual =>
          obtain ⟨datum, member⟩ := populated residual.missing.cls
          rw [residual.missing.empty] at member
          exact (List.not_mem_nil member).elim
      | exhaustive certificate =>
        simp only [missingEquation]

/-- Exact canonical trace of the complete-table CT10 execution. -/
theorem run_trace_exhaustive_of_noDirect_of_populated
    (noDirect : ∀ cls : capability.Class, ¬ capability.Direct cls)
    (populated : ∀ cls : capability.Class,
      ∃ datum : capability.Datum, datum ∈ row capability input cls) :
    (run capability input).trace =
      [.entry, .table, .direct, .missing, .exhaustiveTerminal] := by
  have terminal := run_terminal_exhaustive_of_noDirect_of_populated
    capability input noDirect populated
  generalize resultEquation : run capability input = result at terminal ⊢
  cases result with
  | mk resultTerminal path outcome =>
      dsimp only at terminal
      subst resultTerminal
      exact Graph.trace_eq_of_path_to_exhaustive capability input path

end StructuralExhaustion.CT10
