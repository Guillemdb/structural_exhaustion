namespace StructuralExhaustion.Core.FiniteObservedReconstruction

universe u

/-!
# Complete-or-first-missing reconstruction on a supplied row list

This classifier scans only the caller's ordered finite observations.  The
reconstruction type may depend on the row.  It either returns a reconstruction
for every supplied row or the first row at which the supplied derivation
returns `none`, retaining the completely reconstructed prefix.
-/

structure System (Row : Type u) where
  Reconstruction : Row → Prop
  derive : DecidablePred Reconstruction

namespace System

variable {Row : Type u} (system : System Row)

structure ReconstructedFamily (rows : List Row) where
  value : ∀ row, row ∈ rows → system.Reconstruction row

structure FirstMissing (rows : List Row) where
  priorRows : List Row
  row : Row
  suffix : List Row
  rowsExact : rows = priorRows ++ row :: suffix
  priorValue : ∀ entry, entry ∈ priorRows → system.Reconstruction entry
  missing : ¬system.Reconstruction row

inductive Outcome (rows : List Row) where
  | complete (family : system.ReconstructedFamily rows)
  | firstMissing (residual : system.FirstMissing rows)

/-- Ordered, early-stopping classifier on the supplied rows. -/
def classify : (rows : List Row) → system.Outcome rows
  | [] => .complete ⟨fun _row member => by simp at member⟩
  | row :: rows => by
      cases decision : system.derive row with
      | isFalse missing =>
          exact .firstMissing {
            priorRows := []
            row := row
            suffix := rows
            rowsExact := rfl
            priorValue := fun _entry member => by simp at member
            missing := missing
          }
      | isTrue value =>
          cases recursive : classify rows with
          | complete family =>
              apply Outcome.complete
              refine ⟨fun entry member => ?_⟩
              rcases List.mem_cons.mp member with same | later
              · subst entry
                exact value
              · exact family.value entry later
          | firstMissing residual =>
              exact .firstMissing {
                priorRows := row :: residual.priorRows
                row := residual.row
                suffix := residual.suffix
                rowsExact := by
                  simpa using (congrArg (List.cons row) residual.rowsExact)
                priorValue := fun entry member => by
                  rcases List.mem_cons.mp member with same | later
                  · subst entry
                    exact value
                  · exact residual.priorValue entry later
                missing := residual.missing
              }

theorem classify_exhaustive (rows : List Row) :
    (∃ family, system.classify rows = .complete family) ∨
      (∃ residual, system.classify rows = .firstMissing residual) := by
  cases equation : system.classify rows with
  | complete family => exact Or.inl ⟨family, rfl⟩
  | firstMissing residual => exact Or.inr ⟨residual, rfl⟩

end System

end StructuralExhaustion.Core.FiniteObservedReconstruction
