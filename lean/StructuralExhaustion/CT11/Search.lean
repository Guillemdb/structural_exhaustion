import StructuralExhaustion.CT11.State

namespace StructuralExhaustion.CT11

universe uAmbient uBranch uCell
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uCell} P)
variable (input : Input capability)

inductive AdmissibilityDecision where
  | gap (residual : AdmissibilityGapResidual capability input)
  | closed (state : AdmissibleDecomposition capability input)

def inadmissibleDecidable (cell : capability.Cell) :
    Decidable (¬ capability.Admissible input.context cell) :=
  match capability.admissibleDecidable input.context cell with
  | .isTrue admissible => .isFalse fun inadmissible => inadmissible admissible
  | .isFalse inadmissible => .isTrue inadmissible

def analyzeAdmissibility : AdmissibilityDecision capability input :=
  match Core.FiniteSearch.onList input.cells.values
      (fun cell => ¬ capability.Admissible input.context cell)
      (inadmissibleDecidable capability input) with
  | .found cell member inadmissible => .gap ⟨cell, member, inadmissible⟩
  | .absent noGap => .closed ⟨fun cell member =>
      match capability.admissibleDecidable input.context cell with
      | .isTrue admissible => admissible
      | .isFalse inadmissible => (noGap cell member inadmissible).elim⟩

theorem sum_nonnegative (values : List Int)
    (nonnegative : ∀ value : Int, value ∈ values → 0 ≤ value) :
    0 ≤ values.sum := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.sum_cons]
      apply Int.add_nonneg
      · exact nonnegative head (by simp)
      · exact ih fun value member => nonnegative value (by simp [member])

def localize (admissible : AdmissibleDecomposition capability input) :
    LocalizedDeficitResidual capability input :=
  match Core.FiniteSearch.onList input.cells.values
      (fun cell => capability.localBudget input.context cell < 0)
      (fun _ => inferInstance) with
  | .found cell member negative => ⟨admissible, cell, member, negative⟩
  | .absent noNegative => by
      have nonnegative : 0 ≤
          (input.cells.values.map (capability.localBudget input.context)).sum := by
        apply sum_nonnegative
        intro value member
        simp only [List.mem_map] at member
        obtain ⟨cell, cellMem, rfl⟩ := member
        exact Int.le_of_not_gt (noNegative cell cellMem)
      exact (Int.not_lt_of_ge nonnegative input.deficit).elim

theorem localize_sound (admissible : AdmissibleDecomposition capability input) :
    let residual := localize capability input admissible
    residual.cell ∈ input.cells.values ∧
      capability.localBudget input.context residual.cell < 0 := by
  exact ⟨(localize capability input admissible).member,
    (localize capability input admissible).negative⟩

end StructuralExhaustion.CT11
