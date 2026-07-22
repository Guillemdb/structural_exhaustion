import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Residual.Focus

/-!
# Focused proof projections

A proof projection records one proposition derived from an active query on the
literal predecessor. Core owns the certificate, counted branch selection,
ledger extension, successor focus, latest query, and work accounting. The
proof transformation itself performs no primitive inspection; the total count
is exactly the inherited focus-selection count.
-/

namespace Hypostructure.Core.Residual.ProofProjection

universe uPrevious

/-- Framework-owned evidence for one dependent claim projected from the
active predecessor ledger.  The private constructor prevents callers from
manufacturing either the certificate or its work count. -/
structure Certificate {Previous : Type uPrevious}
    (focus : Focus.Profile Previous)
    (Claim : (previous : Previous) -> focus.Active previous -> Prop)
    (previous : Previous) (active : focus.Active previous) where
  private mk ::
  claim : Claim previous active
  checks : Nat
  checks_eq_budget : checks = focus.selectionBudget.checks previous

/-- The proof transformation is free, so the complete executor inherits the
exact counted budget of focused branch selection. -/
def workBudget {Previous : Type uPrevious} (focus : Focus.Profile Previous) :
    PolynomialCheckBudget Previous :=
  focus.selectionBudget

@[simp] theorem workBudget_checks {Previous : Type uPrevious}
    (focus : Focus.Profile Previous) (previous : Previous) :
    (workBudget focus).checks previous =
      focus.selectionBudget.checks previous :=
  rfl

/-- Core's registered focus-selection schedule satisfies its polynomial
envelope at every literal predecessor. -/
theorem workBudget_bounded {Previous : Type uPrevious}
    (focus : Focus.Profile Previous) (previous : Previous) :
    (workBudget focus).checks previous <=
      (workBudget focus).coefficient *
        ((workBudget focus).size previous + 1) ^
          (workBudget focus).degree :=
  (workBudget focus).bounded previous

/-- Canonical predicate form of the registered proof-projection work
envelope. -/
theorem workBudget_within {Previous : Type uPrevious}
    (focus : Focus.Profile Previous) (previous : Previous) :
    (workBudget focus).Within previous
      ((workBudget focus).checks previous) :=
  (workBudget focus).checks_within previous

namespace Certificate

/-- Every generated certificate satisfies Core's proof-projection work
envelope. -/
theorem work_bounded {Previous : Type uPrevious}
    {focus : Focus.Profile Previous}
    {Claim : (previous : Previous) -> focus.Active previous -> Prop}
    {previous : Previous} {active : focus.Active previous}
    (certificate : Certificate focus Claim previous active) :
    certificate.checks <=
      (workBudget focus).coefficient *
        ((workBudget focus).size previous + 1) ^
          (workBudget focus).degree := by
  rw [certificate.checks_eq_budget]
  exact (workBudget focus).bounded previous

/-- Canonical predicate form of `work_bounded`, avoiding expansion of the
polynomial envelope at application sites. -/
theorem work_within {Previous : Type uPrevious}
    {focus : Focus.Profile Previous}
    {Claim : (previous : Previous) -> focus.Active previous -> Prop}
    {previous : Previous} {active : focus.Active previous}
    (certificate : Certificate focus Claim previous active) :
    (workBudget focus).Within previous certificate.checks :=
  certificate.work_bounded

end Certificate

/-- Exact accumulated successor carrying one Core-owned proof certificate on
the active branch and no payload on inactive siblings. -/
abbrev Stage {Previous : Type uPrevious}
    (focus : Focus.Profile Previous)
    (Claim : (previous : Previous) -> focus.Active previous -> Prop) :=
  Focus.Stage focus fun previous active =>
    Certificate focus Claim previous active

/-- The same active branch after the proof certificate has been appended. -/
abbrev Profile {Previous : Type uPrevious}
    (focus : Focus.Profile Previous)
    (Claim : (previous : Previous) -> focus.Active previous -> Prop) :=
  Focus.successor focus fun previous active =>
    Certificate focus Claim previous active

/-- Project an exact active query through one counted focus selection. The
returned stage and check count arise from the same selector execution. -/
def executeCounted {Previous : Type uPrevious}
    (focus : Focus.Profile Previous)
    (Claim : (previous : Previous) -> focus.Active previous -> Prop)
    (projection : Focus.ActiveQuery focus Claim)
    (previous : Previous) : Counted (Stage focus Claim) :=
  Focus.runCounted focus previous fun active checks exact =>
    .mk (projection.read previous active) checks exact

/-- Public stage projection. Exact work remains queryable from the private
certificate and is definitionally the count of `executeCounted`. -/
def execute {Previous : Type uPrevious}
    (focus : Focus.Profile Previous)
    (Claim : (previous : Previous) -> focus.Active previous -> Prop)
    (projection : Focus.ActiveQuery focus Claim)
    (previous : Previous) : Stage focus Claim :=
  (executeCounted focus Claim projection previous).value

@[simp] theorem executeCounted_checks {Previous : Type uPrevious}
    (focus : Focus.Profile Previous)
    (Claim : (previous : Previous) -> focus.Active previous -> Prop)
    (projection : Focus.ActiveQuery focus Claim)
    (previous : Previous) :
    (executeCounted focus Claim projection previous).checks =
      focus.selectionBudget.checks previous :=
  Focus.runCounted_checks focus previous _

/-- The complete counted projection, including inactive outcomes, satisfies
the registered focus-selection envelope. -/
theorem executeCounted_checks_bounded {Previous : Type uPrevious}
    (focus : Focus.Profile Previous)
    (Claim : (previous : Previous) -> focus.Active previous -> Prop)
    (projection : Focus.ActiveQuery focus Claim)
    (previous : Previous) :
    (executeCounted focus Claim projection previous).checks <=
      (workBudget focus).coefficient *
        ((workBudget focus).size previous + 1) ^
          (workBudget focus).degree := by
  rw [executeCounted_checks]
  exact (workBudget focus).bounded previous

/-- Predicate-form work theorem for counted proof projections. -/
theorem executeCounted_work_within {Previous : Type uPrevious}
    (focus : Focus.Profile Previous)
    (Claim : (previous : Previous) -> focus.Active previous -> Prop)
    (projection : Focus.ActiveQuery focus Claim)
    (previous : Previous) :
    (workBudget focus).Within previous
      (executeCounted focus Claim projection previous).checks := by
  rw [executeCounted_checks]
  exact workBudget_within focus previous

/-- Read the exact certificate introduced by the latest focused extension. -/
def latest {Previous : Type uPrevious}
    (focus : Focus.Profile Previous)
    (Claim : (previous : Previous) -> focus.Active previous -> Prop) :
    Focus.ActiveQuery (Profile focus Claim) fun stage active =>
      Certificate focus Claim stage.previous active :=
  Focus.ActiveQuery.latest

/-- Read only the projected claim from the newest certificate. -/
def latestClaim {Previous : Type uPrevious}
    (focus : Focus.Profile Previous)
    (Claim : (previous : Previous) -> focus.Active previous -> Prop) :
    Focus.ActiveQuery (Profile focus Claim) fun stage active =>
      Claim stage.previous active :=
  (latest focus Claim).map fun _stage _active certificate =>
    certificate.claim

@[simp] theorem execute_previous {Previous : Type uPrevious}
    (focus : Focus.Profile Previous)
    (Claim : (previous : Previous) -> focus.Active previous -> Prop)
    (projection : Focus.ActiveQuery focus Claim)
    (previous : Previous) :
    (execute focus Claim projection previous).previous = previous :=
  rfl

/-- The newest claim is exactly the predecessor-indexed projection supplied
to the executor. -/
@[simp] theorem latestClaim_read_execute {Previous : Type uPrevious}
    (focus : Focus.Profile Previous)
    (Claim : (previous : Previous) -> focus.Active previous -> Prop)
    (projection : Focus.ActiveQuery focus Claim)
    (previous : Previous) (active : focus.Active previous) :
    (latestClaim focus Claim).read
        (execute focus Claim projection previous) active =
      projection.read previous active :=
  Subsingleton.elim _ _

/-- The certificate read from an executed active branch records exactly the
counted focus-selection work. -/
@[simp] theorem latest_checks_eq_budget {Previous : Type uPrevious}
    (focus : Focus.Profile Previous)
    (Claim : (previous : Previous) -> focus.Active previous -> Prop)
    (projection : Focus.ActiveQuery focus Claim)
    (previous : Previous) (active : focus.Active previous) :
    ((latest focus Claim).read
      (execute focus Claim projection previous) active).checks =
        focus.selectionBudget.checks previous :=
  ((latest focus Claim).read
    (execute focus Claim projection previous) active).checks_eq_budget

/-- The stored certificate count is the exact count returned by the single
counted execution that produced its stage. -/
theorem latest_checks_eq_execution {Previous : Type uPrevious}
    (focus : Focus.Profile Previous)
    (Claim : (previous : Previous) -> focus.Active previous -> Prop)
    (projection : Focus.ActiveQuery focus Claim)
    (previous : Previous) (active : focus.Active previous) :
    ((latest focus Claim).read
      (execute focus Claim projection previous) active).checks =
        (executeCounted focus Claim projection previous).checks := by
  rw [latest_checks_eq_budget, executeCounted_checks]

end Hypostructure.Core.Residual.ProofProjection
