import Hypostructure.Core.Residual.ProofProjection

/-!
# Focused proof-projection fixture

The fixture projects one exact fact from an active accumulated ledger, leaves
an inactive sibling untouched, and checks predecessor retention, query
precision, and the exact single focus-selection check.
-/

namespace Hypostructure.Fixtures.ProofProjection

open Hypostructure.Core
open Hypostructure.Core.Residual

abbrev BasePrevious := Ledger.Extension (Ledger Bool) fun _root => Nat

def predecessor (flag : Bool) (value : Nat) : BasePrevious :=
  Ledger.extend (Ledger.initial flag) value

/-- Exact read before the framework decision that creates the focus. -/
def baseValueQuery : Query BasePrevious fun _previous => Nat :=
  Query.latest

abbrev ActiveProperty (previous : BasePrevious) : Prop :=
  residualOf previous = true /\ baseValueQuery.read previous = 7

def activePropertyDecidable (previous : BasePrevious) :
    Decidable (ActiveProperty previous) :=
  inferInstance

def decision : Decision.Node BasePrevious ActiveProperty
    (fun previous => Not (ActiveProperty previous)) :=
  Decision.Node.complement ActiveProperty activePropertyDecidable

abbrev Previous := Decision.Stage ActiveProperty
  (fun previous => Not (ActiveProperty previous))

def activePrevious : Previous :=
  decision.run (predecessor true 7)

def inactivePrevious : Previous :=
  decision.run (predecessor false 11)

/-- Exact read of the value already stored in the predecessor ledger. -/
def valueQuery : Query Previous fun _previous => Nat :=
  baseValueQuery.preserve

/-- Core's yes focus inspects only the stored decision constructor. -/
abbrev focus : Focus.Profile Previous :=
  Focus.yes (Yes := ActiveProperty)
    (No := fun previous => Not (ActiveProperty previous))

/-- The dependent proposition appended on the active branch. -/
abbrev Claim (previous : Previous) (_active : focus.Active previous) : Prop :=
  valueQuery.read previous = 7

/-- Build the claim only by transforming an active query on the literal
predecessor. -/
def projection : Focus.ActiveQuery focus Claim :=
  (Focus.ActiveQuery.ofQuery valueQuery).map fun _previous active _value =>
    active.proof.2

abbrev ProjectedStage :=
  Core.Residual.ProofProjection.Stage focus Claim

abbrev projectedFocus :=
  Core.Residual.ProofProjection.Profile focus Claim

def projectCounted (previous : Previous) : Core.Counted ProjectedStage :=
  Core.Residual.ProofProjection.executeCounted
    focus Claim projection previous

def project (previous : Previous) : ProjectedStage :=
  (projectCounted previous).value

def activeStage : ProjectedStage :=
  project activePrevious

def inactiveStage : ProjectedStage :=
  project inactivePrevious

def activeProof : focus.Active activePrevious where
  proof := ⟨rfl, rfl⟩
  selected := rfl

def inactiveProof : Not (focus.Active inactivePrevious) := by
  intro active
  have impossible : false = true := by
    simpa [inactivePrevious, predecessor] using active.proof.1
  cases impossible

def projectedActive : projectedFocus.Active activeStage :=
  activeProof

/-- Latest means the exact certificate installed by this extension. -/
def certificateQuery :
    Focus.ActiveQuery projectedFocus fun stage active =>
      Core.Residual.ProofProjection.Certificate
        focus Claim stage.previous active :=
  Core.Residual.ProofProjection.latest focus Claim

/-- The claim query strips only the private Core certificate wrapper. -/
def claimQuery :
    Focus.ActiveQuery projectedFocus fun stage active =>
      Claim stage.previous active :=
  Core.Residual.ProofProjection.latestClaim focus Claim

theorem active_branch_has_certificate :
    exists proof certificate,
      activeStage.added = Focus.Outcome.active proof certificate := by
  cases branch : activeStage.added with
  | active proof certificate => exact ⟨proof, certificate, rfl⟩
  | inactive absent => exact (absent activeProof).elim

theorem inactive_branch_has_no_payload :
    exists absent,
      inactiveStage.added = Focus.Outcome.inactive absent := by
  cases branch : inactiveStage.added with
  | active proof _certificate => exact (inactiveProof proof).elim
  | inactive absent => exact ⟨absent, rfl⟩

theorem active_predecessor_retained :
    activeStage.previous = activePrevious :=
  Core.Residual.ProofProjection.execute_previous
    focus Claim projection activePrevious

theorem inactive_predecessor_retained :
    inactiveStage.previous = inactivePrevious :=
  Core.Residual.ProofProjection.execute_previous
    focus Claim projection inactivePrevious

/-- An ordinary predecessor query remains available through the complete
extension, with its exact old value. -/
theorem active_ledger_value_preserved :
    (valueQuery.preserve.read activeStage : Nat) = 7 :=
  rfl

theorem inactive_ledger_value_preserved :
    (valueQuery.preserve.read inactiveStage : Nat) = 11 :=
  rfl

theorem active_residual_preserved :
    residualOf activeStage = true :=
  rfl

theorem inactive_residual_preserved :
    residualOf inactiveStage = false :=
  rfl

/-- The newest query proves the claim at the literal predecessor, not at a
copied or reconstructed state. -/
theorem exact_projected_query :
    valueQuery.read activeStage.previous = 7 :=
  claimQuery.read activeStage projectedActive

theorem active_checks_eq_one :
    (certificateQuery.read activeStage projectedActive).checks = 1 := by
  exact
    (certificateQuery.read activeStage projectedActive).checks_eq_budget.trans
      rfl

theorem active_certificate_matches_execution_count :
    (certificateQuery.read activeStage projectedActive).checks =
      (projectCounted activePrevious).checks :=
  Core.Residual.ProofProjection.latest_checks_eq_execution
    focus Claim projection activePrevious activeProof

theorem active_execution_checks_eq_one :
    (projectCounted activePrevious).checks = 1 := by
  exact (Core.Residual.ProofProjection.executeCounted_checks
    focus Claim projection activePrevious).trans rfl

/-- The inactive branch performs the same one stored-constructor inspection,
even though it correctly receives no certificate payload. -/
theorem inactive_execution_checks_eq_one :
    (projectCounted inactivePrevious).checks = 1 := by
  exact (Core.Residual.ProofProjection.executeCounted_checks
    focus Claim projection inactivePrevious).trans rfl

theorem inactive_execution_work_bounded :
    (projectCounted inactivePrevious).checks <=
      (Core.Residual.ProofProjection.workBudget focus).coefficient *
        ((Core.Residual.ProofProjection.workBudget focus).size
          inactivePrevious + 1) ^
          (Core.Residual.ProofProjection.workBudget focus).degree :=
  Core.Residual.ProofProjection.executeCounted_checks_bounded
    focus Claim projection inactivePrevious

theorem framework_budget_exact_one :
    (Core.Residual.ProofProjection.workBudget focus).checks
      activePrevious = 1 :=
  rfl

theorem framework_budget_bounded :
    (Core.Residual.ProofProjection.workBudget focus).checks
        activePrevious <=
      (Core.Residual.ProofProjection.workBudget focus).coefficient *
        ((Core.Residual.ProofProjection.workBudget focus).size
          activePrevious + 1) ^
          (Core.Residual.ProofProjection.workBudget focus).degree :=
  Core.Residual.ProofProjection.workBudget_bounded focus activePrevious

#print axioms Core.Residual.ProofProjection.execute
#print axioms Core.Residual.ProofProjection.executeCounted
#print axioms Core.Residual.ProofProjection.latest
#print axioms Core.Residual.ProofProjection.latestClaim
#print axioms Core.Residual.ProofProjection.execute_previous
#print axioms Core.Residual.ProofProjection.latestClaim_read_execute
#print axioms Core.Residual.ProofProjection.workBudget_checks
#print axioms Core.Residual.ProofProjection.workBudget_bounded
#print axioms Core.Residual.ProofProjection.latest_checks_eq_budget
#print axioms Core.Residual.ProofProjection.latest_checks_eq_execution
#print axioms Core.Residual.ProofProjection.Certificate.work_bounded
#print axioms active_branch_has_certificate
#print axioms inactive_branch_has_no_payload
#print axioms active_predecessor_retained
#print axioms inactive_predecessor_retained
#print axioms active_ledger_value_preserved
#print axioms inactive_ledger_value_preserved
#print axioms exact_projected_query
#print axioms active_checks_eq_one
#print axioms active_certificate_matches_execution_count
#print axioms active_execution_checks_eq_one
#print axioms inactive_execution_checks_eq_one
#print axioms inactive_execution_work_bounded
#print axioms framework_budget_bounded

end Hypostructure.Fixtures.ProofProjection
