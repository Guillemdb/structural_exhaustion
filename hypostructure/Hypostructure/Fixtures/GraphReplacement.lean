import Hypostructure.Graph.Replacement

/-!
# Graph replacement fixture

This fixture exercises the normalized replacement executor without an EG
instantiation.  The predecessor is a one-residual ledger carrying an arbitrary
minimal graph context; the context is read through Core's public residual
query and the replacement contradiction is appended by Graph's focused
executor.
-/

namespace Hypostructure.Fixtures.GraphReplacement

open Hypostructure

universe u v

abbrev Context (Baseline : Graph.FiniteObject.{u} -> Prop)
    (BranchState : Graph.FiniteObject.{u} -> Type v)
    (Target : Graph.FiniteObject.{u} -> Prop) :=
  Core.MinimalCounterexampleContext
    (Graph.problem Baseline BranchState) Target
    (Graph.lexicographicProgress Baseline BranchState)

abbrev Previous (Baseline : Graph.FiniteObject.{u} -> Prop)
    (BranchState : Graph.FiniteObject.{u} -> Type v)
    (Target : Graph.FiniteObject.{u} -> Prop) :=
  Core.Residual.Ledger (Context Baseline BranchState Target)

/-- The fixture uses Core's public always-active focus; it performs no local
branch routing. -/
abbrev focus (Baseline : Graph.FiniteObject.{u} -> Prop)
    (BranchState : Graph.FiniteObject.{u} -> Type v)
    (Target : Graph.FiniteObject.{u} -> Prop) :
    Core.Residual.Focus.Profile
      (Previous Baseline BranchState Target) :=
  Core.Residual.Focus.always
    (Previous Baseline BranchState Target)

/-- Read the exact predecessor context through the public residual query. -/
def contextQuery (Baseline : Graph.FiniteObject.{u} -> Prop)
    (BranchState : Graph.FiniteObject.{u} -> Type v)
    (Target : Graph.FiniteObject.{u} -> Prop) :
    Core.Residual.Focus.ActiveQuery
      (focus Baseline BranchState Target)
      (fun _previous _active => Context Baseline BranchState Target) :=
  Core.Residual.Focus.ActiveQuery.ofQuery
    (Core.Residual.Query.residual
      (Source := Previous Baseline BranchState Target)
      (Residual := Context Baseline BranchState Target))

variable {Baseline : Graph.FiniteObject.{u} -> Prop}
variable {BranchState : Graph.FiniteObject.{u} -> Type v}
variable {Target : Graph.FiniteObject.{u} -> Prop}

variable (profile : Graph.NormalizedAtomReplacementProfile Baseline)
variable (baselineInvariant :
  Graph.FiniteObject.IsomorphismInvariant Baseline)
variable (targetInvariant :
  Graph.FiniteObject.IsomorphismInvariant Target)

def runCounted (previous : Previous Baseline BranchState Target) :
    Core.Counted
      (Graph.FocusedNormalizedAtomReplacementStage
        (focus Baseline BranchState Target)
        (contextQuery Baseline BranchState Target) profile) :=
  Graph.executeFocusedNormalizedAtomReplacementCounted
    (focus Baseline BranchState Target)
    (contextQuery Baseline BranchState Target)
    profile baselineInvariant targetInvariant previous

def run (previous : Previous Baseline BranchState Target) :
    Graph.FocusedNormalizedAtomReplacementStage
      (focus Baseline BranchState Target)
      (contextQuery Baseline BranchState Target) profile :=
  (runCounted profile baselineInvariant targetInvariant previous).value

/-- Query the Graph-owned normalized replacement contradiction from the newest
ledger entry. -/
def claimQuery :
    Core.Residual.Focus.ActiveQuery
      (Core.Residual.ProofProjection.Profile
        (focus Baseline BranchState Target)
        (Graph.FocusedNormalizedAtomReplacementClaim
          (focus Baseline BranchState Target)
          (contextQuery Baseline BranchState Target) profile))
      (fun stage active =>
        Graph.FocusedNormalizedAtomReplacementClaim
          (focus Baseline BranchState Target)
          (contextQuery Baseline BranchState Target) profile
          stage.previous active) :=
  Graph.focusedNormalizedAtomReplacementQuery
    (focus Baseline BranchState Target)
    (contextQuery Baseline BranchState Target) profile

@[simp] theorem runCounted_checks_eq_zero
    (previous : Previous Baseline BranchState Target) :
    (runCounted profile baselineInvariant targetInvariant previous).checks =
      0 := by
  change
    (Graph.executeFocusedNormalizedAtomReplacementCounted
      (focus Baseline BranchState Target)
      (contextQuery Baseline BranchState Target)
      profile baselineInvariant targetInvariant previous).checks = 0
  rw [Graph.executeFocusedNormalizedAtomReplacementCounted_checks]
  rfl

theorem runCounted_work_bounded
    (previous : Previous Baseline BranchState Target) :
    (runCounted profile baselineInvariant targetInvariant previous).checks <=
      (Core.Residual.ProofProjection.workBudget
        (focus Baseline BranchState Target)).coefficient *
        ((Core.Residual.ProofProjection.workBudget
          (focus Baseline BranchState Target)).size previous + 1) ^
          (Core.Residual.ProofProjection.workBudget
            (focus Baseline BranchState Target)).degree :=
  Graph.executeFocusedNormalizedAtomReplacementCounted_checks_bounded
    (focus Baseline BranchState Target)
    (contextQuery Baseline BranchState Target)
    profile baselineInvariant targetInvariant previous

/-- The newest focused query exposes exactly the normalized replacement claim
installed by Graph. -/
theorem claim_available
    (baselineInvariant :
      Graph.FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant :
      Graph.FiniteObject.IsomorphismInvariant Target)
    (previous : Previous Baseline BranchState Target) :
    Graph.FocusedNormalizedAtomReplacementClaim
      (focus Baseline BranchState Target)
      (contextQuery Baseline BranchState Target) profile previous trivial :=
  (claimQuery profile).read
    (run profile baselineInvariant targetInvariant previous) trivial

#print axioms runCounted
#print axioms claimQuery
#print axioms runCounted_checks_eq_zero
#print axioms runCounted_work_bounded
#print axioms claim_available

end Hypostructure.Fixtures.GraphReplacement
