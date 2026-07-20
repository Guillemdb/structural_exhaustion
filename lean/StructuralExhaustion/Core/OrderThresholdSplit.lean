import Mathlib.Order.Defs.LinearOrder
import StructuralExhaustion.Core.ResidualRefinement
import StructuralExhaustion.Core.ZeroWorkBudget

namespace StructuralExhaustion.Core.OrderThresholdSplit

/-!
# Proof-level ordered threshold splits

This profile owns the exhaustive dichotomy `threshold ≤ value` or
`value < threshold` for any linear order.  It is a logical branch constructor,
not an evaluator: applications may use symbolic real-valued quantities without
normalizing or computing them.
-/

universe u

structure Profile (α : Type u) [LinearOrder α] where
  value : α
  threshold : α

namespace Profile

variable {α : Type u} [LinearOrder α]

inductive Outcome (profile : Profile α) : Type
  | high (bound : profile.threshold ≤ profile.value)
  | low (strict : profile.value < profile.threshold)

def run (profile : Profile α) : profile.Outcome :=
  if high : profile.threshold ≤ profile.value then
    .high high
  else
    .low (lt_of_not_ge high)

theorem exhaustive (profile : Profile α) :
    profile.threshold ≤ profile.value ∨ profile.value < profile.threshold :=
  le_or_gt profile.threshold profile.value

/-- A proof-level threshold split performs no primitive finite inspection. -/
def workBudget (_profile : Profile α) : PolynomialCheckBudget Unit :=
  PolynomialCheckBudget.zero (fun _ => 0)

@[simp] theorem checks_eq_zero (profile : Profile α) :
    profile.workBudget.checks () = 0 :=
  rfl

structure VerifiedStage (profile : Profile α) : Type where
  outcome : profile.Outcome
  total : profile.threshold ≤ profile.value ∨ profile.value < profile.threshold
  work : profile.workBudget.checks () = 0

def verifiedStage (profile : Profile α) : profile.VerifiedStage where
  outcome := profile.run
  total := profile.exhaustive
  work := profile.checks_eq_zero

end Profile

/-! ## Accumulated predecessor execution -/

universe uResidual uPrevious uOrder

/-- A threshold profile whose compared values are determined by one literal
predecessor stage. Applications provide only those values; the framework owns
ledger retrieval and exact branch retention. -/
structure DependentProfileFamily
    (Residual : Type uResidual) (Previous : Residual → Type uPrevious)
    (α : Type uOrder) [LinearOrder α] where
  profile : (residual : Residual) → Previous residual → Profile α

namespace DependentProfileFamily

variable {α : Type uOrder} [LinearOrder α]
variable {Residual : Type uResidual} {Previous : Residual → Type uPrevious}

def High (family : DependentProfileFamily Residual Previous α)
    (residual : Residual) (previous : Previous residual) : Prop :=
  (family.profile residual previous).threshold ≤
    (family.profile residual previous).value

def Low (family : DependentProfileFamily Residual Previous α)
    (residual : Residual) (previous : Previous residual) : Prop :=
  (family.profile residual previous).value <
    (family.profile residual previous).threshold

/-- Strict upper-side predicate used when a manuscript labels
`threshold < value` as its positive branch. -/
def StrictHigh (family : DependentProfileFamily Residual Previous α)
    (residual : Residual) (previous : Previous residual) : Prop :=
  (family.profile residual previous).threshold <
    (family.profile residual previous).value

/-- Complement of `StrictHigh`, retaining the exact weak upper bound. -/
def AtMost (family : DependentProfileFamily Residual Previous α)
    (residual : Residual) (previous : Previous residual) : Prop :=
  (family.profile residual previous).value ≤
    (family.profile residual previous).threshold

/-- Exact exhaustive threshold decision attached to the literal predecessor
retrieved from the one accumulated ledger. -/
abbrev Decision (family : DependentProfileFamily Residual Previous α)
    (residual : Residual) :=
  ResidualRefinement.State.DependentDecision Previous family.High family.Low
    residual

/-- Execute a predecessor-dependent threshold split without exposing ledger
routing or an application-owned branch carrier. -/
noncomputable def executeUsingStage
    (family : DependentProfileFamily Residual Previous α) {facts}
    [ResidualRefinement.Proofs.Contains
      (ResidualRefinement.State.Available Previous) facts] :
    ResidualRefinement.State.StageNode (facts := facts) family.Decision := by
  classical
  exact ResidualRefinement.State.StageNode.decideUsingStage
    (fun _residual _previous => inferInstance)
    (fun _residual _previous absent => lt_of_not_ge absent)

/-- The strict/complementary orientation of the same framework-owned split.
This prevents applications from rebuilding a branch carrier merely because
their diagram names the strict inequality as the yes edge. -/
abbrev StrictDecision
    (family : DependentProfileFamily Residual Previous α)
    (residual : Residual) :=
  ResidualRefinement.State.DependentDecision Previous family.StrictHigh
    family.AtMost residual

noncomputable def executeStrictUsingStage
    (family : DependentProfileFamily Residual Previous α) {facts}
    [ResidualRefinement.Proofs.Contains
      (ResidualRefinement.State.Available Previous) facts] :
    ResidualRefinement.State.StageNode (facts := facts)
      family.StrictDecision := by
  classical
  exact ResidualRefinement.State.StageNode.decideUsingStage
    (fun _residual _previous => inferInstance)
    (fun _residual _previous absent => le_of_not_gt absent)

theorem exhaustive (family : DependentProfileFamily Residual Previous α)
    {residual : Residual} (previous : Previous residual) :
    family.High residual previous ∨ family.Low residual previous :=
  (family.profile residual previous).exhaustive

theorem strictExhaustive
    (family : DependentProfileFamily Residual Previous α)
    {residual : Residual} (previous : Previous residual) :
    family.StrictHigh residual previous ∨ family.AtMost residual previous :=
  lt_or_ge _ _

/-- The proof-level split performs no finite inspection beyond its inherited
predecessor stage. -/
def workBudget (_family : DependentProfileFamily Residual Previous α) :
    PolynomialCheckBudget Unit :=
  PolynomialCheckBudget.zero (fun _ => 0)

@[simp] theorem checks_eq_zero
    (family : DependentProfileFamily Residual Previous α) :
    family.workBudget.checks () = 0 :=
  rfl

end DependentProfileFamily

/-! ## Threshold decisions on an existing negative-leaf payload -/

structure DependentNoContinuationProfileFamily
    (Residual : Type uResidual) (Previous : Residual → Type uPrevious)
    (OuterNo : (residual : Residual) → Previous residual → Prop)
    (Output : (residual : Residual) → (previous : Previous residual) →
      OuterNo residual previous → Type*)
    (α : Type uOrder) [LinearOrder α] where
  profile : (residual : Residual) → (previous : Previous residual) →
    (outerProof : OuterNo residual previous) →
    Output residual previous outerProof → Profile α

namespace DependentNoContinuationProfileFamily

variable {α : Type uOrder} [LinearOrder α]
variable {Residual : Type uResidual} {Previous : Residual → Type uPrevious}
variable {OuterYes OuterNo : (residual : Residual) → Previous residual → Prop}
variable {Output : (residual : Residual) → (previous : Previous residual) →
  OuterNo residual previous → Type*}

def StrictHigh
    (family : DependentNoContinuationProfileFamily Residual Previous
      OuterNo Output α)
    (residual : Residual) (previous : Previous residual)
    (outerProof : OuterNo residual previous)
    (output : Output residual previous outerProof) : Prop :=
  (family.profile residual previous outerProof output).threshold <
    (family.profile residual previous outerProof output).value

def AtMost
    (family : DependentNoContinuationProfileFamily Residual Previous
      OuterNo Output α)
    (residual : Residual) (previous : Previous residual)
    (outerProof : OuterNo residual previous)
    (output : Output residual previous outerProof) : Prop :=
  (family.profile residual previous outerProof output).value ≤
    (family.profile residual previous outerProof output).threshold

abbrev Decision
    (OuterYes : (residual : Residual) → Previous residual → Prop)
    (family : DependentNoContinuationProfileFamily Residual Previous
      OuterNo Output α) (residual : Residual) :=
  ResidualRefinement.State.DependentDecisionOnNoContinuation Previous
    OuterYes OuterNo Output family.StrictHigh family.AtMost residual

noncomputable def executeStrictUsingNoContinuation
    (family : DependentNoContinuationProfileFamily Residual Previous
      OuterNo Output α) {facts}
    [ResidualRefinement.Proofs.Contains
      (ResidualRefinement.State.Available
        (ResidualRefinement.State.DependentDecisionNoContinuation Previous
          OuterYes OuterNo Output)) facts] :
    ResidualRefinement.State.StageNode (facts := facts)
      (family.Decision OuterYes) := by
  classical
  exact ResidualRefinement.State.StageNode.decideOnDependentNoContinuation
    (fun _residual _previous _outerProof _output => inferInstance)
    (fun _residual _previous _outerProof _output absent => le_of_not_gt absent)

theorem strictExhaustive
    (family : DependentNoContinuationProfileFamily Residual Previous
      OuterNo Output α)
    {residual : Residual} (previous : Previous residual)
    (outerProof : OuterNo residual previous)
    (output : Output residual previous outerProof) :
    family.StrictHigh residual previous outerProof output ∨
      family.AtMost residual previous outerProof output :=
  lt_or_ge _ _

def workBudget
    (_family : DependentNoContinuationProfileFamily Residual Previous
      OuterNo Output α) : PolynomialCheckBudget Unit :=
  PolynomialCheckBudget.zero (fun _ => 0)

@[simp] theorem checks_eq_zero
    (family : DependentNoContinuationProfileFamily Residual Previous
      OuterNo Output α) : family.workBudget.checks () = 0 := rfl

end DependentNoContinuationProfileFamily

end StructuralExhaustion.Core.OrderThresholdSplit
