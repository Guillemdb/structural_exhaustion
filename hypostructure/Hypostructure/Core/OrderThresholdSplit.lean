import Mathlib.Order.Defs.LinearOrder
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Residual.Decision

/-!
# Symbolic ordered threshold splits

This module owns proof-level dichotomies of the form `threshold < value` versus
`value <= threshold`, or `threshold <= value` versus `value < threshold`.  It
does not evaluate the compared expressions; applications provide only the
expressions attached to the literal predecessor.
-/

namespace Hypostructure.Core.OrderThresholdSplit

universe u uResidual uPrevious uOutput uOrder

/-- A pair of ordered quantities to compare. -/
structure Profile (α : Type u) [LinearOrder α] where
  value : α
  threshold : α

namespace Profile

variable {α : Type u} [LinearOrder α]

inductive Outcome (profile : Profile α) : Type u
  | high (bound : profile.threshold <= profile.value)
  | low (strict : profile.value < profile.threshold)

def run (profile : Profile α) : profile.Outcome :=
  if high : profile.threshold <= profile.value then
    .high high
  else
    .low (lt_of_not_ge high)

theorem exhaustive (profile : Profile α) :
    profile.threshold <= profile.value ∨ profile.value < profile.threshold :=
  le_or_gt profile.threshold profile.value

def workBudget (_profile : Profile α) : PolynomialCheckBudget Unit :=
  PolynomialCheckBudget.proofOnly Unit

@[simp] theorem checks_eq_zero (profile : Profile α) :
    profile.workBudget.checks () = 0 :=
  rfl

structure VerifiedStage (profile : Profile α) : Type u where
  outcome : profile.Outcome
  exhaustive : profile.threshold <= profile.value ∨
    profile.value < profile.threshold
  work : profile.workBudget.checks () = 0

def verifiedStage (profile : Profile α) : profile.VerifiedStage where
  outcome := profile.run
  exhaustive := profile.exhaustive
  work := profile.checks_eq_zero

end Profile

/-- A threshold profile whose expressions are read from one literal
predecessor. -/
structure DependentProfileFamily
    (Res : Type uResidual) (Previous : Res -> Type uPrevious)
    (α : Type uOrder) [LinearOrder α] where
  profile : (residual : Res) -> Previous residual -> Profile α

namespace DependentProfileFamily

variable {α : Type uOrder} [LinearOrder α]
variable {Res : Type uResidual} {Previous : Res -> Type uPrevious}

def High (family : DependentProfileFamily Res Previous α)
    (residual : Res) (previous : Previous residual) : Prop :=
  (family.profile residual previous).threshold <=
    (family.profile residual previous).value

def Low (family : DependentProfileFamily Res Previous α)
    (residual : Res) (previous : Previous residual) : Prop :=
  (family.profile residual previous).value <
    (family.profile residual previous).threshold

def StrictHigh (family : DependentProfileFamily Res Previous α)
    (residual : Res) (previous : Previous residual) : Prop :=
  (family.profile residual previous).threshold <
    (family.profile residual previous).value

def AtMost (family : DependentProfileFamily Res Previous α)
    (residual : Res) (previous : Previous residual) : Prop :=
  (family.profile residual previous).value <=
    (family.profile residual previous).threshold

abbrev Decision (family : DependentProfileFamily Res Previous α)
    (residual : Res) :=
  Residual.Decision.Stage (family.High residual) (family.Low residual)

def decisionNode (family : DependentProfileFamily Res Previous α)
    (residual : Res) :
  Residual.Decision.Node (Previous residual)
      (family.High residual) (family.Low residual) :=
  Residual.Decision.Node.create
    (fun previous => by
      unfold High
      infer_instance)
    (fun _previous absent => lt_of_not_ge absent)

def execute (family : DependentProfileFamily Res Previous α)
    {residual : Res} (previous : Previous residual) :
    family.Decision residual :=
  (family.decisionNode residual).run previous

abbrev StrictDecision
    (family : DependentProfileFamily Res Previous α)
    (residual : Res) :=
  Residual.Decision.Stage (family.StrictHigh residual) (family.AtMost residual)

def strictDecisionNode (family : DependentProfileFamily Res Previous α)
    (residual : Res) :
  Residual.Decision.Node (Previous residual)
      (family.StrictHigh residual) (family.AtMost residual) :=
  Residual.Decision.Node.create
    (fun previous => by
      unfold StrictHigh
      infer_instance)
    (fun _previous absent => le_of_not_gt absent)

def executeStrict (family : DependentProfileFamily Res Previous α)
    {residual : Res} (previous : Previous residual) :
    family.StrictDecision residual :=
  (family.strictDecisionNode residual).run previous

theorem exhaustive (family : DependentProfileFamily Res Previous α)
    {residual : Res} (previous : Previous residual) :
    family.High residual previous ∨ family.Low residual previous :=
  (family.profile residual previous).exhaustive

theorem strictExhaustive
    (family : DependentProfileFamily Res Previous α)
    {residual : Res} (previous : Previous residual) :
    family.StrictHigh residual previous ∨ family.AtMost residual previous :=
  lt_or_ge _ _

def workBudget (_family : DependentProfileFamily Res Previous α) :
    PolynomialCheckBudget Unit :=
  PolynomialCheckBudget.proofOnly Unit

@[simp] theorem checks_eq_zero
    (family : DependentProfileFamily Res Previous α) :
    family.workBudget.checks () = 0 :=
  rfl

end DependentProfileFamily

/-- A strict threshold split on the payload of an already continued negative
branch.  The outer positive sibling remains in the predecessor decision stage. -/
structure DependentNoContinuationProfileFamily
    (Res : Type uResidual) (Previous : Res -> Type uPrevious)
    (OuterNo : (residual : Res) -> Previous residual -> Prop)
    (Output : (residual : Res) -> (previous : Previous residual) ->
      OuterNo residual previous -> Type uOutput)
    (α : Type uOrder) [LinearOrder α] where
  profile : (residual : Res) -> (previous : Previous residual) ->
    (outerProof : OuterNo residual previous) ->
    Output residual previous outerProof -> Profile α

namespace DependentNoContinuationProfileFamily

variable {α : Type uOrder} [LinearOrder α]
variable {Res : Type uResidual} {Previous : Res -> Type uPrevious}
variable {OuterYes OuterNo : (residual : Res) ->
  Previous residual -> Prop}
variable {Output : (residual : Res) -> (previous : Previous residual) ->
  OuterNo residual previous -> Type uOutput}

def StrictHigh
    (family : DependentNoContinuationProfileFamily Res Previous
      OuterNo Output α)
    (residual : Res) (previous : Previous residual)
    (outerProof : OuterNo residual previous)
    (output : Output residual previous outerProof) : Prop :=
  (family.profile residual previous outerProof output).threshold <
    (family.profile residual previous outerProof output).value

def AtMost
    (family : DependentNoContinuationProfileFamily Res Previous
      OuterNo Output α)
    (residual : Res) (previous : Previous residual)
    (outerProof : OuterNo residual previous)
    (output : Output residual previous outerProof) : Prop :=
  (family.profile residual previous outerProof output).value <=
    (family.profile residual previous outerProof output).threshold

abbrev Decision
    (OuterYes : (residual : Res) -> Previous residual -> Prop)
    (family : DependentNoContinuationProfileFamily Res Previous
      OuterNo Output α) (residual : Res) :=
  Residual.Decision.NoContinuationSuccessorStage
    (Yes := OuterYes residual) (No := OuterNo residual)
    (CurrentYes := fun _previous _proof => PUnit)
    (CurrentNo := fun previous proof => Output residual previous proof)
    (fun previous proof output =>
      Residual.Decision.Stage
        (fun _unit : PUnit => family.StrictHigh residual previous proof output)
        (fun _unit : PUnit => family.AtMost residual previous proof output))

theorem strictExhaustive
    (family : DependentNoContinuationProfileFamily Res Previous
      OuterNo Output α)
    {residual : Res} (previous : Previous residual)
    (outerProof : OuterNo residual previous)
    (output : Output residual previous outerProof) :
    family.StrictHigh residual previous outerProof output ∨
      family.AtMost residual previous outerProof output :=
  lt_or_ge _ _

def workBudget
    (_family : DependentNoContinuationProfileFamily Res Previous
      OuterNo Output α) : PolynomialCheckBudget Unit :=
  PolynomialCheckBudget.proofOnly Unit

@[simp] theorem checks_eq_zero
    (family : DependentNoContinuationProfileFamily Res Previous
      OuterNo Output α) : family.workBudget.checks () = 0 :=
  rfl

end DependentNoContinuationProfileFamily

end Hypostructure.Core.OrderThresholdSplit
