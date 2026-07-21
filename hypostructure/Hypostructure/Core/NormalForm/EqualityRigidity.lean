import Hypostructure.Core.NormalForm.ClassClosure

/-!
# Equality-rigidity normal form

Equality-rigidity is the class-closure executor specialized to an exact
predecessor-owned equality family.  Saturation identities and an optional
separator remain typed predecessor queries and participate in the visibility
predicate; they are never copied into a successor object.  All scanning,
branching, ledger extension, and quotient propagation are delegated to the
generic class-closure machine.
-/

namespace Hypostructure.Core.NormalForm.EqualityRigidity

open Hypostructure.Core

universe uPrevious uCarrier uQuotient uNextQuotient uSaturation uSeparator

/-- Generic equality data sufficient to instantiate class closure. -/
structure Profile (Previous : Type uPrevious) where
  Carrier : Type uCarrier
  closure : ClosureOperator Carrier
  TargetNull : Carrier -> Prop
  equalityFamily : Residual.Query Previous fun _previous =>
    Finite.Enumeration Carrier
  ledger : Residual.Query Previous fun _previous =>
    ClosedClassLedger closure TargetNull
  quotient : (previous : Previous) ->
    LedgerQuotient.{uCarrier, uQuotient} (ledger.read previous)
  Saturation : Previous -> Type uSaturation
  saturation : Residual.Query Previous Saturation
  Separator : Previous -> Type uSeparator
  separator : Residual.Query Previous fun previous => Option (Separator previous)
  RigidityVisible : (previous : Previous) -> Saturation previous ->
    Option (Separator previous) -> (quotient previous).Quotient -> Prop
  rigidityVisibleDecidable : (previous : Previous) ->
    (quotientClass : (quotient previous).Quotient) ->
      Decidable (RigidityVisible previous (saturation.read previous)
        (separator.read previous) quotientClass)
  visibleNonzero : forall (previous : Previous) {carrier : Carrier},
    RigidityVisible previous (saturation.read previous)
        (separator.read previous) ((quotient previous).project carrier) ->
      Not ((quotient previous).project carrier = (quotient previous).null)
  nullOfNotVisible : forall (previous : Previous) (carrier : Carrier),
    Not (RigidityVisible previous (saturation.read previous)
      (separator.read previous) ((quotient previous).project carrier)) ->
      (quotient previous).project carrier = (quotient previous).null
  targetNullOfNull : forall (previous : Previous) (carrier : Carrier),
    (quotient previous).project carrier = (quotient previous).null ->
      TargetNull carrier
  closureStable : ClosureStable closure TargetNull

namespace Profile

variable {Previous : Type uPrevious}
  (profile : Profile.{uPrevious, uCarrier, uQuotient, uSaturation, uSeparator}
    Previous)

/-- Exact class-closure profile generated from equality-rigidity inputs. -/
def toClassClosure :
    ClassClosure.Profile.{uPrevious, uCarrier, uQuotient} Previous where
  Carrier := profile.Carrier
  closure := profile.closure
  TargetNull := profile.TargetNull
  family := profile.equalityFamily
  ledger := profile.ledger
  quotient := profile.quotient
  TargetVisible := fun previous quotientClass =>
    profile.RigidityVisible previous (profile.saturation.read previous)
      (profile.separator.read previous) quotientClass
  targetVisibleDecidable := profile.rigidityVisibleDecidable
  visibleNonzero := profile.visibleNonzero
  nullOfNotVisible := profile.nullOfNotVisible
  targetNullOfNull := profile.targetNullOfNull
  closureStable := profile.closureStable

end Profile

/-- Quotient registration for the enlarged equality ledger. -/
abbrev ExtensionRegistration {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient, uSaturation, uSeparator}
      Previous) :=
  ClassClosure.ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
    uNextQuotient} profile.toClassClosure

/-- Exact target-visible rigidity residual emitted by the shared executor. -/
abbrev TargetVisibleRigidityResidual {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient, uSaturation, uSeparator}
      Previous)
    (previous : Previous)
    (visible : profile.toClassClosure.HasTargetVisible previous) :=
  ClassClosure.TargetVisibleResidual profile.toClassClosure previous visible

/-- Zero-equality-quotient propagation emitted by the shared executor. -/
abbrev ZeroEqualityPropagation {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient, uSaturation, uSeparator}
      Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient, uSaturation, uSeparator} profile)
    (previous : Previous)
    (avoids : profile.toClassClosure.AvoidsTargetVisible previous) :=
  ClassClosure.ZeroQuotientPropagation profile.toClassClosure registration
    previous avoids

/-- Framework-owned equality-rigidity stage. -/
abbrev Stage {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient, uSaturation, uSeparator}
      Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient, uSaturation, uSeparator} profile) :=
  ClassClosure.Stage profile.toClassClosure registration

/-- Equality-specific names for the two shared class-closure terminals. -/
inductive Terminal where
  | zeroEqualityQuotient
  | targetVisibleRigidity
  deriving DecidableEq, Repr

/-- Execute equality-rigidity entirely through class-closure machinery. -/
def run {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient, uSaturation, uSeparator}
      Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient, uSaturation, uSeparator} profile)
    (previous : Previous) : Stage profile registration :=
  ClassClosure.run profile.toClassClosure registration previous

@[simp] theorem run_previous {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient, uSaturation, uSeparator}
      Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient, uSaturation, uSeparator} profile)
    (previous : Previous) :
    (run profile registration previous).previous.previous = previous :=
  rfl

/-- Observable equality terminal, derived from the shared Core decision. -/
def terminal {Previous : Type uPrevious}
    {profile : Profile.{uPrevious, uCarrier, uQuotient, uSaturation, uSeparator}
      Previous}
    {registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient, uSaturation, uSeparator} profile}
    (stage : Stage profile registration) : Terminal :=
  match ClassClosure.terminal stage with
  | .zeroQuotient => .zeroEqualityQuotient
  | .targetVisible => .targetVisibleRigidity

end Hypostructure.Core.NormalForm.EqualityRigidity
