import Hypostructure.CT12.Capability

/-!
# CT12 generated terminal states

Terminal evidence is typed by the exact predecessor.  The exhausted
certificate constructor is private, and complete routed results are private
in the execution layer, so applications cannot select a branch.
-/

namespace Hypostructure.CT12

universe uPrevious uState uPeeled uDemand uTier

/-- Exhaustive terminal grammar of CT12. -/
inductive Terminal where
  | exhausted
  | demand
  | tier
  deriving DecidableEq, Repr

/-- Audit nodes exposed by the canonical CT12 trace. -/
inductive NodeId where
  | entry
  | saturation
  | peel
  | restoration
  | decrease
  | exhaustedTerminal
  | demandTerminal
  | tierTerminal
  deriving DecidableEq, Repr

/-- Framework-generated evidence that peeling reached load zero. -/
structure ExhaustedCertificate
    {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (previous : Previous) where
  private mk ::
  state : spec.State previous 0

namespace ExhaustedCertificate

/-- Package the load-zero state reached by the framework runner. -/
def ofState
    {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous}
    {previous : Previous} (state : spec.State previous 0) :
    ExhaustedCertificate spec previous :=
  .mk state

end ExhaustedCertificate

/-- Terminal-indexed semantic output.  Demand and tier types are themselves
the application-supplied proof-carrying residual contracts. -/
inductive Outcome
    {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (previous : Previous) : Terminal -> Type _ where
  | exhausted (certificate : ExhaustedCertificate spec previous) :
      Outcome spec previous .exhausted
  | demand (residual : spec.DemandResidual previous) :
      Outcome spec previous .demand
  | tier (residual : spec.TierResidual previous) :
      Outcome spec previous .tier

end Hypostructure.CT12
