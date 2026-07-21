import Hypostructure.CT2.State
import Hypostructure.Core.Residual.Decision

/-!
# CT2 reference decision

The reference machine performs exactly one decision on the piece selected by
the predecessor's bounded index.  Core constructs the binary route and its
complementary criticality proof.
-/

namespace Hypostructure.CT2

universe uAmbient uBranch uMeasure uPrevious uPiece

/-- Core-owned decision node for selected-piece eligibility. -/
def decisionNode
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) :
    Core.Residual.Decision.Node Previous
      capability.Eligible (CriticalityState capability) :=
  Core.Residual.Decision.Node.complement capability.Eligible
    capability.eligibleDecidable

/-- The exact Core decision stage emitted by CT2. -/
abbrev RoutedDecision
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) :=
  Core.Residual.Decision.Stage
    capability.Eligible (CriticalityState capability)

/-- Execute the unique selected-piece dichotomy on the literal predecessor. -/
def route
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) :
    RoutedDecision capability :=
  (decisionNode capability).run previous

@[simp] theorem route_previous
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) :
    (route capability previous).previous = previous :=
  rfl

end Hypostructure.CT2
