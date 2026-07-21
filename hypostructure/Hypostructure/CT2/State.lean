import Hypostructure.CT2.Capability

/-!
# CT2 local-deletion states

The positive state is semantic evidence for the unique selected deletion.
The complementary residual is exactly the negation of eligibility for that
same residual-selected piece.
-/

namespace Hypostructure.CT2

universe uAmbient uBranch uMeasure uPrevious uPiece

/-- The exact evidence produced when the selected local deletion is eligible. -/
structure DeletionWitness
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) : Prop where
  private mk ::
  baseline : P.Baseline
    (spec.delete (capability.selectedPiece previous))
  avoids : Not (Target
    (spec.delete (capability.selectedPiece previous)))
  decreases : progress.Smaller
    (spec.delete (capability.selectedPiece previous))
    (capability.contextAt previous).G

/-- The exact residual emitted when the selected deletion is unavailable. -/
abbrev CriticalityState
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous) :=
  Not (capability.Eligible previous)

namespace DeletionWitness

/-- Minimality closes the exact smaller target-avoiding deletion. -/
theorem contradiction
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    {capability : Capability Target progress spec} {previous : Previous}
    (witness : DeletionWitness capability previous) : False :=
  witness.avoids <|
    (capability.contextAt previous).target_of_smaller
      witness.decreases witness.baseline

end DeletionWitness

namespace Capability

/-- Derive the complete deletion witness from framework-selected eligibility. -/
def deletionWitness
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {spec : Spec.{uAmbient, uBranch, uPrevious, uPiece} P Previous}
    (capability : Capability Target progress spec) (previous : Previous)
    (eligible : capability.Eligible previous) :
    DeletionWitness capability previous where
  baseline := capability.preservesBaseline
    (capability.contextAt previous).state
    (capability.selectedPiece previous) eligible.1 eligible.2
    (capability.contextAt previous).baseline
  avoids := fun reducedTarget =>
    (capability.contextAt previous).avoids <|
      capability.targetMonotone
        (capability.contextAt previous).state
        (capability.selectedPiece previous) eligible.1 eligible.2
        (capability.contextAt previous).baseline reducedTarget
  decreases := capability.decreases
    (capability.contextAt previous).state
    (capability.selectedPiece previous) eligible.1 eligible.2

end Capability

end Hypostructure.CT2
