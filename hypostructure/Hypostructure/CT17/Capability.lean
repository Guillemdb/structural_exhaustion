import Hypostructure.CT17.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query

/-!
# CT17 executable capability

Targets, offsets, the active scale, its containing scale schedule, and the
position schedule at every queried scale are inherited ledger reads.  The
application supplies no detached candidate family and cannot select a route.
-/

namespace Hypostructure.CT17

universe uPrevious uTarget uOffset uPosition uValue

/-- Worst-case visible work for compatibility, scale routing, all finite block
comparisons, the orbit comparison, and orbit-value materialization. -/
def localCheckBound {Target : Type uTarget} {Offset : Type uOffset}
    {Position : Type uPosition}
    (targets : Core.Finite.Enumeration Target)
    (offsets : Core.Finite.Enumeration Offset)
    (positions : Core.Finite.Enumeration Position) : Nat :=
  let pairs := targets.card * offsets.card
  2 * pairs + positions.card * pairs + offsets.card + 2

/-- Minimal executable surface for bounded target thickening. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous) where
  targets : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Target previous)
  offsets : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Offset previous)
  scales : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Nat
  selectedScale : Core.Residual.Query Previous fun _previous => Nat
  selectedScale_mem : forall previous,
    selectedScale.read previous ∈ (scales.read previous).values
  positions : (scale : Nat) -> Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Position previous scale)
  finiteScaleLimit : Core.Residual.Query Previous fun _previous => Nat
  compatibleDecidable : (previous : Previous) ->
    (target : spec.Target previous) -> (offset : spec.Offset previous) ->
      Decidable (spec.Compatible previous target offset)
  valueDecidableEq : (previous : Previous) ->
    DecidableEq (spec.Value previous)
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    localCheckBound (targets.read previous) (offsets.read previous)
      ((positions (selectedScale.read previous)).read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree

namespace Capability

/-- Exact inherited target schedule. -/
def targetsAt {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous}
    (capability : Capability spec) (previous : Previous) :=
  capability.targets.read previous

/-- Exact inherited offset schedule, shared by block and orbit arithmetic. -/
def offsetsAt {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous}
    (capability : Capability spec) (previous : Previous) :=
  capability.offsets.read previous

/-- Exact inherited schedule of admissible scale values. -/
def scalesAt {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous}
    (capability : Capability spec) (previous : Previous) :=
  capability.scales.read previous

/-- Scale selected by the predecessor for this CT17 invocation. -/
def scaleAt {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous}
    (capability : Capability spec) (previous : Previous) : Nat :=
  capability.selectedScale.read previous

/-- Exact inherited position schedule at the selected scale. -/
def positionsAt {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous}
    (capability : Capability spec) (previous : Previous) :=
  (capability.positions (capability.scaleAt previous)).read previous

/-- Finite/orbit cutoff inherited from the predecessor. -/
def scaleLimitAt {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous}
    (capability : Capability spec) (previous : Previous) : Nat :=
  capability.finiteScaleLimit.read previous

/-- Target-major, offset-minor compatibility and arithmetic schedule. -/
def pairScheduleAt {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous}
    (capability : Capability spec) (previous : Previous) :=
  (capability.targetsAt previous).product (capability.offsetsAt previous)

/-- The selected scale is certified to belong to the predecessor-owned scale
schedule. -/
theorem scaleAt_mem {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous}
    (capability : Capability spec) (previous : Previous) :
    capability.scaleAt previous ∈ (capability.scalesAt previous).values :=
  capability.selectedScale_mem previous

/-- Framework-visible polynomial work envelope. -/
def polynomialBudget {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous}
    (capability : Capability spec) : Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := fun previous => localCheckBound
    (capability.targetsAt previous) (capability.offsetsAt previous)
    (capability.positionsAt previous)
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := capability.workBound

end Capability

end Hypostructure.CT17
