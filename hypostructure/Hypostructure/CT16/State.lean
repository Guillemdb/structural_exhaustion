import Hypostructure.CT16.Capability
import Hypostructure.Core.Finite.Search

/-!
# CT16 generated states

The support residual reuses Core's canonical first-hit certificate.  Whole
support reuses Core's exact exhaustive-avoidance proposition.
-/

namespace Hypostructure.CT16

universe uPrevious uCoordinate uCode

/-- Canonical first coordinate missing from the exact incoming schedule. -/
abbrev ProperSupportResidual {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.IndexedHit (capability.coordinatesAt previous)
    (fun coordinate => Not (spec.InSupport previous coordinate))

/-- Exhaustive absence of a missing coordinate on the exact schedule. -/
abbrev WholeSupportState {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.Avoids (capability.coordinatesAt previous)
    (fun coordinate => Not (spec.InSupport previous coordinate))

namespace ProperSupportResidual

/-- The generated coordinate is an exact member of the incoming schedule. -/
theorem member {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec} {previous : Previous}
    (residual : ProperSupportResidual capability previous) :
    residual.value ∈ (capability.coordinatesAt previous).values :=
  Core.Finite.Search.IndexedHit.member residual

/-- The generated coordinate is absent from the support. -/
theorem absent {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec} {previous : Previous}
    (residual : ProperSupportResidual capability previous) :
    Not (spec.InSupport previous residual.value) :=
  Core.Finite.Search.IndexedHit.sound residual

/-- Every scheduled coordinate before the first missing coordinate is present. -/
theorem beforePresent {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec} {previous : Previous}
    (residual : ProperSupportResidual capability previous) :
    forall coordinate,
      coordinate ∈ (capability.coordinatesAt previous).values.take
        residual.index.1 ->
      spec.InSupport previous coordinate := by
  intro coordinate member
  by_cases present : spec.InSupport previous coordinate
  · exact present
  · exact (Core.Finite.Search.IndexedHit.first residual
      coordinate member present).elim

end ProperSupportResidual

namespace WholeSupportState

/-- Exhaustive avoidance proves support at every scheduled coordinate. -/
theorem covers {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec} {previous : Previous}
    (state : WholeSupportState capability previous) :
    WholeSupport spec previous (capability.coordinatesAt previous) := by
  intro coordinate member
  obtain ⟨index, equal⟩ :=
    ((capability.coordinatesAt previous).mem_iff_exists_index coordinate).mp
      member
  by_cases present : spec.InSupport previous coordinate
  · exact present
  · exact (state index (by simpa [equal] using present)).elim

end WholeSupportState

/-- The unique code computed directly after whole support is established. -/
structure ClosedCodeState {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) where
  private mk ::
  whole : WholeSupportState capability previous
  code : spec.ClosedCode previous
  exact : code = spec.closedCode previous

/-- Compute the closed code once, without enumerating candidate codes. -/
def computeClosedCode {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous)
    (whole : WholeSupportState capability previous) :
    ClosedCodeState capability previous :=
  .mk whole (spec.closedCode previous) rfl

/-- Whole-support state with a literal target-code equality. -/
structure ExactCodeCertificate {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) where
  private mk ::
  state : ClosedCodeState capability previous
  equal : state.code = spec.targetCode previous

namespace ExactCodeCertificate

/-- Package the equality selected by Core's literal code decision. -/
def ofEquality {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec} {previous : Previous}
    (state : ClosedCodeState capability previous)
    (equal : state.code = spec.targetCode previous) :
    ExactCodeCertificate capability previous :=
  .mk state equal

end ExactCodeCertificate

/-- Whole-support state whose computed code differs from the target code. -/
structure ClosedTypeMismatchResidual {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) where
  private mk ::
  state : ClosedCodeState capability previous
  notEqual : state.code ≠ spec.targetCode previous

namespace ClosedTypeMismatchResidual

/-- Package the complement selected by Core's literal code decision. -/
def ofInequality {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec} {previous : Previous}
    (state : ClosedCodeState capability previous)
    (notEqual : state.code ≠ spec.targetCode previous) :
    ClosedTypeMismatchResidual capability previous :=
  .mk state notEqual

end ClosedTypeMismatchResidual

end Hypostructure.CT16
