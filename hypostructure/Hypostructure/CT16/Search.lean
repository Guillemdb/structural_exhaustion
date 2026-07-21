import Hypostructure.CT16.State
import Hypostructure.Core.Finite.Accounting

/-!
# CT16 support scan and code decision

Both executable branches are selected by Core machinery.  CT16 specializes
the generic first-hit scan to missing support and the generic complement
decision to literal equality of the one computed code.
-/

namespace Hypostructure.CT16

universe uPrevious uCoordinate uCode

/-- Decidability of missing support derived from primitive support decisions. -/
def missingDecidable {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous)
    (coordinate : spec.Coordinate previous) :
    Decidable (Not (spec.InSupport previous coordinate)) :=
  match capability.inSupportDecidable previous coordinate with
  | .isTrue present => .isFalse fun absent => absent present
  | .isFalse absent => .isTrue absent

/-- Canonical counted scan for the first missing support coordinate. -/
def countedSupportScan {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.coordinatesAt previous)
      (fun coordinate => Not (spec.InSupport previous coordinate))) :=
  Core.Finite.Accounting.countedRun (capability.coordinatesAt previous)
    (fun coordinate => Not (spec.InSupport previous coordinate))
    (missingDecidable capability previous)

/-- Exact support-search execution. -/
def supportScan {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :=
  (countedSupportScan spec capability previous).value

/-- Exact visible support checks. -/
def supportChecks {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) : Nat :=
  (countedSupportScan spec capability previous).checks

/-- Core-owned support route: yes means first missing coordinate; no means
whole support on the exact schedule. -/
abbrev RoutedSupport {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (capability.coordinatesAt previous)
        (fun coordinate => Not (spec.InSupport previous coordinate)) =>
      execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (capability.coordinatesAt previous)
        (fun coordinate => Not (spec.InSupport previous coordinate)) =>
      WholeSupportState capability previous)

/-- Route the support scan through Core's first-hit decision executor. -/
def routeSupport {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    RoutedSupport spec capability previous :=
  Core.Finite.Search.route (supportScan spec capability previous)

/-- Core's literal equality/complement route for one computed code. -/
abbrev RoutedCode {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) :=
  Core.Residual.Decision.Stage
    (fun state : ClosedCodeState capability previous =>
      state.code = spec.targetCode previous)
    (fun state : ClosedCodeState capability previous =>
      state.code ≠ spec.targetCode previous)

/-- The generic proposition-versus-complement code decision. -/
def codeDecisionNode {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) :
    Core.Residual.Decision.Node (ClosedCodeState capability previous)
      (fun state => state.code = spec.targetCode previous)
      (fun state => state.code ≠ spec.targetCode previous) :=
  Core.Residual.Decision.Node.complement
    (fun state : ClosedCodeState capability previous =>
      state.code = spec.targetCode previous)
    (fun state => capability.codeDecidableEq previous
      state.code (spec.targetCode previous))

/-- Compare exactly the computed code with the literal target code. -/
def routeCode {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous)
    (state : ClosedCodeState capability previous) :
    RoutedCode capability previous :=
  (codeDecisionNode capability previous).run state

theorem supportChecks_le_card {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    supportChecks spec capability previous ≤
      (capability.coordinatesAt previous).card :=
  Core.Finite.Accounting.executionChecks_le_card
    (supportScan spec capability previous)

end Hypostructure.CT16
