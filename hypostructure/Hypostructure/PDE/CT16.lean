import Hypostructure.CT16.Automation
import Hypostructure.PDE.Model

/-!
# PDE adapter for CT16 compactified support

PDE supplies represented-object support and code semantics over an explicit
residual-owned coordinate schedule.  No window, profile, state, or code
carrier is manufactured by this adapter.
-/

namespace Hypostructure.PDE.CT16

universe u uPrevious uCoordinate uCode

/-- CT16 semantics for a represented PDE object and finite compactification
coordinates already present in the predecessor ledger. -/
def compactifiedSpec {Previous : Type uPrevious}
    (M : LocalModel.{u})
    (object : Core.Residual.Query Previous fun _previous =>
      M.problem.Ambient)
    (Coordinate : Type uCoordinate)
    (InSupport : M.problem.Ambient -> Coordinate -> Prop)
    (ClosedCode : Type uCode)
    (closedCode : M.problem.Ambient -> ClosedCode)
    (targetCode : ClosedCode) :
    _root_.Hypostructure.CT16.Spec Previous where
  Coordinate := fun _previous => Coordinate
  InSupport := fun previous coordinate =>
    InSupport (object.read previous) coordinate
  ClosedCode := fun _previous => ClosedCode
  closedCode := fun previous => closedCode (object.read previous)
  targetCode := fun _previous => targetCode

/-- Build the PDE CT16 capability from the one residual-owned coordinate
query and primitive semantic decisions. -/
def compactifiedCapability {Previous : Type uPrevious}
    (M : LocalModel.{u})
    (object : Core.Residual.Query Previous fun _previous =>
      M.problem.Ambient)
    (Coordinate : Type uCoordinate)
    (coordinates : Core.Residual.Query Previous fun _previous =>
      Core.Finite.Enumeration Coordinate)
    (InSupport : M.problem.Ambient -> Coordinate -> Prop)
    (ClosedCode : Type uCode)
    (closedCode : M.problem.Ambient -> ClosedCode)
    (targetCode : ClosedCode)
    (inSupportDecidable : (selected : M.problem.Ambient) ->
      (coordinate : Coordinate) -> Decidable (InSupport selected coordinate))
    (codeDecidableEq : DecidableEq ClosedCode) :
    _root_.Hypostructure.CT16.Capability
      (compactifiedSpec M object Coordinate InSupport ClosedCode
        closedCode targetCode) where
  coordinates := coordinates
  inSupportDecidable := fun previous coordinate =>
    inSupportDecidable (object.read previous) coordinate
  codeDecidableEq := fun _previous => codeDecidableEq

end Hypostructure.PDE.CT16
