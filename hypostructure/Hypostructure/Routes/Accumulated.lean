import Hypostructure.Routes.Registry

/-!
# Generic accumulated-route facade

All generic accumulated edges share this constructor and executor.  A catalog
entry supplies identity only; a typed `Core.Routing.Profile` must separately
supply semantic discovery, target-input construction, and a real target
capability.  The executor delegates result construction to Core and therefore
retains the literal complete predecessor ledger.
-/

namespace Hypostructure.Routes.Accumulated

open Hypostructure.Core

universe uSource uInput uOutcome uTrace uSeed uBlocked uResidual

/-- Register one typed generic accumulated profile under a catalog identity.
The equality gate prevents specialized and merely planned-family rows from
using this facade. -/
def register (entry : Registry.Entry)
    (_generic : entry.kind = .genericAccumulated)
    (profile :
      Routing.Profile.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
        Source) :
    Routing.Transition.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
      entry.edge Source :=
  Routing.Transition.register entry.edge profile

/-- Execute a registered accumulated profile on the literal complete source
stage.  Core owns discovery, target execution, provenance, and the sole ledger
extension. -/
def advance {entry : Registry.Entry}
    (transition :
      Routing.Transition.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
        entry.edge Source)
    (source : Source) : Routing.Stage transition :=
  Routing.advance transition source

/-- The generic facade preserves the exact predecessor definitionally. -/
@[simp] theorem advance_previous {entry : Registry.Entry}
    (transition :
      Routing.Transition.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
        entry.edge Source)
    (source : Source) :
    (advance transition source).previous = source :=
  Routing.advance_previous transition source

/-- The generated provenance is exactly the selected catalog edge. -/
theorem advance_provenance {entry : Registry.Entry}
    (transition :
      Routing.Transition.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
        entry.edge Source)
    (source : Source) :
    (advance transition source).added.provenance.recorded = entry.edge :=
  Routing.advance_provenance transition source

/-- Semantic discovery stored by the result is exactly the registered
profile's discovery. -/
theorem advance_canonical {entry : Registry.Entry}
    (transition :
      Routing.Transition.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
        entry.edge Source)
    (source : Source) :
    (advance transition source).added.discovery =
      transition.profile.discover (advance transition source).previous :=
  Routing.advance_canonical transition source

/-- The stable root residual remains reachable through the complete extended
ledger. -/
@[simp] theorem advance_residual {entry : Registry.Entry}
    {ResidualType : Type uResidual}
    [Residual.HasResidual Source ResidualType]
    (transition :
      Routing.Transition.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
        entry.edge Source)
    (source : Source) :
    Residual.residualOf (advance transition source) =
      Residual.residualOf source :=
  Routing.advance_residual transition source

end Hypostructure.Routes.Accumulated
