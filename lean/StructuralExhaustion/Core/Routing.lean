import Std

namespace StructuralExhaustion.Core.Routing

universe uSeed

/-!
Constructive discovery used by executable CT transitions.  Target interfaces,
trigger construction, execution, and accumulated-ledger transport live
exclusively in `Core.CTTransition`.
-/

/-- Constructive capability discovery. -/
inductive Discovery (Seed : Type uSeed) where
  | enabled (seed : Seed)
  | disabled (reject : Seed → False)

namespace Discovery

def toOption {Seed : Type uSeed} : Discovery Seed → Option Seed
  | .enabled seed => some seed
  | .disabled _ => none

theorem enabled_sound {Seed : Type uSeed} (seed : Seed) :
    (Discovery.enabled seed).toOption = some seed :=
  rfl

theorem disabled_complete {Seed : Type uSeed} (reject : Seed → False) :
    (Discovery.disabled reject).toOption = none :=
  rfl

end Discovery

end StructuralExhaustion.Core.Routing
