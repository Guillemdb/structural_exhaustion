import Mathlib

/-!
# Hypostructure Core prelude

This module is the root of the domain-independent import graph.  It deliberately
contains no proof-domain declarations: Graph and PDE specializations build on
Core, never the reverse.
-/

namespace Hypostructure

namespace Core

/-- A stable identifier for a framework capability or execution profile. -/
abbrev CapabilityId := String

/-- A stable identifier for a residual kind exported by a framework executor. -/
abbrev ResidualKindId := String

end Core

end Hypostructure
