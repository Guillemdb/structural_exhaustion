import StructuralExhaustion.Core.Problem
import StructuralExhaustion.Core.Context
import StructuralExhaustion.Core.MinimalSelection
import StructuralExhaustion.Core.Enumeration
import StructuralExhaustion.Core.FiniteSearch
import StructuralExhaustion.Core.ExactObservation
import StructuralExhaustion.Core.SmallerObject
import StructuralExhaustion.Core.Routing
import StructuralExhaustion.Core.Provision
import StructuralExhaustion.Core.WorkBudget

/-!
Umbrella import for the automation-first Structural Exhaustion core.

The module intentionally imports no CT implementation.  Problem instances and
all closure tactics depend on this layer; this layer never depends on them.
-/
