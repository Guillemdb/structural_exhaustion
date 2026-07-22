import Hypostructure.Graph.Contraction
import Hypostructure.Graph.DeletionCriticality
import Hypostructure.Graph.OneThreeRepair
import Hypostructure.Graph.RootedReturn
import Hypostructure.Graph.Target

/-!
# Reusable graph theorem profiles

This barrel exposes reusable graph theorem families that are built entirely
from the public Graph API and Core CTs.  It does not add any paper-specific
constants or application routing.
-/

namespace Hypostructure.Graph.Theorems

open Hypostructure.Graph

/-- Reusable cycle-target interface from the public graph target encoding. -/
def cycleTargetInterface (LengthOK : Nat → Prop) :=
  Hypostructure.Graph.cycleTargetInterface LengthOK

/-- Reusable one-three repair identity from the public graph theorem profile. -/
def oneThreeIdentity :=
  Hypostructure.Graph.OneThreeRepair.Component.identity

/-- Reusable contraction decrease theorem for packed finite graphs. -/
def contractionVertexCount_lt :=
  Hypostructure.Graph.vertexCount_lt

/-- Reusable minimum-degree deletion criticality profile. -/
def minimumDegreeDeletionCriticalityProfile :=
  Hypostructure.Graph.minimumDegreeDeletionCriticalityProfile

end Hypostructure.Graph.Theorems
