import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT9

universe uAmbient uBranch uItem uLabel

/-- Mathematical data for exact label fibres and capacity comparison. -/
structure Capability (P : Core.Problem.{uAmbient, uBranch}) where
  Item : Type uItem
  Label : Type uLabel
  labels : FinEnum Label
  label : Item → Label
  capacity : Label → Nat

/-- Runtime CT9 data: one branch and its exact active item collection. -/
structure Input {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uItem, uLabel} P) where
  context : Core.BranchContext P
  items : Core.OrderedCollection capability.Item

/-- Transition-facing CT9 trigger.  The inherited branch is an index; discovery
supplies only the active finite collection. -/
structure Trigger {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uItem, uLabel} P)
    (_context : Core.BranchContext P) where
  items : Core.OrderedCollection capability.Item

namespace Input

/-- Materialize the runner input while preserving the route's branch context
definitionally. -/
def ofTrigger {P : Core.Problem.{uAmbient, uBranch}}
    {capability : Capability.{uAmbient, uBranch, uItem, uLabel} P}
    (context : Core.BranchContext P) (trigger : Trigger capability context) :
    Input capability where
  context := context
  items := trigger.items

end Input

/-- Exact fibre of one label, computed from the active collection. -/
def fibre {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uItem, uLabel} P)
    (input : Input capability) (label : capability.Label) : List capability.Item :=
  letI : DecidableEq capability.Label := capability.labels.decEq
  input.items.values.filter fun item => capability.label item = label

def fibreCount {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uItem, uLabel} P)
    (input : Input capability) (label : capability.Label) : Nat :=
  (fibre capability input label).length

/-- Total number of item slots permitted across the exact label universe. -/
def totalCapacity {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uItem, uLabel} P) : Nat :=
  (capability.labels.orderedValues.map capability.capacity).sum

end StructuralExhaustion.CT9
