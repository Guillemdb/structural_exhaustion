import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT11

universe uAmbient uBranch uCell

structure Capability (P : Core.Problem.{uAmbient, uBranch}) where
  Cell : Type uCell
  Admissible : Core.BranchContext P → Cell → Prop
  admissibleDecidable : (ctx : Core.BranchContext P) →
    (cell : Cell) → Decidable (Admissible ctx cell)
  localBudget : Core.BranchContext P → Cell → Int

structure Input {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uCell} P) where
  context : Core.BranchContext P
  cells : Core.OrderedCollection capability.Cell
  deficit : (cells.values.map (capability.localBudget context)).sum < 0

/-- Route-facing CT11 trigger.  Its deficit proof is indexed by the inherited
branch context, so routing cannot silently substitute another branch. -/
structure Trigger {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uCell} P)
    (context : Core.BranchContext P) where
  cells : Core.OrderedCollection capability.Cell
  deficit : (cells.values.map (capability.localBudget context)).sum < 0

namespace Input

def ofTrigger {P : Core.Problem.{uAmbient, uBranch}}
    {capability : Capability.{uAmbient, uBranch, uCell} P}
    (context : Core.BranchContext P) (trigger : Trigger capability context) :
    Input capability where
  context := context
  cells := trigger.cells
  deficit := trigger.deficit

end Input

def tacticInterface {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uCell} P) :
    Core.Routing.TacticInterface where
  Context := Core.BranchContext P
  Trigger := Trigger capability

end StructuralExhaustion.CT11
