import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT10

universe uAmbient uBranch uDatum uClass uPromotion

structure Capability (P : Core.Problem.{uAmbient, uBranch}) where
  Datum : Type uDatum
  Class : Type uClass
  Promotion : Type uPromotion
  classes : FinEnum Class
  classOf : Datum → Class
  Direct : Class → Prop
  directDecidable : (cls : Class) → Decidable (Direct cls)
  promote : Class → Promotion

structure Input {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uDatum, uClass, uPromotion} P) where
  context : Core.BranchContext P
  data : Core.OrderedCollection capability.Datum

/-- Route-facing CT10 trigger.  Discovery supplies only the finite datum
collection; the inherited branch context remains the router index and cannot
be replaced by a route seed. -/
structure Trigger {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uDatum, uClass, uPromotion} P)
    (_context : Core.BranchContext P) where
  data : Core.OrderedCollection capability.Datum

namespace Input

/-- Materialize the runner input from a typed trigger.  Branch preservation
is definitional because the context is supplied by the route index. -/
def ofTrigger {P : Core.Problem.{uAmbient, uBranch}}
    {capability : Capability.{uAmbient, uBranch, uDatum, uClass, uPromotion} P}
    (context : Core.BranchContext P) (trigger : Trigger capability context) :
    Input capability where
  context := context
  data := trigger.data

end Input

def row {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uDatum, uClass, uPromotion} P)
    (input : Input capability) (cls : capability.Class) : List capability.Datum :=
  letI : DecidableEq capability.Class := capability.classes.decEq
  input.data.values.filter fun datum => capability.classOf datum = cls

def tacticInterface {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uDatum, uClass, uPromotion} P) :
    Core.Routing.TacticInterface where
  Context := Core.BranchContext P
  Trigger := Trigger capability

end StructuralExhaustion.CT10
