import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT8

universe uAmbient uBranch uState uType uResponseContext

structure Capability (P : Core.Problem.{uAmbient, uBranch}) where
  State : Type uState
  ExactType : Type uType
  ResponseContext : Type uResponseContext
  exactTypes : FinEnum ExactType
  responseContexts : FinEnum ResponseContext
  exactType : State → ExactType
  response : State → ResponseContext → Bool

structure Input
    {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uState, uType, uResponseContext} P)
    (ctx : Core.BranchContext P) where
  sequence : List capability.State
  remove : capability.State → capability.State → Core.SmallerObject P ctx.G

def tacticInterface
    {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability.{uAmbient, uBranch, uState, uType, uResponseContext} P) :
    Core.Routing.TacticInterface where
  Context := Core.BranchContext P
  Trigger := Input capability

end StructuralExhaustion.CT8
