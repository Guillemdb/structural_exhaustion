import StructuralExhaustion.CT3.Types
import StructuralExhaustion.CT4.Types
import StructuralExhaustion.CT6.Interface
import StructuralExhaustion.CT7.Interface
import StructuralExhaustion.CT9.Interface
import StructuralExhaustion.CT10.Interface

namespace StructuralExhaustion.CT6

/-!
Proof-carrying vocabulary for the CT6 active/dormant machine.

The `entry` field is the stable input API.  Consumer entry frameworks are
also interface-only values, so the tactic-level routing cycle
CT6 → CT7/CT9/CT10 does not become a Lean import cycle.
-/

structure Framework where
  entry : Interface.Framework
  ct3 : CT3.Framework
  ct4 : CT4.Framework
  ct7 : CT7.Interface.Framework
  ct9 : CT9.Interface.Framework
  ct10 : CT10.Interface.Framework

  DefinitionCertified : Interface.Input entry → Prop
  ActiveRegime : Interface.Input entry → Prop
  DormantRegime : Interface.Input entry → Prop
  FirstFailureStructural :
    (input : Interface.Input entry) →
    entry.FailureWitness input.G input.branch → Prop

  CT3Aligned :
    (input : Interface.Input entry) → CT3.Input ct3 → Prop
  CT4Aligned :
    (input : Interface.Input entry) → CT4.Input ct4 → Prop
  CT7Aligned :
    (input : Interface.Input entry) → CT7.Interface.Input ct7 → Prop
  CT9Aligned :
    (input : Interface.Input entry) → CT9.Interface.Input ct9 → Prop
  CT10Aligned :
    (input : Interface.Input entry) → CT10.Interface.Input ct10 → Prop

abbrev Input (F : Framework) := Interface.Input F.entry

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  Interface.ScopeReadyAt F.entry input

structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unavailable : ¬ ScopeReadyAt F input

structure ScopedState (F : Framework) (input : Input F) : Prop where
  ready : ScopeReadyAt F input

structure DefinitionCertificate (F : Framework) (input : Input F) : Prop where
  certified : F.DefinitionCertified input

structure DefinitionState (F : Framework) (input : Input F) : Prop where
  scope : ScopedState F input
  certificate : DefinitionCertificate F input

structure ActiveState (F : Framework) (input : Input F)
    (_definition : DefinitionState F input) : Prop where
  active : F.ActiveRegime input

structure DormantState (F : Framework) (input : Input F)
    (_definition : DefinitionState F input) where
  dormant : F.DormantRegime input
  witness : F.entry.FailureWitness input.G input.branch
  structural : F.FirstFailureStructural input witness

structure CT4Payload (F : Framework) (input : Input F)
    {definition : DefinitionState F input}
    (_active : ActiveState F input definition) where
  downstream : CT4.Input F.ct4
  aligned : F.CT4Aligned input downstream

namespace CT4Payload

def toInput {F : Framework} {input : Input F}
    {definition : DefinitionState F input}
    {active : ActiveState F input definition}
    (payload : CT4Payload F input active) : CT4.Input F.ct4 :=
  payload.downstream

end CT4Payload

structure C1Certificate (F : Framework) (input : Input F)
    {definition : DefinitionState F input}
    (_dormant : DormantState F input definition) : Prop where
  closes : F.entry.C1Claim input.G input.branch

structure CT3Payload (F : Framework) (input : Input F)
    {definition : DefinitionState F input}
    (_dormant : DormantState F input definition) where
  downstream : CT3.Input F.ct3
  aligned : F.CT3Aligned input downstream

structure CT7Payload (F : Framework) (input : Input F)
    {definition : DefinitionState F input}
    (_dormant : DormantState F input definition) where
  downstream : CT7.Interface.Input F.ct7
  aligned : F.CT7Aligned input downstream

structure CT9Payload (F : Framework) (input : Input F)
    {definition : DefinitionState F input}
    (_dormant : DormantState F input definition) where
  downstream : CT9.Interface.Input F.ct9
  aligned : F.CT9Aligned input downstream

structure CT10Payload (F : Framework) (input : Input F)
    {definition : DefinitionState F input}
    (_dormant : DormantState F input definition) where
  downstream : CT10.Interface.Input F.ct10
  aligned : F.CT10Aligned input downstream

namespace CT3Payload
def toInput {F : Framework} {input : Input F}
    {definition : DefinitionState F input}
    {dormant : DormantState F input definition}
    (payload : CT3Payload F input dormant) : CT3.Input F.ct3 := payload.downstream
end CT3Payload

namespace CT7Payload
def toInput {F : Framework} {input : Input F}
    {definition : DefinitionState F input}
    {dormant : DormantState F input definition}
    (payload : CT7Payload F input dormant) : CT7.Interface.Input F.ct7 := payload.downstream
end CT7Payload

namespace CT9Payload
def toInput {F : Framework} {input : Input F}
    {definition : DefinitionState F input}
    {dormant : DormantState F input definition}
    (payload : CT9Payload F input dormant) : CT9.Interface.Input F.ct9 := payload.downstream
end CT9Payload

namespace CT10Payload
def toInput {F : Framework} {input : Input F}
    {definition : DefinitionState F input}
    {dormant : DormantState F input definition}
    (payload : CT10Payload F input dormant) : CT10.Interface.Input F.ct10 := payload.downstream
end CT10Payload

inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct4 {definition : DefinitionState F input}
      {active : ActiveState F input definition}
      (payload : CT4Payload F input active)
  | ct3 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT3Payload F input dormant)
  | ct7 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT7Payload F input dormant)
  | ct9 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT9Payload F input dormant)
  | ct10 {definition : DefinitionState F input}
      {dormant : DormantState F input definition}
      (payload : CT10Payload F input dormant)

structure Port (F : Framework) (input : Input F) where
  accepts : HandoffPayload F input → Prop

structure HandoffPlan (F : Framework) (input : Input F)
    (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT6
