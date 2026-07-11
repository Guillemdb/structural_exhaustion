import StructuralExhaustion.CT3.Types
import StructuralExhaustion.CT7.Interface
import StructuralExhaustion.CT10.Interface
import StructuralExhaustion.CT12.Interface
import StructuralExhaustion.CT16.Interface

namespace StructuralExhaustion.CT7

/-! Proof-carrying vocabulary for the CT7 exchange trichotomy. -/

structure Framework where
  entry : Interface.Framework
  ct3 : CT3.Framework
  ct10 : CT10.Interface.Framework
  ct12 : CT12.Interface.Framework
  ct16 : CT16.Interface.Framework

  ContextComplete : Interface.Input entry → Prop
  NoRealization : Interface.Input entry → Prop
  Distinguishing : Interface.Input entry → Prop
  NeutralResponses : Interface.Input entry → Prop

  CT3Aligned : Interface.Input entry → CT3.Input ct3 → Prop
  CT10Aligned :
    Interface.Input entry → CT10.Interface.Input ct10 → Prop
  CT12Aligned : Interface.Input entry → CT12.Interface.Input ct12 → Prop
  CT16Aligned : Interface.Input entry → CT16.Interface.Input ct16 → Prop

abbrev Input (F : Framework) := Interface.Input F.entry

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  Interface.ScopeReadyAt F.entry input

structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unavailable : ¬ ScopeReadyAt F input

structure ScopedState (F : Framework) (input : Input F) : Prop where
  ready : ScopeReadyAt F input

structure ContextCertificate (F : Framework) (input : Input F) : Prop where
  complete : F.ContextComplete input

structure ContextState (F : Framework) (input : Input F) : Prop where
  scope : ScopedState F input
  certificate : ContextCertificate F input

structure C1Certificate (F : Framework) (input : Input F)
    (_context : ContextState F input) : Prop where
  closes : F.entry.C1Claim input.G input.branch

structure UnrealizedState (F : Framework) (input : Input F)
    (_context : ContextState F input) : Prop where
  none : F.NoRealization input

structure DefectState (F : Framework) (input : Input F)
    {context : ContextState F input}
    (_unrealized : UnrealizedState F input context) : Prop where
  separates : F.Distinguishing input

structure NeutralState (F : Framework) (input : Input F)
    {context : ContextState F input}
    (_unrealized : UnrealizedState F input context) : Prop where
  equivalent : F.NeutralResponses input

structure C3Certificate (F : Framework) (input : Input F)
    {context : ContextState F input}
    {unrealized : UnrealizedState F input context}
    (_defect : DefectState F input unrealized) : Prop where
  closes : F.entry.C3Claim input.G input.branch

structure CT3Payload (F : Framework) (input : Input F)
    {context : ContextState F input}
    {unrealized : UnrealizedState F input context}
    (_defect : DefectState F input unrealized) where
  downstream : CT3.Input F.ct3
  aligned : F.CT3Aligned input downstream

structure CT12Payload (F : Framework) (input : Input F)
    {context : ContextState F input}
    {unrealized : UnrealizedState F input context}
    (_defect : DefectState F input unrealized) where
  downstream : CT12.Interface.Input F.ct12
  aligned : F.CT12Aligned input downstream

structure C2Certificate (F : Framework) (input : Input F)
    {context : ContextState F input}
    {unrealized : UnrealizedState F input context}
    (_neutral : NeutralState F input unrealized) : Prop where
  closes : F.entry.C2Claim input.G input.branch

structure CT10Payload (F : Framework) (input : Input F)
    {context : ContextState F input}
    {unrealized : UnrealizedState F input context}
    (_neutral : NeutralState F input unrealized) where
  downstream : CT10.Interface.Input F.ct10
  aligned : F.CT10Aligned input downstream

structure CT16Payload (F : Framework) (input : Input F)
    {context : ContextState F input}
    {unrealized : UnrealizedState F input context}
    (_neutral : NeutralState F input unrealized) where
  downstream : CT16.Interface.Input F.ct16
  aligned : F.CT16Aligned input downstream

namespace CT3Payload
def toInput {F : Framework} {input : Input F}
    {context : ContextState F input}
    {unrealized : UnrealizedState F input context}
    {defect : DefectState F input unrealized}
    (payload : CT3Payload F input defect) : CT3.Input F.ct3 := payload.downstream
end CT3Payload

namespace CT10Payload
def toInput {F : Framework} {input : Input F}
    {context : ContextState F input}
    {unrealized : UnrealizedState F input context}
    {neutral : NeutralState F input unrealized}
    (payload : CT10Payload F input neutral) : CT10.Interface.Input F.ct10 :=
  payload.downstream
end CT10Payload

namespace CT12Payload
def toInput {F : Framework} {input : Input F} {context : ContextState F input}
    {unrealized : UnrealizedState F input context} {defect : DefectState F input unrealized}
    (payload : CT12Payload F input defect) : CT12.Interface.Input F.ct12 := payload.downstream
end CT12Payload

namespace CT16Payload
def toInput {F : Framework} {input : Input F} {context : ContextState F input}
    {unrealized : UnrealizedState F input context} {neutral : NeutralState F input unrealized}
    (payload : CT16Payload F input neutral) : CT16.Interface.Input F.ct16 := payload.downstream
end CT16Payload

inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct3 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {defect : DefectState F input unrealized}
      (payload : CT3Payload F input defect)
  | ct12 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {defect : DefectState F input unrealized}
      (payload : CT12Payload F input defect)
  | ct10 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {neutral : NeutralState F input unrealized}
      (payload : CT10Payload F input neutral)
  | ct16 {context : ContextState F input}
      {unrealized : UnrealizedState F input context}
      {neutral : NeutralState F input unrealized}
      (payload : CT16Payload F input neutral)

structure Port (F : Framework) (input : Input F) where
  accepts : HandoffPayload F input → Prop

structure HandoffPlan (F : Framework) (input : Input F)
    (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT7
