import StructuralExhaustion.CT3.Types
import StructuralExhaustion.CT7.Interface
import StructuralExhaustion.CT8.Interface
import StructuralExhaustion.CT10.Interface

namespace StructuralExhaustion.CT8

/-! Proof-carrying vocabulary for CT8 finite-state pumping. -/

structure Framework where
  entry : Interface.Framework
  ct3 : CT3.Framework
  ct7 : CT7.Interface.Framework
  ct10 : CT10.Interface.Framework

  TypeEqualityCertified : Interface.Input entry → Prop
  CoarseLabel : Interface.Input entry → Prop
  ShortSequence : Interface.Input entry → Prop
  RepeatedType : Interface.Input entry → Prop
  Indistinguishable : Interface.Input entry → Prop
  Separating : Interface.Input entry → Prop

  CT3Aligned : Interface.Input entry → CT3.Input ct3 → Prop
  CT7Aligned : Interface.Input entry → CT7.Interface.Input ct7 → Prop
  CT10Aligned : Interface.Input entry → CT10.Interface.Input ct10 → Prop

abbrev Input (F : Framework) := Interface.Input F.entry
def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  Interface.ScopeReadyAt F.entry input

structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unavailable : ¬ ScopeReadyAt F input

structure ScopedState (F : Framework) (input : Input F) : Prop where
  ready : ScopeReadyAt F input

/-- A finite label design exists, but it is not response-complete. -/
structure CT10Payload (F : Framework) (input : Input F) where
  coarse : F.CoarseLabel input
  downstream : CT10.Interface.Input F.ct10
  aligned : F.CT10Aligned input downstream

structure EqualityCertificate (F : Framework) (input : Input F) : Prop where
  exact : F.TypeEqualityCertified input

structure EqualityState (F : Framework) (input : Input F) : Prop where
  scope : ScopedState F input
  certificate : EqualityCertificate F input

structure C5Certificate (F : Framework) (input : Input F)
    (_equality : EqualityState F input) : Prop where
  short : F.ShortSequence input
  closes : F.entry.C5Claim input.G input.branch

structure RepeatedState (F : Framework) (input : Input F)
    (_equality : EqualityState F input) : Prop where
  repeated : F.RepeatedType input

structure C2Certificate (F : Framework) (input : Input F)
    {equality : EqualityState F input}
    (_repeated : RepeatedState F input equality) : Prop where
  equivalent : F.Indistinguishable input
  closes : F.entry.C2Claim input.G input.branch

structure SeparatingState (F : Framework) (input : Input F)
    {equality : EqualityState F input}
    (_repeated : RepeatedState F input equality) : Prop where
  separates : F.Separating input

structure CT3Payload (F : Framework) (input : Input F)
    {equality : EqualityState F input}
    {repeated : RepeatedState F input equality}
    (_separating : SeparatingState F input repeated) where
  downstream : CT3.Input F.ct3
  aligned : F.CT3Aligned input downstream

structure CT7Payload (F : Framework) (input : Input F)
    {equality : EqualityState F input}
    {repeated : RepeatedState F input equality}
    (_separating : SeparatingState F input repeated) where
  downstream : CT7.Interface.Input F.ct7
  aligned : F.CT7Aligned input downstream

namespace CT10Payload
def toInput {F : Framework} {input : Input F}
    (payload : CT10Payload F input) : CT10.Interface.Input F.ct10 := payload.downstream
end CT10Payload

namespace CT3Payload
def toInput {F : Framework} {input : Input F}
    {equality : EqualityState F input}
    {repeated : RepeatedState F input equality}
    {separating : SeparatingState F input repeated}
    (payload : CT3Payload F input separating) : CT3.Input F.ct3 := payload.downstream
end CT3Payload

namespace CT7Payload
def toInput {F : Framework} {input : Input F}
    {equality : EqualityState F input}
    {repeated : RepeatedState F input equality}
    {separating : SeparatingState F input repeated}
    (payload : CT7Payload F input separating) : CT7.Interface.Input F.ct7 :=
  payload.downstream
end CT7Payload

inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct10 (payload : CT10Payload F input)
  | ct3 {equality : EqualityState F input}
      {repeated : RepeatedState F input equality}
      {separating : SeparatingState F input repeated}
      (payload : CT3Payload F input separating)
  | ct7 {equality : EqualityState F input}
      {repeated : RepeatedState F input equality}
      {separating : SeparatingState F input repeated}
      (payload : CT7Payload F input separating)

structure Port (F : Framework) (input : Input F) where
  accepts : HandoffPayload F input → Prop

structure HandoffPlan (F : Framework) (input : Input F) (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT8
