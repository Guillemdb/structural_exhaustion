import StructuralExhaustion.CT1.Types
import StructuralExhaustion.CT7.Interface
import StructuralExhaustion.CT10.Interface
import StructuralExhaustion.CT11.Interface
import StructuralExhaustion.CT14.Interface

namespace StructuralExhaustion.CT11

/-! Proof-carrying vocabulary for CT11 localization. -/

structure Framework where
  entry : Interface.Framework
  ct1 : CT1.Framework
  ct7 : CT7.Interface.Framework
  ct10 : CT10.Interface.Framework
  ct14 : CT14.Interface.Framework

  DecompositionCertified : Interface.Input entry → Prop
  AdmissibilityClosed : Interface.Input entry → Prop
  SummationCertified : Interface.Input entry → Prop
  LocalDeficitExists : Interface.Input entry → Prop

  CT1Aligned : Interface.Input entry → CT1.Input ct1 → Prop
  CT7Aligned : Interface.Input entry → CT7.Interface.Input ct7 → Prop
  CT10Aligned : Interface.Input entry → CT10.Interface.Input ct10 → Prop
  CT14Aligned : Interface.Input entry → CT14.Interface.Input ct14 → Prop

abbrev Input (F : Framework) := Interface.Input F.entry
def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  Interface.ScopeReadyAt F.entry input

structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unavailable : ¬ ScopeReadyAt F input

structure ScopedState (F : Framework) (input : Input F) : Prop where
  ready : ScopeReadyAt F input

structure DecompositionState (F : Framework) (input : Input F) : Prop where
  scope : ScopedState F input
  certified : F.DecompositionCertified input

structure AdmissibleState (F : Framework) (input : Input F)
    (_decomposition : DecompositionState F input) : Prop where
  closed : F.AdmissibilityClosed input

structure LocalizationState (F : Framework) (input : Input F)
    {decomposition : DecompositionState F input}
    (_admissible : AdmissibleState F input decomposition) : Prop where
  summed : F.SummationCertified input
  localized : F.LocalDeficitExists input

structure CT10Payload (F : Framework) (input : Input F)
    (_decomposition : DecompositionState F input) where
  downstream : CT10.Interface.Input F.ct10
  aligned : F.CT10Aligned input downstream

structure CT1Payload (F : Framework) (input : Input F)
    {decomposition : DecompositionState F input}
    {admissible : AdmissibleState F input decomposition}
    (_localized : LocalizationState F input admissible) where
  downstream : CT1.Input F.ct1
  aligned : F.CT1Aligned input downstream

structure CT7Payload (F : Framework) (input : Input F)
    {decomposition : DecompositionState F input}
    {admissible : AdmissibleState F input decomposition}
    (_localized : LocalizationState F input admissible) where
  downstream : CT7.Interface.Input F.ct7
  aligned : F.CT7Aligned input downstream

structure CT14Payload (F : Framework) (input : Input F)
    {decomposition : DecompositionState F input}
    {admissible : AdmissibleState F input decomposition}
    (_localized : LocalizationState F input admissible) where
  downstream : CT14.Interface.Input F.ct14
  aligned : F.CT14Aligned input downstream

namespace CT10Payload
def toInput {F : Framework} {input : Input F}
    {decomposition : DecompositionState F input}
    (payload : CT10Payload F input decomposition) : CT10.Interface.Input F.ct10 :=
  payload.downstream
end CT10Payload

namespace CT1Payload
def toInput {F : Framework} {input : Input F}
    {decomposition : DecompositionState F input}
    {admissible : AdmissibleState F input decomposition}
    {localized : LocalizationState F input admissible}
    (payload : CT1Payload F input localized) : CT1.Input F.ct1 := payload.downstream
end CT1Payload

namespace CT7Payload
def toInput {F : Framework} {input : Input F}
    {decomposition : DecompositionState F input}
    {admissible : AdmissibleState F input decomposition}
    {localized : LocalizationState F input admissible}
    (payload : CT7Payload F input localized) : CT7.Interface.Input F.ct7 :=
  payload.downstream
end CT7Payload

namespace CT14Payload
def toInput {F : Framework} {input : Input F}
    {decomposition : DecompositionState F input}
    {admissible : AdmissibleState F input decomposition}
    {localized : LocalizationState F input admissible}
    (payload : CT14Payload F input localized) : CT14.Interface.Input F.ct14 :=
  payload.downstream
end CT14Payload

inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct10 {decomposition : DecompositionState F input}
      (payload : CT10Payload F input decomposition)
  | ct1 {decomposition : DecompositionState F input}
      {admissible : AdmissibleState F input decomposition}
      {localized : LocalizationState F input admissible}
      (payload : CT1Payload F input localized)
  | ct7 {decomposition : DecompositionState F input}
      {admissible : AdmissibleState F input decomposition}
      {localized : LocalizationState F input admissible}
      (payload : CT7Payload F input localized)
  | ct14 {decomposition : DecompositionState F input}
      {admissible : AdmissibleState F input decomposition}
      {localized : LocalizationState F input admissible}
      (payload : CT14Payload F input localized)

structure Port (F : Framework) (input : Input F) where
  accepts : HandoffPayload F input → Prop

structure HandoffPlan (F : Framework) (input : Input F) (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT11
