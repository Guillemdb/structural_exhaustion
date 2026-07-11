import StructuralExhaustion.CT4.Types
import StructuralExhaustion.CT9.Interface
import StructuralExhaustion.CT13.Interface
import StructuralExhaustion.CT14.Interface

namespace StructuralExhaustion.CT13

/-! Proof-carrying vocabulary for CT13 tiered charging. -/

structure Framework where
  entry : Interface.Framework
  ct4 : CT4.Framework
  ct9 : CT9.Interface.Framework
  ct14 : CT14.Interface.Framework

  TierOneAvailable : Interface.Input entry → Prop
  TierOneCanonical : Interface.Input entry → Prop
  MinimalObstruction : Interface.Input entry → Prop
  TierTwoCanonical : Interface.Input entry → Prop
  ResourcesReconciled : Interface.Input entry → Prop
  CombinedCapacity : Interface.Input entry → Prop

  CT4Aligned : Interface.Input entry → CT4.Input ct4 → Prop
  CT9Aligned : Interface.Input entry → CT9.Interface.Input ct9 → Prop
  CT14Aligned : Interface.Input entry → CT14.Interface.Input ct14 → Prop

abbrev Input (F : Framework) := Interface.Input F.entry
def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  Interface.ScopeReadyAt F.entry input

structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unavailable : ¬ ScopeReadyAt F input
structure ScopedState (F : Framework) (input : Input F) : Prop where
  ready : ScopeReadyAt F input

structure AvailableState (F : Framework) (input : Input F)
    (_scope : ScopedState F input) : Prop where
  available : F.TierOneAvailable input
structure UnavailableState (F : Framework) (input : Input F)
    (_scope : ScopedState F input) : Prop where
  unavailable : ¬ F.TierOneAvailable input

structure TierOneState (F : Framework) (input : Input F)
    {scope : ScopedState F input} (_available : AvailableState F input scope) : Prop where
  canonical : F.TierOneCanonical input

structure FallbackState (F : Framework) (input : Input F)
    {scope : ScopedState F input} (_unavailable : UnavailableState F input scope) : Prop where
  minimal : F.MinimalObstruction input
  canonical : F.TierTwoCanonical input

structure ReconciledState (F : Framework) (input : Input F)
    {scope : ScopedState F input}
    {unavailable : UnavailableState F input scope}
    (_fallback : FallbackState F input unavailable) : Prop where
  reconciled : F.ResourcesReconciled input

structure OverlapState (F : Framework) (input : Input F)
    {scope : ScopedState F input}
    {unavailable : UnavailableState F input scope}
    (_fallback : FallbackState F input unavailable) : Prop where
  unreconciled : ¬ F.ResourcesReconciled input

structure C4Certificate (F : Framework) (input : Input F)
    {scope : ScopedState F input}
    {unavailable : UnavailableState F input scope}
    {fallback : FallbackState F input unavailable}
    (_reconciled : ReconciledState F input fallback) : Prop where
  comparison : F.CombinedCapacity input
  closes : F.entry.C4Claim input.G input.branch

structure CT4Payload (F : Framework) (input : Input F)
    {scope : ScopedState F input} {available : AvailableState F input scope}
    (_tierOne : TierOneState F input available) where
  downstream : CT4.Input F.ct4
  aligned : F.CT4Aligned input downstream

structure CT9Payload (F : Framework) (input : Input F)
    {scope : ScopedState F input}
    {unavailable : UnavailableState F input scope}
    {fallback : FallbackState F input unavailable}
    (_overlap : OverlapState F input fallback) where
  downstream : CT9.Interface.Input F.ct9
  aligned : F.CT9Aligned input downstream

structure CT14Payload (F : Framework) (input : Input F)
    {scope : ScopedState F input}
    {unavailable : UnavailableState F input scope}
    {fallback : FallbackState F input unavailable}
    (_overlap : OverlapState F input fallback) where
  downstream : CT14.Interface.Input F.ct14
  aligned : F.CT14Aligned input downstream

namespace CT4Payload
def toInput {F : Framework} {input : Input F} {scope : ScopedState F input}
    {available : AvailableState F input scope} {tierOne : TierOneState F input available}
    (payload : CT4Payload F input tierOne) : CT4.Input F.ct4 := payload.downstream
end CT4Payload
namespace CT9Payload
def toInput {F : Framework} {input : Input F} {scope : ScopedState F input}
    {unavailable : UnavailableState F input scope}
    {fallback : FallbackState F input unavailable}
    {overlap : OverlapState F input fallback} (payload : CT9Payload F input overlap) :
    CT9.Interface.Input F.ct9 := payload.downstream
end CT9Payload
namespace CT14Payload
def toInput {F : Framework} {input : Input F} {scope : ScopedState F input}
    {unavailable : UnavailableState F input scope}
    {fallback : FallbackState F input unavailable}
    {overlap : OverlapState F input fallback} (payload : CT14Payload F input overlap) :
    CT14.Interface.Input F.ct14 := payload.downstream
end CT14Payload

inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct4 {scope : ScopedState F input} {available : AvailableState F input scope}
      {tierOne : TierOneState F input available} (payload : CT4Payload F input tierOne)
  | ct9 {scope : ScopedState F input} {unavailable : UnavailableState F input scope}
      {fallback : FallbackState F input unavailable} {overlap : OverlapState F input fallback}
      (payload : CT9Payload F input overlap)
  | ct14 {scope : ScopedState F input} {unavailable : UnavailableState F input scope}
      {fallback : FallbackState F input unavailable} {overlap : OverlapState F input fallback}
      (payload : CT14Payload F input overlap)

structure Port (F : Framework) (input : Input F) where
  accepts : HandoffPayload F input → Prop
structure HandoffPlan (F : Framework) (input : Input F) (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT13
