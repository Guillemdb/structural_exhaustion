import StructuralExhaustion.CT3.Types
import StructuralExhaustion.CT4.Types
import StructuralExhaustion.CT7.Interface
import StructuralExhaustion.CT15.Interface
import StructuralExhaustion.CT16.Interface

namespace StructuralExhaustion.CT15

/-! Proof-carrying vocabulary for CT15 target-relative rank forcing. -/

structure Framework where
  entry : Interface.Framework
  ct3 : CT3.Framework
  ct4 : CT4.Framework
  ct7 : CT7.Interface.Framework
  ct16 : CT16.Interface.Framework
  TargetRelative : Interface.Input entry → Prop
  StructuralDependence : Interface.Input entry → Prop
  IndependentCoordinates : Interface.Input entry → Prop
  LedgerCertified : Interface.Input entry → Prop
  DemandExceedsCapacity : Interface.Input entry → Prop
  CT3Aligned : Interface.Input entry → CT3.Input ct3 → Prop
  CT4Aligned : Interface.Input entry → CT4.Input ct4 → Prop
  CT7Aligned : Interface.Input entry → CT7.Interface.Input ct7 → Prop
  CT16Aligned : Interface.Input entry → CT16.Interface.Input ct16 → Prop

abbrev Input (F : Framework) := Interface.Input F.entry
def ScopeReadyAt (F : Framework) (input : Input F) : Prop := Interface.ScopeReadyAt F.entry input
structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unavailable : ¬ ScopeReadyAt F input
structure ScopedState (F : Framework) (input : Input F) : Prop where ready : ScopeReadyAt F input
structure RankState (F : Framework) (input : Input F) : Prop where
  scope : ScopedState F input
  targetRelative : F.TargetRelative input
structure DependenceState (F : Framework) (input : Input F)
    (_rank : RankState F input) : Prop where structural : F.StructuralDependence input
structure FullRankState (F : Framework) (input : Input F)
    (_rank : RankState F input) : Prop where independent : F.IndependentCoordinates input
structure LedgerState (F : Framework) (input : Input F)
    {rank : RankState F input} (_full : FullRankState F input rank) : Prop where
  certified : F.LedgerCertified input
structure C4Certificate (F : Framework) (input : Input F)
    {rank : RankState F input} {full : FullRankState F input rank}
    (_ledger : LedgerState F input full) : Prop where
  exceeds : F.DemandExceedsCapacity input
  closes : F.entry.C4Claim input.G input.branch
structure CT3Payload (F : Framework) (input : Input F)
    {rank : RankState F input} (_dependence : DependenceState F input rank) where
  downstream : CT3.Input F.ct3
  aligned : F.CT3Aligned input downstream
structure CT7Payload (F : Framework) (input : Input F)
    {rank : RankState F input} (_dependence : DependenceState F input rank) where
  downstream : CT7.Interface.Input F.ct7
  aligned : F.CT7Aligned input downstream
structure CT16Payload (F : Framework) (input : Input F)
    {rank : RankState F input} (_dependence : DependenceState F input rank) where
  downstream : CT16.Interface.Input F.ct16
  aligned : F.CT16Aligned input downstream
structure CT4Payload (F : Framework) (input : Input F)
    {rank : RankState F input} {full : FullRankState F input rank}
    (_ledger : LedgerState F input full) where
  downstream : CT4.Input F.ct4
  aligned : F.CT4Aligned input downstream
namespace CT3Payload
def toInput {F : Framework} {input : Input F} {rank : RankState F input}
    {dependence : DependenceState F input rank} (p : CT3Payload F input dependence) :
    CT3.Input F.ct3 := p.downstream
end CT3Payload
namespace CT7Payload
def toInput {F : Framework} {input : Input F} {rank : RankState F input}
    {dependence : DependenceState F input rank} (p : CT7Payload F input dependence) :
    CT7.Interface.Input F.ct7 := p.downstream
end CT7Payload
namespace CT16Payload
def toInput {F : Framework} {input : Input F} {rank : RankState F input}
    {dependence : DependenceState F input rank} (p : CT16Payload F input dependence) :
    CT16.Interface.Input F.ct16 := p.downstream
end CT16Payload
namespace CT4Payload
def toInput {F : Framework} {input : Input F} {rank : RankState F input}
    {full : FullRankState F input rank} {ledger : LedgerState F input full}
    (p : CT4Payload F input ledger) : CT4.Input F.ct4 := p.downstream
end CT4Payload
inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct3 {rank : RankState F input} {dependence : DependenceState F input rank}
      (payload : CT3Payload F input dependence)
  | ct7 {rank : RankState F input} {dependence : DependenceState F input rank}
      (payload : CT7Payload F input dependence)
  | ct16 {rank : RankState F input} {dependence : DependenceState F input rank}
      (payload : CT16Payload F input dependence)
  | ct4 {rank : RankState F input} {full : FullRankState F input rank}
      {ledger : LedgerState F input full} (payload : CT4Payload F input ledger)
structure Port (F : Framework) (input : Input F) where accepts : HandoffPayload F input → Prop
structure HandoffPlan (F : Framework) (input : Input F) (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT15
