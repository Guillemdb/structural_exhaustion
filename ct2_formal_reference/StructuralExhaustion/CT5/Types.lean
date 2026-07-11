import StructuralExhaustion.CT4.Types
import StructuralExhaustion.CT11.Interface
import StructuralExhaustion.CT14.Interface

namespace StructuralExhaustion.CT5

universe uA uB uD uP uC uL u9 u4_14 u13
universe uS uW u11 u5_14

/-! Proof-carrying vocabulary for CT5's local-to-global machine. -/

structure Framework where
  ct4 : CT4.Framework.{uA, uB, uD, uP, uC, uL, u9, u4_14, u13}
  ct11 : CT11.Interface.Framework.{u11, u11, u11, u11, u11, u11}
  ct14 : CT14.Interface.Framework.{u5_14, u5_14, u5_14, u5_14, u5_14, u5_14}
  Site :
    (G : ct4.Ambient) → ct4.BranchState G → Type uS
  LocalWitness :
    (G : ct4.Ambient) → (branch : ct4.BranchState G) →
    Site G branch → Type uW

  ScopeReady :
    (G : ct4.Ambient) → ct4.BranchState G → Prop
  Active :
    {G : ct4.Ambient} → {branch : ct4.BranchState G} →
    Site G branch → Prop
  WitnessSupports :
    {G : ct4.Ambient} → {branch : ct4.BranchState G} →
    (site : Site G branch) → LocalWitness G branch site → Prop
  LocalityHolds :
    {G : ct4.Ambient} → {branch : ct4.BranchState G} →
    ((site : Site G branch) → Option (LocalWitness G branch site)) → Prop
  LocalLedgerReady :
    {G : ct4.Ambient} → {branch : ct4.BranchState G} →
    ((site : Site G branch) → Option (LocalWitness G branch site)) → Prop
  SummationHolds :
    {G : ct4.Ambient} → {branch : ct4.BranchState G} →
    ((site : Site G branch) → Option (LocalWitness G branch site)) → Prop

  CT11Aligned :
    (G : ct4.Ambient) → ct4.BranchState G → CT11.Interface.Input ct11 → Prop
  CT14Aligned :
    (G : ct4.Ambient) → ct4.BranchState G → CT14.Interface.Input ct14 → Prop

structure Input (F : Framework) where
  G : F.ct4.Ambient
  branch : F.ct4.BranchState G
  extract :
    (site : F.Site G branch) → Option (F.LocalWitness G branch site)

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  F.ScopeReady input.G input.branch

structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unavailable : ¬ ScopeReadyAt F input

structure ScopedState (F : Framework) (input : Input F) : Prop where
  ready : ScopeReadyAt F input

/-- The locality lemma is a certification boundary, not a branch of the
runtime machine. -/
structure LocalityCertificate (F : Framework) (input : Input F) : Prop where
  holds : F.LocalityHolds input.extract

structure LocalityState (F : Framework) (input : Input F) : Prop where
  scope : ScopedState F input
  certificate : LocalityCertificate F input

structure CT11Payload (F : Framework) (input : Input F)
    (_locality : LocalityState F input) where
  downstream : CT11.Interface.Input F.ct11
  aligned : F.CT11Aligned input.G input.branch downstream

namespace CT11Payload
def toInput {F : Framework} {input : Input F} {locality : LocalityState F input}
    (payload : CT11Payload F input locality) : CT11.Interface.Input F.ct11 :=
  payload.downstream
end CT11Payload

structure LocalLedgerState (F : Framework) (input : Input F)
    (_locality : LocalityState F input) : Prop where
  ready : F.LocalLedgerReady input.extract

/-- S-Comp certificate for the local-to-global sum. -/
structure SummationState (F : Framework) (input : Input F)
    {locality : LocalityState F input}
    (_ledger : LocalLedgerState F input locality) : Prop where
  summed : F.SummationHolds input.extract

structure C4Certificate (F : Framework) (input : Input F)
    {locality : LocalityState F input}
    {ledger : LocalLedgerState F input locality}
    (_summation : SummationState F input ledger) : Prop where
  closes : F.ct4.C4Claim input.G input.branch

/-- Exact charge-ledger payload.  `toInput` fixes the CT4 ambient object and
branch state definitionally and exposes only the three ledger fields CT4 still
needs to certify. -/
structure CT4Payload (F : Framework) (input : Input F)
    {locality : LocalityState F input}
    {ledger : LocalLedgerState F input locality}
    (_summation : SummationState F input ledger) where
  assign :
    F.ct4.Demand input.G input.branch →
      Option (F.ct4.Payer input.G input.branch)
  capacity : F.ct4.CapacityData input.G input.branch
  lowerBound : F.ct4.LowerBoundData input.G input.branch

namespace CT4Payload

def toInput {F : Framework} {input : Input F}
    {locality : LocalityState F input}
    {ledger : LocalLedgerState F input locality}
    {summation : SummationState F input ledger}
    (payload : CT4Payload F input summation) : CT4.Input F.ct4 where
  G := input.G
  branch := input.branch
  assign := payload.assign
  capacity := payload.capacity
  lowerBound := payload.lowerBound

end CT4Payload

structure CT14Payload (F : Framework) (input : Input F)
    {locality : LocalityState F input}
    {ledger : LocalLedgerState F input locality}
    (_summation : SummationState F input ledger) where
  downstream : CT14.Interface.Input F.ct14
  aligned : F.CT14Aligned input.G input.branch downstream

namespace CT14Payload
def toInput {F : Framework} {input : Input F}
    {locality : LocalityState F input} {ledger : LocalLedgerState F input locality}
    {summation : SummationState F input ledger}
    (payload : CT14Payload F input summation) : CT14.Interface.Input F.ct14 :=
  payload.downstream
end CT14Payload

inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct11 {locality : LocalityState F input}
      (payload : CT11Payload F input locality)
  | ct4 {locality : LocalityState F input}
      {ledger : LocalLedgerState F input locality}
      {summation : SummationState F input ledger}
      (payload : CT4Payload F input summation)
  | ct14 {locality : LocalityState F input}
      {ledger : LocalLedgerState F input locality}
      {summation : SummationState F input ledger}
      (payload : CT14Payload F input summation)

structure Port (F : Framework) (input : Input F) where
  accepts : HandoffPayload F input → Prop

structure HandoffPlan (F : Framework) (input : Input F)
    (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT5
