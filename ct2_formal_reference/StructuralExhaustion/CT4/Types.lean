import StructuralExhaustion.CT9.Interface
import StructuralExhaustion.CT13.Interface
import StructuralExhaustion.CT14.Interface

namespace StructuralExhaustion.CT4

universe uA uB uD uP uC uL u9 u14 u13

/-! Proof-carrying vocabulary for CT4's deterministic charging machine. -/

structure Framework where
  Ambient : Type uA
  BranchState : Ambient → Type uB
  Demand : (G : Ambient) → BranchState G → Type uD
  Payer : (G : Ambient) → BranchState G → Type uP
  CapacityData : (G : Ambient) → BranchState G → Type uC
  LowerBoundData : (G : Ambient) → BranchState G → Type uL

  ScopeReady : (G : Ambient) → BranchState G → Prop
  Eligible :
    {G : Ambient} → {branch : BranchState G} →
    Demand G branch → Payer G branch → Prop
  CanonicalAssignment :
    {G : Ambient} → {branch : BranchState G} →
    (Demand G branch → Option (Payer G branch)) → Prop
  FibreBounded :
    {G : Ambient} → {branch : BranchState G} →
    (Demand G branch → Option (Payer G branch)) →
    CapacityData G branch → Prop
  DemandExceedsCapacity :
    {G : Ambient} → {branch : BranchState G} →
    (Demand G branch → Option (Payer G branch)) →
    CapacityData G branch → LowerBoundData G branch → Prop

  C4Claim : (G : Ambient) → BranchState G → Prop
  ct9 : CT9.Interface.Framework.{u9, u9, u9, u9, u9, u9}
  ct14 : CT14.Interface.Framework.{u14, u14, u14, u14, u14, u14}
  ct13 : CT13.Interface.Framework.{u13, u13, u13, u13, u13}
  CT9Aligned :
    (G : Ambient) → BranchState G → CT9.Interface.Input ct9 → Prop
  CT14Aligned :
    (G : Ambient) → BranchState G → CT14.Interface.Input ct14 → Prop
  CT13Aligned :
    (G : Ambient) → BranchState G → CT13.Interface.Input ct13 → Prop

/-- A ledger is entry data.  Determinism, totality, bounded fibres, and the
capacity comparison are certified by distinct nodes. -/
structure Input (F : Framework) where
  G : F.Ambient
  branch : F.BranchState G
  assign : F.Demand G branch → Option (F.Payer G branch)
  capacity : F.CapacityData G branch
  lowerBound : F.LowerBoundData G branch

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  F.ScopeReady input.G input.branch

structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unavailable : ¬ ScopeReadyAt F input

structure ScopedState (F : Framework) (input : Input F) : Prop where
  ready : ScopeReadyAt F input

structure AssignmentCertificate (F : Framework) (input : Input F) : Prop where
  canonical : F.CanonicalAssignment input.assign

structure AssignmentState (F : Framework) (input : Input F) : Prop where
  scope : ScopedState F input
  certificate : AssignmentCertificate F input

/-- Constructive evidence for the recovery route to CT13. -/
structure MissingPayerWitness (F : Framework) (input : Input F) where
  demand : F.Demand input.G input.branch
  unassigned : input.assign demand = none
  unavailable :
    ∀ payer : F.Payer input.G input.branch,
      ¬ F.Eligible demand payer

structure CT13Payload (F : Framework) (input : Input F)
    (_assignment : AssignmentState F input) where
  witness : MissingPayerWitness F input
  downstream : CT13.Interface.Input F.ct13
  aligned : F.CT13Aligned input.G input.branch downstream

namespace CT13Payload
def toInput {F : Framework} {input : Input F}
    {assignment : AssignmentState F input} (payload : CT13Payload F input assignment) :
    CT13.Interface.Input F.ct13 := payload.downstream
end CT13Payload

structure TotalAssignmentState (F : Framework) (input : Input F)
    (_assignment : AssignmentState F input) : Prop where
  total :
    ∀ demand : F.Demand input.G input.branch,
      ∃ payer : F.Payer input.G input.branch,
        input.assign demand = some payer ∧ F.Eligible demand payer

structure CT9Payload (F : Framework) (input : Input F)
    {assignment : AssignmentState F input}
    (_total : TotalAssignmentState F input assignment) where
  downstream : CT9.Interface.Input F.ct9
  aligned : F.CT9Aligned input.G input.branch downstream

namespace CT9Payload
def toInput {F : Framework} {input : Input F}
    {assignment : AssignmentState F input}
    {total : TotalAssignmentState F input assignment}
    (payload : CT9Payload F input total) : CT9.Interface.Input F.ct9 :=
  payload.downstream
end CT9Payload

structure BoundedFibreState (F : Framework) (input : Input F)
    {assignment : AssignmentState F input}
    (_total : TotalAssignmentState F input assignment) : Prop where
  bounded : F.FibreBounded input.assign input.capacity

structure C4Certificate (F : Framework) (input : Input F)
    {assignment : AssignmentState F input}
    {total : TotalAssignmentState F input assignment}
    (_bounded : BoundedFibreState F input total) : Prop where
  exceeds :
    F.DemandExceedsCapacity input.assign input.capacity input.lowerBound
  closes : F.C4Claim input.G input.branch

structure CT14Payload (F : Framework) (input : Input F)
    {assignment : AssignmentState F input}
    {total : TotalAssignmentState F input assignment}
    (_bounded : BoundedFibreState F input total) where
  downstream : CT14.Interface.Input F.ct14
  aligned : F.CT14Aligned input.G input.branch downstream

namespace CT14Payload
def toInput {F : Framework} {input : Input F}
    {assignment : AssignmentState F input}
    {total : TotalAssignmentState F input assignment}
    {bounded : BoundedFibreState F input total}
    (payload : CT14Payload F input bounded) : CT14.Interface.Input F.ct14 :=
  payload.downstream
end CT14Payload

inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct13 {assignment : AssignmentState F input}
      (payload : CT13Payload F input assignment)
  | ct9 {assignment : AssignmentState F input}
      {total : TotalAssignmentState F input assignment}
      (payload : CT9Payload F input total)
  | ct14 {assignment : AssignmentState F input}
      {total : TotalAssignmentState F input assignment}
      {bounded : BoundedFibreState F input total}
      (payload : CT14Payload F input bounded)

structure Port (F : Framework) (input : Input F) where
  accepts : HandoffPayload F input → Prop

structure HandoffPlan (F : Framework) (input : Input F)
    (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT4
