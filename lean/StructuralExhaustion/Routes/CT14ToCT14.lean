import StructuralExhaustion.CT14.Automation

namespace StructuralExhaustion.Routes.CT14ToCT14

open StructuralExhaustion

universe uSourceMember uSourceLabel uTargetMember uTargetLabel
universe uAmbient uBranch uLedger

/-- Stable identity of this executable transition profile. -/
def transitionId : String := "CT14.residual.capacity->CT14"

/-!
# CT14 capacity-ledger refinement

One aggregate ledger can be refined by another independently declared CT14
capability on the identical branch. The framework retains the entire source
ledger and owns the target's empty trigger and execution.
-/

/-- The sole public CT14→CT14 transition. -/
def transition
    {P : Core.Problem.{uAmbient, uBranch}}
    {sourceCapability : CT14.Capability.{uSourceMember, uSourceLabel} P}
    {ctx : Core.BranchContext P}
    (targetCapability : CT14.Capability.{uTargetMember, uTargetLabel} P) :
    Core.Routing.CTTransition .ct14 .ct14
      (CT14.CapacityResidual sourceCapability ctx)
      targetCapability.executableInterface :=
  Core.Routing.CTTransition.ofTotalResidual
    transitionId (fun _source => ctx)
    (fun _source => ⟨⟩)

/-- Execute the target CT14 refinement while retaining the complete incoming
CT14 ledger. -/
def advance
    {P : Core.Problem.{uAmbient, uBranch}}
    {sourceCapability : CT14.Capability.{uSourceMember, uSourceLabel} P}
    {ctx : Core.BranchContext P}
    (targetCapability : CT14.Capability.{uTargetMember, uTargetLabel} P)
    {Ledger : Sort uLedger}
    (current : Ledger → CT14.CapacityResidual sourceCapability ctx)
    (source : Core.Routing.ResidualStage .ct14 Ledger) :
    Core.Routing.ResidualStage .ct14
      (((transition targetCapability).onLedger current).EnabledStage source) :=
  (transition targetCapability).runEnabledLedgerOnLedger current source () rfl

@[simp] theorem transition_profile_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {sourceCapability : CT14.Capability.{uSourceMember, uSourceLabel} P}
    {ctx : Core.BranchContext P}
    (targetCapability : CT14.Capability.{uTargetMember, uTargetLabel} P) :
    (transition (sourceCapability := sourceCapability) (ctx := ctx)
      targetCapability).profileId =
      "CT14.residual.capacity->CT14" :=
  rfl

/-- Machine-readable executable profile for the CT14→CT14 family. -/
def transitionContract : Core.CTTransitionProfileContract where
  profileId := transitionId
  sourceTacticId := "CT14"
  targetTacticId := "CT14"
  sourceResidualKind := "CT14.residual.capacity"
  targetExecutableInterface :=
    "StructuralExhaustion.CT14.Capability.executableInterface"
  transitionConstructor :=
    "StructuralExhaustion.Routes.CT14ToCT14.transition"
  advanceExecutor := "StructuralExhaustion.Routes.CT14ToCT14.advance"
  selectionClass := .forced
  semanticDiscovery := .capabilityDiscovery
  problemSpecificInputs := [.targetCapability]

end StructuralExhaustion.Routes.CT14ToCT14
