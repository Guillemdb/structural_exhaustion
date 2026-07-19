import StructuralExhaustion.CT5.State
import StructuralExhaustion.CT14.Automation

namespace StructuralExhaustion.Routes.CT5ToCT14

open StructuralExhaustion

universe uSite uWitness uMember uLabel
universe uAmbient uBranch uLedger

/-- Stable identity of this executable transition profile. -/
def transitionId : String := "CT5.residual.chargeLedger->CT14"

/-!
# CT5 charge-ledger to CT14 aggregate-mass transition

A CT5 charge residual has completed its local witness ledger on one branch
context. CT14's member universe is fixed by its target capability and its
trigger carries no additional author datum. The framework therefore owns the
unique context-preserving transition and target execution.
-/

/-- The sole public CT5→CT14 transition. No semantic adapter is needed: the
source residual already fixes the inherited context and CT14 has an empty
trigger. -/
def transition
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT5.Spec.{uSite, uWitness} P}
    {sourceCapability : CT5.Capability S}
    {input : CT5.Input P}
    (targetCapability : CT14.Capability.{uMember, uLabel} P) :
    Core.Routing.CTTransition .ct5 .ct14
      (CT5.ChargeLedgerResidual S sourceCapability input)
      targetCapability.executableInterface :=
  Core.Routing.CTTransition.ofTotalResidual
    transitionId (fun _source => input)
    (fun _source => ⟨⟩)

/-- Execute CT14 while retaining the complete incoming CT5 ledger. The
enabled stage, rather than a reconstructed target input, is the only handoff
that may continue downstream. -/
def advance
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT5.Spec.{uSite, uWitness} P}
    {sourceCapability : CT5.Capability S}
    {input : CT5.Input P}
    (targetCapability : CT14.Capability.{uMember, uLabel} P)
    {Ledger : Sort uLedger}
    (current : Ledger → CT5.ChargeLedgerResidual S sourceCapability input)
    (source : Core.Routing.ResidualStage .ct5 Ledger) :
    ((transition targetCapability).onLedger current).EnabledStage source :=
  (transition targetCapability).runEnabledOnLedger current source () rfl

@[simp] theorem transition_profile_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT5.Spec.{uSite, uWitness} P}
    {sourceCapability : CT5.Capability S}
    {input : CT5.Input P}
    (targetCapability : CT14.Capability.{uMember, uLabel} P) :
    (transition (S := S) (sourceCapability := sourceCapability)
      (input := input) targetCapability).profileId =
      "CT5.residual.chargeLedger->CT14" :=
  rfl

/-- Machine-readable executable profile for the CT5→CT14 family. -/
def transitionContract : Core.CTTransitionProfileContract where
  profileId := transitionId
  sourceTacticId := "CT5"
  targetTacticId := "CT14"
  sourceResidualKind := "CT5.residual.chargeLedger"
  targetExecutableInterface :=
    "StructuralExhaustion.CT14.Capability.executableInterface"
  transitionConstructor :=
    "StructuralExhaustion.Routes.CT5ToCT14.transition"
  advanceExecutor := "StructuralExhaustion.Routes.CT5ToCT14.advance"
  selectionClass := .forced
  semanticDiscovery := .capabilityDiscovery
  problemSpecificInputs := [.targetCapability]

end StructuralExhaustion.Routes.CT5ToCT14
