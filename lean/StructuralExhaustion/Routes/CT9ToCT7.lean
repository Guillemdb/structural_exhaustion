import StructuralExhaustion.CT7.Automation
import StructuralExhaustion.CT9.Search

namespace StructuralExhaustion.Routes.CT9ToCT7

universe uItem uLabel uObject uLedger

/-- Stable identity of this executable transition profile. -/
def transitionId : String := "CT9.residual.overload->CT7"

/-!
# CT9 overload to CT7 response-comparison transition

An overloaded capacity-one CT9 fibre contains two distinct same-label items.
The application supplies only their mathematical interpretation as CT7
objects; the framework extracts the pair, retains the complete CT9 ledger,
constructs the CT7 trigger, and executes CT7.
-/

/-- Problem-specific item-to-object interpretation. -/
structure ObjectAdapter (Item : Type uItem) (Object : Type uObject) where
  object : Item → Object

/-- The exact same-label pair certified by the CT9 overload. -/
def sourcePair
    {P : Core.Problem}
    {sourceCapability : CT9.Capability.{_, _, uItem, uLabel} P}
    {sourceInput : CT9.Input sourceCapability}
    (source : CT9.OverloadResidual sourceCapability sourceInput)
    (capacityOne : sourceCapability.capacity source.label = 1) :
    CT9.SameLabelPair sourceCapability sourceInput source.label :=
  source.sameLabelPairOfCapacityOne capacityOne

/-- The sole public CT9→CT7 transition. -/
def transition
    {P : Core.Problem}
    {sourceCapability : CT9.Capability.{_, _, uItem, uLabel} P}
    {sourceInput : CT9.Input sourceCapability}
    {targetSpec : CT7.Spec P}
    (targetCapability : CT7.Capability targetSpec)
    (adapter : ObjectAdapter sourceCapability.Item targetSpec.Object)
    (capacityOne : ∀ label, sourceCapability.capacity label = 1) :
    Core.Routing.CTTransition .ct9 .ct7
      (CT9.OverloadResidual sourceCapability sourceInput)
      targetCapability.executableInterface :=
  Core.Routing.CTTransition.ofTotalResidual
    transitionId (fun _source => sourceInput.context)
    (fun source =>
      let pair := sourcePair source (capacityOne source.label)
      ⟨adapter.object pair.first, adapter.object pair.second⟩)

/-- Execute CT7 while retaining the complete incoming CT9 ledger. -/
def advance
    {P : Core.Problem}
    {sourceCapability : CT9.Capability.{_, _, uItem, uLabel} P}
    {sourceInput : CT9.Input sourceCapability}
    {targetSpec : CT7.Spec P}
    (targetCapability : CT7.Capability targetSpec)
    (adapter : ObjectAdapter sourceCapability.Item targetSpec.Object)
    (capacityOne : ∀ label, sourceCapability.capacity label = 1)
    {Ledger : Sort uLedger}
    (current : Ledger → CT9.OverloadResidual sourceCapability sourceInput)
    (source : Core.Routing.ResidualStage .ct9 Ledger) :
    Core.Routing.ResidualStage .ct7
      (((transition targetCapability adapter capacityOne).onLedger current
        ).EnabledStage source) :=
  (transition targetCapability adapter capacityOne).runEnabledLedgerOnLedger
    current source () rfl

@[simp] theorem transition_profile_id
    {P : Core.Problem}
    {sourceCapability : CT9.Capability.{_, _, uItem, uLabel} P}
    {sourceInput : CT9.Input sourceCapability}
    {targetSpec : CT7.Spec P}
    (targetCapability : CT7.Capability targetSpec)
    (adapter : ObjectAdapter sourceCapability.Item targetSpec.Object)
    (capacityOne : ∀ label, sourceCapability.capacity label = 1) :
    (transition (sourceCapability := sourceCapability)
      (sourceInput := sourceInput) targetCapability adapter
        capacityOne).profileId = "CT9.residual.overload->CT7" :=
  rfl

theorem source_pair_distinct
    {P : Core.Problem}
    {sourceCapability : CT9.Capability.{_, _, uItem, uLabel} P}
    {sourceInput : CT9.Input sourceCapability}
    (source : CT9.OverloadResidual sourceCapability sourceInput)
    (capacityOne : sourceCapability.capacity source.label = 1) :
    (sourcePair source capacityOne).first ≠
      (sourcePair source capacityOne).second :=
  (sourcePair source capacityOne).distinct

/-- Machine-readable executable profile for the CT9→CT7 family. -/
def transitionContract : Core.CTTransitionProfileContract where
  profileId := transitionId
  sourceTacticId := "CT9"
  targetTacticId := "CT7"
  sourceResidualKind := "CT9.residual.overload"
  targetExecutableInterface :=
    "StructuralExhaustion.CT7.Capability.executableInterface"
  transitionConstructor :=
    "StructuralExhaustion.Routes.CT9ToCT7.transition"
  advanceExecutor := "StructuralExhaustion.Routes.CT9ToCT7.advance"
  selectionClass := .forced
  semanticDiscovery := .problemSemanticAdapter
    "StructuralExhaustion.Routes.CT9ToCT7.ObjectAdapter"
  problemSpecificInputs := [.targetCapability, .semanticDiscoveryAdapter]

end StructuralExhaustion.Routes.CT9ToCT7
