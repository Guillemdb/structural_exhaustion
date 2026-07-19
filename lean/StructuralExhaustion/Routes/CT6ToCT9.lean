import StructuralExhaustion.CT6.State
import StructuralExhaustion.CT9.Automation

namespace StructuralExhaustion.Routes.CT6ToCT9

universe uResidual uItem
universe uAmbient uBranch uIndex uData uLabel uLedger

/-- Stable identity of this executable transition profile. -/
def transitionId : String := "CT6.residual.activeLedger->CT9"

/-!
# CT6 active-ledger to CT9 overload transition

The problem layer supplies only the mathematical interpretation of the exact
CT6 residual as CT9's declared finite item collection. The framework retains
the complete source ledger, constructs the indexed trigger, and executes CT9.
-/

/-- Problem-specific interpretation of a CT6 residual as CT9's finite local
item collection. Duplicate-freedom and order are carried by the collection. -/
structure ItemCollectionAdapter (Residual : Type uResidual)
    (Item : Type uItem) where
  items : Residual → Core.OrderedCollection Item

namespace ItemCollectionAdapter

/-- Canonical adapter when the target collection is already fixed by the
inherited branch state. -/
def constant {Residual : Type uResidual} {Item : Type uItem}
    (items : Core.OrderedCollection Item) :
    ItemCollectionAdapter Residual Item where
  items := fun _source => items

@[simp] theorem constant_items
    {Residual : Type uResidual} {Item : Type uItem}
    (items : Core.OrderedCollection Item) (source : Residual) :
    (constant (Residual := Residual) items).items source = items :=
  rfl

end ItemCollectionAdapter

/-- The sole public CT6→CT9 transition. -/
def transition
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (targetCapability : CT9.Capability.{uAmbient, uBranch, uItem, uLabel} P)
    (adapter : ItemCollectionAdapter
      (CT6.ActiveLedgerResidual S sourceCapability input)
      targetCapability.Item) :
    Core.Routing.CTTransition .ct6 .ct9
      (CT6.ActiveLedgerResidual S sourceCapability input)
      targetCapability.executableInterface :=
  Core.Routing.CTTransition.ofTotalResidual
    transitionId (fun _source => input)
    (fun source => ⟨adapter.items source⟩)

/-- Execute CT9 while retaining the complete incoming CT6 ledger. -/
def advance
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (targetCapability : CT9.Capability.{uAmbient, uBranch, uItem, uLabel} P)
    (adapter : ItemCollectionAdapter
      (CT6.ActiveLedgerResidual S sourceCapability input)
      targetCapability.Item)
    {Ledger : Sort uLedger}
    (current : Ledger → CT6.ActiveLedgerResidual S sourceCapability input)
    (source : Core.Routing.ResidualStage .ct6 Ledger) :
    ((transition targetCapability adapter).onLedger current).EnabledStage source :=
  (transition targetCapability adapter).runEnabledOnLedger
    current source () rfl

@[simp] theorem transition_profile_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (targetCapability : CT9.Capability.{uAmbient, uBranch, uItem, uLabel} P)
    (adapter : ItemCollectionAdapter
      (CT6.ActiveLedgerResidual S sourceCapability input)
      targetCapability.Item) :
    (transition (S := S) (sourceCapability := sourceCapability)
      (input := input) targetCapability adapter).profileId =
      "CT6.residual.activeLedger->CT9" :=
  rfl

/-- Machine-readable executable profile for the CT6→CT9 family. -/
def transitionContract : Core.CTTransitionProfileContract where
  profileId := transitionId
  sourceTacticId := "CT6"
  targetTacticId := "CT9"
  sourceResidualKind := "CT6.residual.activeLedger"
  targetExecutableInterface :=
    "StructuralExhaustion.CT9.Capability.executableInterface"
  transitionConstructor :=
    "StructuralExhaustion.Routes.CT6ToCT9.transition"
  advanceExecutor := "StructuralExhaustion.Routes.CT6ToCT9.advance"
  selectionClass := .forced
  semanticDiscovery := .problemSemanticAdapter
    "StructuralExhaustion.Routes.CT6ToCT9.ItemCollectionAdapter"
  problemSpecificInputs := [.targetCapability, .semanticDiscoveryAdapter]

end StructuralExhaustion.Routes.CT6ToCT9
