import Hypostructure.Routes.Accumulated

/-!
# Route registry fixture

This fixture pins every stable catalog identity and exercises the single
generic accumulated executor on a genuinely accumulated predecessor ledger.
-/

namespace Hypostructure.Fixtures.RouteRegistry

open Hypostructure.Core
open Hypostructure.Routes

/-! ## Exact catalog audit -/

def expectedCTKeys : List String := [
  "CT1", "CT2", "CT3", "CT4", "CT5", "CT6", "CT7", "CT8", "CT9",
  "CT10", "CT11", "CT12", "CT13", "CT14", "CT15", "CT16", "CT17"
]

def expectedProfileIds : List String := [
  "CT1.residual.avoiding->CT2",
  "CT1.residual.avoiding->CT2.localDeletion",
  "CT1.terminal.c1->CT12",
  "CT2.residual.separatingContext->CT3",
  "CT2.residual.criticality->CT10",
  "CT5.residual.chargeLedger->CT14",
  "CT6.residual.activeLedger->CT9",
  "CT9.residual.overload->CT7",
  "CT14.residual.capacity->CT14",
  "CT1.residual.accumulatedLedger->CT9",
  "CT1.residual.accumulatedLedger->CT10",
  "CT2.residual.accumulatedLedger->CT1",
  "CT3.residual.accumulatedLedger->CT1",
  "CT5.residual.accumulatedLedger->CT2",
  "CT7.residual.accumulatedLedger->CT5",
  "CT5.residual.accumulatedLedger->CT10",
  "CT9.residual.accumulatedLedger->CT1",
  "CT9.residual.accumulatedLedger->CT5",
  "CT9.residual.accumulatedLedger->CT10",
  "CT9.residual.accumulatedLedger->CT14",
  "CT10.residual.accumulatedLedger->CT5",
  "CT10.residual.accumulatedLedger->CT6",
  "CT10.residual.accumulatedLedger->CT9",
  "CT10.residual.accumulatedLedger->CT14",
  "CT12.residual.accumulatedLedger->CT10",
  "CT12.residual.accumulatedLedger->CT15",
  "CT14.residual.accumulatedLedger->CT1",
  "CT14.residual.accumulatedLedger->CT12",
  "CT15.residual.accumulatedLedger->CT9",
  "CT12.residual.surplusPortLedger->CT6",
  "CT6.residual.baselineSpineDemand->CT15",
  "CT15.residual.sparsePairResponses->CT15",
  "CT9.residual.capacityTokenLedger->CT9",
  "CT9.residual.coupledClassOverload->CT9",
  "CT15.residual.accumulatedLedger->CT16.pdeRequirement",
  "CT15.residual.accumulatedLedger->CT10.pdeRequirement",
  "CT13.residual.accumulatedLedger->CT7.pdeRequirement",
  "CT3.residual.accumulatedLedger->CT7.pdeRequirement",
  "CT17.residual.accumulatedLedger->CT12.pdeRequirement",
  "CT12.residual.accumulatedLedger->CT11.pdeRequirement",
  "CT10.residual.accumulatedLedger->CT11.pdeRequirement",
  "CT11.residual.accumulatedLedger->CT14.pdeRequirement",
  "CT14.residual.accumulatedLedger->CT11.pdeRequirement",
  "CT3.residual.accumulatedLedger->CT14.pdeRequirement",
  "CT14.residual.accumulatedLedger->CT15.pdeRequirement",
  "CT15.residual.accumulatedLedger->CT13.pdeRequirement",
  "CT11.residual.accumulatedLedger->CT1.pdeRequirement",
  "CT14.residual.accumulatedLedger->CT16.pdeRequirement",
  "CT16.residual.accumulatedLedger->CT10.pdeRequirement",
  "CT7.residual.accumulatedLedger->CT16.pdeRequirement",
  "CT16.residual.accumulatedLedger->CT1.pdeRequirement",
  "CT3.residual.accumulatedLedger->CT13.pdeRequirement",
  "CT13.residual.accumulatedLedger->CT15.pdeRequirement",
  "CT15.residual.accumulatedLedger->CT14.pdeRequirement"
]

def expectedFamilyKeys : List String := [
  "CT1->CT2",
  "CT1->CT2",
  "CT1->CT12",
  "CT2->CT3",
  "CT2->CT10",
  "CT5->CT14",
  "CT6->CT9",
  "CT9->CT7",
  "CT14->CT14",
  "CT1->CT9",
  "CT1->CT10",
  "CT2->CT1",
  "CT3->CT1",
  "CT5->CT2",
  "CT7->CT5",
  "CT5->CT10",
  "CT9->CT1",
  "CT9->CT5",
  "CT9->CT10",
  "CT9->CT14",
  "CT10->CT5",
  "CT10->CT6",
  "CT10->CT9",
  "CT10->CT14",
  "CT12->CT10",
  "CT12->CT15",
  "CT14->CT1",
  "CT14->CT12",
  "CT15->CT9",
  "CT12->CT6",
  "CT6->CT15",
  "CT15->CT15",
  "CT9->CT9",
  "CT9->CT9",
  "CT15->CT16",
  "CT15->CT10",
  "CT13->CT7",
  "CT3->CT7",
  "CT17->CT12",
  "CT12->CT11",
  "CT10->CT11",
  "CT11->CT14",
  "CT14->CT11",
  "CT3->CT14",
  "CT14->CT15",
  "CT15->CT13",
  "CT11->CT1",
  "CT14->CT16",
  "CT16->CT10",
  "CT7->CT16",
  "CT16->CT1",
  "CT3->CT13",
  "CT13->CT15",
  "CT15->CT14"
]

def expectedEdgeKeys : List String :=
  List.zipWith (fun family profile => family ++ ":" ++ profile)
    expectedFamilyKeys expectedProfileIds

theorem ctCount_exact : Registry.ctIds.length = 17 := by
  decide

theorem specializedBaselineCount_exact :
    Registry.baselineSpecialized.length = 9 := by
  decide

theorem accumulatedBaselineCount_exact :
    Registry.baselineAccumulated.length = 20 := by
  decide

theorem sourceProfileCount_exact :
    Registry.baselineProfiles.length = 29 := by
  decide

theorem egRequirementCount_exact :
    Registry.egRequirements.length = 5 := by
  decide

theorem pdeRequirementCount_exact :
    Registry.pdeRequirements.length = 20 := by
  decide

theorem plannedRequirementCount_exact :
    Registry.plannedRequirements.length = 25 := by
  decide

theorem catalogCount_exact : Registry.all.length = 54 := by
  decide

set_option maxRecDepth 100000 in
theorem specializedBaselineTags_exact :
    ∀ entry ∈ Registry.baselineSpecialized,
      entry.owner = Registry.Owner.sourceRegistry ∧
      entry.kind = Registry.Kind.specializedDiscovery ∧
      entry.status = Registry.Status.baseline := by
  decide

set_option maxRecDepth 100000 in
theorem accumulatedBaselineTags_exact :
    ∀ entry ∈ Registry.baselineAccumulated,
      entry.owner = Registry.Owner.sourceRegistry ∧
      entry.kind = Registry.Kind.genericAccumulated ∧
      entry.status = Registry.Status.baseline := by
  decide

set_option maxRecDepth 100000 in
theorem egRequirementTags_exact :
    ∀ entry ∈ Registry.egRequirements,
      entry.owner = Registry.Owner.erdosGyarf64 ∧
      entry.kind = Registry.Kind.profileRequirement ∧
      entry.status = Registry.Status.planned := by
  decide

set_option maxRecDepth 100000 in
theorem pdeRequirementTags_exact :
    ∀ entry ∈ Registry.pdeRequirements,
      entry.owner = Registry.Owner.pdeArchitecture ∧
      entry.kind = Registry.Kind.familyRequirement ∧
      entry.status = Registry.Status.planned := by
  decide

set_option maxRecDepth 100000 in
theorem ctKeys_exact : Registry.ctKeys = expectedCTKeys := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem profileIds_exact :
    Registry.profileIds Registry.all = expectedProfileIds := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem familyKeys_exact :
    Registry.all.map Registry.Entry.familyKey = expectedFamilyKeys := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem edgeKeys_exact :
    Registry.edgeKeys Registry.all = expectedEdgeKeys := by
  decide

theorem noDuplicateProfileKeys :
    (Registry.profileIds Registry.all).Nodup :=
  Registry.allProfileIds_nodup

theorem noDuplicateEdgeKeys :
    (Registry.edgeKeys Registry.all).Nodup :=
  Registry.allEdgeKeys_nodup

set_option maxRecDepth 100000 in
/-- Planned rows cannot be passed to the generic accumulated constructor.
They must first acquire a real profile kind together with endpoint modules. -/
theorem plannedRows_areNotGenericAccumulated :
    ∀ entry ∈ Registry.plannedRequirements,
      entry.kind ≠ Registry.Kind.genericAccumulated := by
  decide

theorem ct9RequirementProfiles_distinct :
    Registry.egCt9ToCt9CapacityToken.profileId ≠
      Registry.egCt9ToCt9CoupledOverload.profileId :=
  Registry.ct9RefinementProfileKeys_distinct

theorem ct9RequirementEdges_distinct :
    Registry.egCt9ToCt9CapacityToken.edgeKey ≠
      Registry.egCt9ToCt9CoupledOverload.edgeKey :=
  Registry.ct9RefinementEdgeKeys_distinct

/-! ## Representative full-ledger execution -/

structure ToyResidual where
  rootValue : Nat

def root : Residual.Ledger ToyResidual :=
  Residual.Ledger.initial ⟨7⟩

abbrev Predecessor :=
  Residual.Ledger.Extension (Residual.Ledger ToyResidual) (fun _ => Nat)

/-- The route receives this complete two-level ledger, not just `37`. -/
def predecessor : Predecessor :=
  Residual.Ledger.extend root 37

def targetSpec : Execution.Spec Predecessor where
  Input := fun _ => PUnit
  Outcome := fun _ _ => Nat
  Trace := fun previous _ outcome =>
    PLift (outcome = previous.added + (Residual.residualOf previous).rootValue)
  Sound := fun previous _ outcome _trace =>
    outcome = previous.added + (Residual.residualOf previous).rootValue
  Exhaustive := fun previous _ outcome =>
    outcome = previous.added + (Residual.residualOf previous).rootValue

def targetCapability : Execution.Capability targetSpec where
  reference := fun previous _ => ⟨⟨
    previous.added + (Residual.residualOf previous).rootValue,
    ⟨rfl⟩
  ⟩, 1⟩
  sound := by
    intro previous input
    rfl
  exhaustive := by
    intro previous input
    rfl
  work := PolynomialCheckBudget.constant (fun _ => 1) 1
  checks_eq := by
    intro previous input
    rfl

def accumulatedProfile : Routing.Profile.{0, 0, 0, 0, 0, 0} Predecessor where
  Target := targetSpec
  executor := targetCapability
  Seed := fun _ => PUnit
  Blocked := fun _ => Empty
  discover := fun _ => .enabled PUnit.unit
  targetInput := fun _ _ => PUnit.unit

def transition :
    Routing.Transition.{0, 0, 0, 0, 0, 0}
      Registry.ct1ToCt9Accumulated.edge Predecessor :=
  Accumulated.register Registry.ct1ToCt9Accumulated rfl accumulatedProfile

def routed :=
  Accumulated.advance transition predecessor

/-- The complete predecessor is retained literally. -/
theorem fullLedgerPreserved : routed.previous = predecessor :=
  Accumulated.advance_previous transition predecessor

/-- A fact attached before routing remains available through the predecessor. -/
theorem predecessorFactReachable : routed.previous.added = 37 := by
  rfl

/-- The stable root residual remains available through every extension. -/
theorem rootResidualPreserved :
    Residual.residualOf routed = Residual.residualOf predecessor :=
  Accumulated.advance_residual transition predecessor

/-- The selected catalog identity is generated as route provenance. -/
theorem provenanceExact :
    routed.added.provenance.recorded = Registry.ct1ToCt9Accumulated.edge :=
  Accumulated.advance_provenance transition predecessor

/-- The representative profile takes its enabled branch. -/
theorem discoveryExact :
    routed.added.discovery = Routing.Discovery.enabled PUnit.unit := by
  rfl

/-- Target execution uses both the predecessor fact and stable root residual. -/
theorem targetExecutionExact :
    routed.added.execution.outcome = (44 : Nat) := by
  change (44 : Nat) = 44
  rfl

#print axioms ctKeys_exact
#print axioms profileIds_exact
#print axioms edgeKeys_exact
#print axioms noDuplicateProfileKeys
#print axioms fullLedgerPreserved
#print axioms rootResidualPreserved
#print axioms provenanceExact
#print axioms targetExecutionExact

end Hypostructure.Fixtures.RouteRegistry
