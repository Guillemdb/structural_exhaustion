import Hypostructure.Core.Routing

/-!
# Stable transition profile registry

This catalog separates three facts that must not be conflated during the
migration:

* `baseline` rows record profiles that were executable in the source registry;
* `planned` rows record routes required by the EG or PDE migration; and
* only a separately supplied, typed `Core.Routing.Profile` can make a catalog
  row executable in Hypostructure.

Consequently, this file contains identities and requirements only.  It does
not manufacture endpoint capabilities or semantic discovery.
-/

namespace Hypostructure.Routes.Registry

open Hypostructure.Core

/-- The document or registry from which a route row originates. -/
inductive Owner where
  | sourceRegistry
  | erdosGyarf64
  | pdeArchitecture
  deriving Repr, DecidableEq

/-- The implementation shape recorded for a profile or requirement. -/
inductive Kind where
  | specializedDiscovery
  | genericAccumulated
  | profileRequirement
  | familyRequirement
  deriving Repr, DecidableEq

/-- Catalog status.  `baseline` describes the source registry, not current
Hypostructure endpoint availability. -/
inductive Status where
  | baseline
  | planned
  deriving Repr, DecidableEq

/-- Stable metadata for one transition profile or planned route requirement. -/
structure Entry where
  source : Routing.CTId
  target : Routing.CTId
  profileId : String
  owner : Owner
  kind : Kind
  status : Status
  deriving Repr, DecidableEq

namespace Entry

/-- The Core edge identity corresponding to this catalog row. -/
def edge (entry : Entry) : Routing.Edge where
  source := entry.source
  target := entry.target
  profile := entry.profileId

/-- Stable source/target family key. -/
def familyKey (entry : Entry) : String :=
  entry.edge.familyKey

/-- Stable full edge key.  The profile ID disambiguates profiles in one
source/target family. -/
def edgeKey (entry : Entry) : String :=
  entry.edge.key

end Entry

private def baselineSpecializedEntry
    (source target : Routing.CTId) (profileId : String) : Entry :=
  ⟨source, target, profileId, .sourceRegistry, .specializedDiscovery,
    .baseline⟩

private def baselineAccumulatedEntry
    (source target : Routing.CTId) (profileId : String) : Entry :=
  ⟨source, target, profileId, .sourceRegistry, .genericAccumulated,
    .baseline⟩

private def egRequirementEntry
    (source target : Routing.CTId) (profileId : String) : Entry :=
  ⟨source, target, profileId, .erdosGyarf64, .profileRequirement, .planned⟩

private def pdeRequirementEntry
    (source target : Routing.CTId) (profileId : String) : Entry :=
  ⟨source, target, profileId, .pdeArchitecture, .familyRequirement, .planned⟩

/-! ## Stable CT catalog -/

/-- Every CT identity, in stable numeric order. -/
def ctIds : List Routing.CTId := [
  .ct1, .ct2, .ct3, .ct4, .ct5, .ct6, .ct7, .ct8, .ct9,
  .ct10, .ct11, .ct12, .ct13, .ct14, .ct15, .ct16, .ct17
]

/-- Stable string keys for all CT identities. -/
def ctKeys : List String :=
  ctIds.map Routing.CTId.key

/-! ## Nine specialized source-registry profiles -/

def ct1ToCt2Ordinary : Entry :=
  baselineSpecializedEntry .ct1 .ct2 "CT1.residual.avoiding->CT2"

def ct1ToCt2LocalDeletion : Entry :=
  baselineSpecializedEntry .ct1 .ct2
    "CT1.residual.avoiding->CT2.localDeletion"

def ct1ToCt12C1 : Entry :=
  baselineSpecializedEntry .ct1 .ct12 "CT1.terminal.c1->CT12"

def ct2ToCt3SeparatingContext : Entry :=
  baselineSpecializedEntry .ct2 .ct3
    "CT2.residual.separatingContext->CT3"

def ct2ToCt10Criticality : Entry :=
  baselineSpecializedEntry .ct2 .ct10
    "CT2.residual.criticality->CT10"

def ct5ToCt14ChargeLedger : Entry :=
  baselineSpecializedEntry .ct5 .ct14
    "CT5.residual.chargeLedger->CT14"

def ct6ToCt9ActiveLedger : Entry :=
  baselineSpecializedEntry .ct6 .ct9
    "CT6.residual.activeLedger->CT9"

def ct9ToCt7Overload : Entry :=
  baselineSpecializedEntry .ct9 .ct7 "CT9.residual.overload->CT7"

def ct14ToCt14Capacity : Entry :=
  baselineSpecializedEntry .ct14 .ct14
    "CT14.residual.capacity->CT14"

/-- Exact nine-profile specialized baseline. -/
def baselineSpecialized : List Entry := [
  ct1ToCt2Ordinary,
  ct1ToCt2LocalDeletion,
  ct1ToCt12C1,
  ct2ToCt3SeparatingContext,
  ct2ToCt10Criticality,
  ct5ToCt14ChargeLedger,
  ct6ToCt9ActiveLedger,
  ct9ToCt7Overload,
  ct14ToCt14Capacity
]

/-! ## Twenty generic accumulated source-registry profiles -/

def ct1ToCt9Accumulated : Entry :=
  baselineAccumulatedEntry .ct1 .ct9
    "CT1.residual.accumulatedLedger->CT9"

def ct1ToCt10Accumulated : Entry :=
  baselineAccumulatedEntry .ct1 .ct10
    "CT1.residual.accumulatedLedger->CT10"

def ct2ToCt1Accumulated : Entry :=
  baselineAccumulatedEntry .ct2 .ct1
    "CT2.residual.accumulatedLedger->CT1"

def ct3ToCt1Accumulated : Entry :=
  baselineAccumulatedEntry .ct3 .ct1
    "CT3.residual.accumulatedLedger->CT1"

def ct5ToCt2Accumulated : Entry :=
  baselineAccumulatedEntry .ct5 .ct2
    "CT5.residual.accumulatedLedger->CT2"

def ct7ToCt5Accumulated : Entry :=
  baselineAccumulatedEntry .ct7 .ct5
    "CT7.residual.accumulatedLedger->CT5"

def ct5ToCt10Accumulated : Entry :=
  baselineAccumulatedEntry .ct5 .ct10
    "CT5.residual.accumulatedLedger->CT10"

def ct9ToCt1Accumulated : Entry :=
  baselineAccumulatedEntry .ct9 .ct1
    "CT9.residual.accumulatedLedger->CT1"

def ct9ToCt5Accumulated : Entry :=
  baselineAccumulatedEntry .ct9 .ct5
    "CT9.residual.accumulatedLedger->CT5"

def ct9ToCt10Accumulated : Entry :=
  baselineAccumulatedEntry .ct9 .ct10
    "CT9.residual.accumulatedLedger->CT10"

def ct9ToCt14Accumulated : Entry :=
  baselineAccumulatedEntry .ct9 .ct14
    "CT9.residual.accumulatedLedger->CT14"

def ct10ToCt5Accumulated : Entry :=
  baselineAccumulatedEntry .ct10 .ct5
    "CT10.residual.accumulatedLedger->CT5"

def ct10ToCt6Accumulated : Entry :=
  baselineAccumulatedEntry .ct10 .ct6
    "CT10.residual.accumulatedLedger->CT6"

def ct10ToCt9Accumulated : Entry :=
  baselineAccumulatedEntry .ct10 .ct9
    "CT10.residual.accumulatedLedger->CT9"

def ct10ToCt14Accumulated : Entry :=
  baselineAccumulatedEntry .ct10 .ct14
    "CT10.residual.accumulatedLedger->CT14"

def ct12ToCt10Accumulated : Entry :=
  baselineAccumulatedEntry .ct12 .ct10
    "CT12.residual.accumulatedLedger->CT10"

def ct12ToCt15Accumulated : Entry :=
  baselineAccumulatedEntry .ct12 .ct15
    "CT12.residual.accumulatedLedger->CT15"

def ct14ToCt1Accumulated : Entry :=
  baselineAccumulatedEntry .ct14 .ct1
    "CT14.residual.accumulatedLedger->CT1"

def ct14ToCt12Accumulated : Entry :=
  baselineAccumulatedEntry .ct14 .ct12
    "CT14.residual.accumulatedLedger->CT12"

def ct15ToCt9Accumulated : Entry :=
  baselineAccumulatedEntry .ct15 .ct9
    "CT15.residual.accumulatedLedger->CT9"

/-- Exact twenty-profile generic accumulated baseline. -/
def baselineAccumulated : List Entry := [
  ct1ToCt9Accumulated,
  ct1ToCt10Accumulated,
  ct2ToCt1Accumulated,
  ct3ToCt1Accumulated,
  ct5ToCt2Accumulated,
  ct7ToCt5Accumulated,
  ct5ToCt10Accumulated,
  ct9ToCt1Accumulated,
  ct9ToCt5Accumulated,
  ct9ToCt10Accumulated,
  ct9ToCt14Accumulated,
  ct10ToCt5Accumulated,
  ct10ToCt6Accumulated,
  ct10ToCt9Accumulated,
  ct10ToCt14Accumulated,
  ct12ToCt10Accumulated,
  ct12ToCt15Accumulated,
  ct14ToCt1Accumulated,
  ct14ToCt12Accumulated,
  ct15ToCt9Accumulated
]

/-- All 29 executable profiles recorded by the source registry.  Membership in
this list does not assert that a new CT endpoint has been implemented. -/
def baselineProfiles : List Entry :=
  baselineSpecialized ++ baselineAccumulated

/-! ## Five missing EG profile requirements -/

def egCt12ToCt6SurplusPort : Entry :=
  egRequirementEntry .ct12 .ct6
    "CT12.residual.surplusPortLedger->CT6"

def egCt6ToCt15BaselineSpine : Entry :=
  egRequirementEntry .ct6 .ct15
    "CT6.residual.baselineSpineDemand->CT15"

def egCt15ToCt15SparsePair : Entry :=
  egRequirementEntry .ct15 .ct15
    "CT15.residual.sparsePairResponses->CT15"

def egCt9ToCt9CapacityToken : Entry :=
  egRequirementEntry .ct9 .ct9
    "CT9.residual.capacityTokenLedger->CT9"

def egCt9ToCt9CoupledOverload : Entry :=
  egRequirementEntry .ct9 .ct9
    "CT9.residual.coupledClassOverload->CT9"

/-- Missing routes exposed by the EG migration. -/
def egRequirements : List Entry := [
  egCt12ToCt6SurplusPort,
  egCt6ToCt15BaselineSpine,
  egCt15ToCt15SparsePair,
  egCt9ToCt9CapacityToken,
  egCt9ToCt9CoupledOverload
]

/-! ## Twenty PDE family requirements -/

def pdeCt15ToCt16 : Entry :=
  pdeRequirementEntry .ct15 .ct16
    "CT15.residual.accumulatedLedger->CT16.pdeRequirement"

def pdeCt15ToCt10 : Entry :=
  pdeRequirementEntry .ct15 .ct10
    "CT15.residual.accumulatedLedger->CT10.pdeRequirement"

def pdeCt13ToCt7 : Entry :=
  pdeRequirementEntry .ct13 .ct7
    "CT13.residual.accumulatedLedger->CT7.pdeRequirement"

def pdeCt3ToCt7 : Entry :=
  pdeRequirementEntry .ct3 .ct7
    "CT3.residual.accumulatedLedger->CT7.pdeRequirement"

def pdeCt17ToCt12 : Entry :=
  pdeRequirementEntry .ct17 .ct12
    "CT17.residual.accumulatedLedger->CT12.pdeRequirement"

def pdeCt12ToCt11 : Entry :=
  pdeRequirementEntry .ct12 .ct11
    "CT12.residual.accumulatedLedger->CT11.pdeRequirement"

def pdeCt10ToCt11 : Entry :=
  pdeRequirementEntry .ct10 .ct11
    "CT10.residual.accumulatedLedger->CT11.pdeRequirement"

def pdeCt11ToCt14 : Entry :=
  pdeRequirementEntry .ct11 .ct14
    "CT11.residual.accumulatedLedger->CT14.pdeRequirement"

def pdeCt14ToCt11 : Entry :=
  pdeRequirementEntry .ct14 .ct11
    "CT14.residual.accumulatedLedger->CT11.pdeRequirement"

def pdeCt3ToCt14 : Entry :=
  pdeRequirementEntry .ct3 .ct14
    "CT3.residual.accumulatedLedger->CT14.pdeRequirement"

def pdeCt14ToCt15 : Entry :=
  pdeRequirementEntry .ct14 .ct15
    "CT14.residual.accumulatedLedger->CT15.pdeRequirement"

def pdeCt15ToCt13 : Entry :=
  pdeRequirementEntry .ct15 .ct13
    "CT15.residual.accumulatedLedger->CT13.pdeRequirement"

def pdeCt11ToCt1 : Entry :=
  pdeRequirementEntry .ct11 .ct1
    "CT11.residual.accumulatedLedger->CT1.pdeRequirement"

def pdeCt14ToCt16 : Entry :=
  pdeRequirementEntry .ct14 .ct16
    "CT14.residual.accumulatedLedger->CT16.pdeRequirement"

def pdeCt16ToCt10 : Entry :=
  pdeRequirementEntry .ct16 .ct10
    "CT16.residual.accumulatedLedger->CT10.pdeRequirement"

def pdeCt7ToCt16 : Entry :=
  pdeRequirementEntry .ct7 .ct16
    "CT7.residual.accumulatedLedger->CT16.pdeRequirement"

def pdeCt16ToCt1 : Entry :=
  pdeRequirementEntry .ct16 .ct1
    "CT16.residual.accumulatedLedger->CT1.pdeRequirement"

def pdeCt3ToCt13 : Entry :=
  pdeRequirementEntry .ct3 .ct13
    "CT3.residual.accumulatedLedger->CT13.pdeRequirement"

def pdeCt13ToCt15 : Entry :=
  pdeRequirementEntry .ct13 .ct15
    "CT13.residual.accumulatedLedger->CT15.pdeRequirement"

def pdeCt15ToCt14 : Entry :=
  pdeRequirementEntry .ct15 .ct14
    "CT15.residual.accumulatedLedger->CT14.pdeRequirement"

/-- Cross-CT families required by the PDE architecture. -/
def pdeRequirements : List Entry := [
  pdeCt15ToCt16,
  pdeCt15ToCt10,
  pdeCt13ToCt7,
  pdeCt3ToCt7,
  pdeCt17ToCt12,
  pdeCt12ToCt11,
  pdeCt10ToCt11,
  pdeCt11ToCt14,
  pdeCt14ToCt11,
  pdeCt3ToCt14,
  pdeCt14ToCt15,
  pdeCt15ToCt13,
  pdeCt11ToCt1,
  pdeCt14ToCt16,
  pdeCt16ToCt10,
  pdeCt7ToCt16,
  pdeCt16ToCt1,
  pdeCt3ToCt13,
  pdeCt13ToCt15,
  pdeCt15ToCt14
]

/-- Every route requirement that is deliberately not yet executable. -/
def plannedRequirements : List Entry :=
  egRequirements ++ pdeRequirements

/-- Complete profile and requirement catalog. -/
def all : List Entry :=
  baselineProfiles ++ plannedRequirements

/-- Profile IDs in catalog order. -/
def profileIds (entries : List Entry) : List String :=
  entries.map Entry.profileId

/-- Full edge keys in catalog order. -/
def edgeKeys (entries : List Entry) : List String :=
  entries.map Entry.edgeKey

set_option maxRecDepth 100000 in
/-- The CT catalog contains no repeated identity. -/
theorem ctIds_nodup : ctIds.Nodup := by
  decide

set_option maxRecDepth 100000 in
/-- Stable CT string keys do not collide. -/
theorem ctKeys_nodup : ctKeys.Nodup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- No baseline profile ID is repeated. -/
theorem baselineProfileIds_nodup :
    (profileIds baselineProfiles).Nodup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Planned requirements cannot collide with each other or with a baseline
profile. -/
theorem allProfileIds_nodup : (profileIds all).Nodup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Full edge keys are globally collision-free. -/
theorem allEdgeKeys_nodup : (edgeKeys all).Nodup := by
  decide

/-- The two CT9 refinement requirements have different semantic identities. -/
theorem ct9RefinementProfileKeys_distinct :
    egCt9ToCt9CapacityToken.profileId ≠
      egCt9ToCt9CoupledOverload.profileId := by
  decide

/-- Their full edge keys are distinct even though they share a family. -/
theorem ct9RefinementEdgeKeys_distinct :
    egCt9ToCt9CapacityToken.edgeKey ≠
      egCt9ToCt9CoupledOverload.edgeKey := by
  decide

end Hypostructure.Routes.Registry
