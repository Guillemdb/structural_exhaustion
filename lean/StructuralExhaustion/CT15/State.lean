import StructuralExhaustion.CT15.Capability

namespace StructuralExhaustion.CT15

universe uAmbient uBranch uCoordinate

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (S : Spec P) (capability : Capability S) (input : Input P)

/-- One coordinate contributes one unit exactly when it is independent of the
target. -/
def rankContribution (coordinate : S.Coordinate) : Nat :=
  match capability.targetDependentDecidable input coordinate with
  | .isTrue _ => 0
  | .isFalse _ => 1

/-- The exact target-relative rank in declared coordinate order. -/
def computedRank : Nat :=
  (capability.coordinates.orderedValues.map
    (rankContribution S capability input)).sum

/-- Full rank means that every enumerated coordinate contributes. -/
def targetRank : Nat := capability.coordinates.orderedValues.length

/-- Machine-computed target-relative rank. -/
structure RankState where
  value : Nat
  computed : value = computedRank S capability input

def computeRank : RankState S capability input where
  value := computedRank S capability input
  computed := rfl

/-- First dependent coordinate, retaining the exact independent prefix. -/
structure RankDropResidual (rank : RankState S capability input) where
  hit : Core.FiniteSearch.FirstHit capability.coordinates.orderedValues
    (S.TargetDependent input)

/-- Exhaustive full-rank evidence.  The equality is derived from the absence
of a dependent coordinate, not supplied by a proof instance. -/
structure FullRankState (rank : RankState S capability input) : Prop where
  noDrop : ∀ coordinate, ¬ S.TargetDependent input coordinate
  full : rank.value = targetRank S capability

/-- Canonical ordered full-rank ledger. -/
def ledgerEntries : List (S.Coordinate × Nat) :=
  capability.coordinates.orderedValues.map fun coordinate =>
    (coordinate, S.charge input coordinate)

def ledgerTotal : Nat :=
  (ledgerEntries S capability input).map Prod.snd |>.sum

/-- Exact ledger state indexed by the full-rank predecessor. -/
structure LedgerState {rank : RankState S capability input}
    (full : FullRankState S capability input rank) where
  entries : List (S.Coordinate × Nat)
  exact : entries = ledgerEntries S capability input
  total : Nat
  summed : total = ledgerTotal S capability input

def buildLedger {rank : RankState S capability input}
    (full : FullRankState S capability input rank) :
    LedgerState S capability input full where
  entries := ledgerEntries S capability input
  exact := rfl
  total := ledgerTotal S capability input
  summed := rfl

/-- Arithmetic C4: exact full-rank demand strictly exceeds capacity. -/
structure C4Certificate {rank : RankState S capability input}
    {full : FullRankState S capability input rank}
    (ledger : LedgerState S capability input full) : Prop where
  capacity_lt_total : S.capacity input < ledger.total

/-- Reusable full-rank ledger when capacity is sufficient. -/
structure FullRankLedgerResidual {rank : RankState S capability input}
    {full : FullRankState S capability input rank}
    (ledger : LedgerState S capability input full) : Prop where
  total_le_capacity : ledger.total ≤ S.capacity input

end StructuralExhaustion.CT15
