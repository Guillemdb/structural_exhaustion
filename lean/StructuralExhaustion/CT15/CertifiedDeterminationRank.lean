import StructuralExhaustion.Core.Enumeration
import StructuralExhaustion.Core.ZeroWorkBudget

namespace StructuralExhaustion.CT15.CertifiedDeterminationRank

open StructuralExhaustion

universe uCoordinate uCandidate

/-!
# Rank over proof-carrying determination candidates

The candidate type owns all semantic and support certificates required by an
application.  CT15 sees only its quotient code.  Thus a rank drop returns the
same candidate value, rather than reconstructing support or prematurely
assuming post-audit admissibility.
-/

structure System where
  Coordinate : Type uCoordinate
  Candidate : Type uCandidate
  code : Candidate → Coordinate → Nat

structure Profile (system : System) where
  coordinates : FinEnum system.Coordinate

namespace Profile

variable {system : System} (profile : Profile system)

def declaredCoordinates : Finset system.Coordinate :=
  @List.toFinset system.Coordinate profile.coordinates.decEq
    profile.coordinates.orderedValues

def Survives (family : Finset system.Coordinate) : Prop :=
  family ⊆ profile.declaredCoordinates ∧
    ∀ candidate : system.Candidate,
      Set.InjOn (system.code candidate) (family : Set system.Coordinate)

theorem declaredCoordinates_card :
    profile.declaredCoordinates.card = profile.coordinates.card := by
  unfold declaredCoordinates
  rw [@List.toFinset_card_of_nodup _ profile.coordinates.decEq _
    profile.coordinates.nodup_orderedValues]
  exact profile.coordinates.orderedValues_length

noncomputable def targetRank : Nat := by
  classical
  exact Nat.findGreatest
    (fun size => ∃ family : Finset system.Coordinate,
      profile.Survives family ∧ family.card = size)
    profile.coordinates.card

theorem targetRank_le_coordinates :
    profile.targetRank ≤ profile.coordinates.card := by
  unfold targetRank
  classical
  exact Nat.findGreatest_le _

theorem surviving_card_le_targetRank
    {family : Finset system.Coordinate} (survives : profile.Survives family) :
    family.card ≤ profile.targetRank := by
  unfold targetRank
  classical
  apply Nat.le_findGreatest
  · calc
      family.card ≤ profile.declaredCoordinates.card :=
        Finset.card_le_card survives.1
      _ = profile.coordinates.card := profile.declaredCoordinates_card
  · exact ⟨family, survives, rfl⟩

theorem exists_surviving_card_eq_targetRank :
    ∃ family : Finset system.Coordinate,
      profile.Survives family ∧ family.card = profile.targetRank := by
  unfold targetRank
  classical
  apply Nat.findGreatest_spec
    (P := fun size => ∃ family : Finset system.Coordinate,
      profile.Survives family ∧ family.card = size)
    (m := 0) (n := profile.coordinates.card)
  · omega
  · refine ⟨∅, ?_, rfl⟩
    refine ⟨Finset.empty_subset _, ?_⟩
    intro candidate
    simp

/-- Exact proof-level split between strict loss and full declared rank. -/
inductive RankDecision where
  | dropped (rank_lt : profile.targetRank < profile.coordinates.card)
  | full (rank_eq : profile.targetRank = profile.coordinates.card)

noncomputable def rankDecision : profile.RankDecision := by
  classical
  by_cases dropped : profile.targetRank < profile.coordinates.card
  · exact .dropped dropped
  · exact .full (Nat.le_antisymm profile.targetRank_le_coordinates
      (Nat.le_of_not_gt dropped))

theorem rankDecision_exhaustive :
    profile.targetRank < profile.coordinates.card ∨
      profile.targetRank = profile.coordinates.card := by
  cases profile.rankDecision with
  | dropped rank_lt => exact Or.inl rank_lt
  | full rank_eq => exact Or.inr rank_eq

/-- Framework-owned decidability for the strict rank-loss constructor. -/
noncomputable def rankDropDecidable :
    Decidable (profile.targetRank < profile.coordinates.card) := by
  cases profile.rankDecision with
  | dropped rank_lt => exact isTrue rank_lt
  | full rank_eq => exact isFalse (Nat.not_lt_of_ge rank_eq.ge)

/-- Eliminate absence of the strict constructor into the exact full-rank
certificate.  Applications must not repeat this order-theoretic plumbing. -/
theorem fullRankOfNotDrop
    (notDropped : ¬ profile.targetRank < profile.coordinates.card) :
    profile.targetRank = profile.coordinates.card :=
  Nat.le_antisymm profile.targetRank_le_coordinates
    (Nat.le_of_not_gt notDropped)

/-- The exact candidate and identified coordinate pair selected by strict rank
loss.  Any graph support, context, boundary, and representative data remain
inside `candidate`. -/
structure PairCircuit where
  candidate : system.Candidate
  determined : system.Coordinate
  basisCoordinate : system.Coordinate
  determined_mem : determined ∈ profile.declaredCoordinates
  basis_mem : basisCoordinate ∈ profile.declaredCoordinates
  distinct : basisCoordinate ≠ determined
  identified :
    system.code candidate basisCoordinate = system.code candidate determined

namespace PairCircuit

variable {profile : Profile system}

/-- The singleton functional basis carried by a pair-collision circuit. -/
def basis (circuit : profile.PairCircuit) : Finset system.Coordinate :=
  @List.toFinset system.Coordinate profile.coordinates.decEq
    [circuit.basisCoordinate]

theorem basis_subset_declared (circuit : profile.PairCircuit) :
    circuit.basis ⊆ profile.declaredCoordinates := by
  intro coordinate member
  have equal : coordinate = circuit.basisCoordinate := by
    simpa [basis] using member
  simpa [equal] using circuit.basis_mem

theorem determined_not_mem_basis (circuit : profile.PairCircuit) :
    circuit.determined ∉ circuit.basis := by
  simpa [basis, ne_comm] using circuit.distinct

end PairCircuit

theorem pairCircuit_nonempty_of_rankDrop
    (rankDrop : profile.targetRank < profile.coordinates.card) :
    Nonempty profile.PairCircuit := by
  classical
  have notSurvives : ¬profile.Survives profile.declaredCoordinates := by
    intro survives
    have lower := profile.surviving_card_le_targetRank survives
    rw [profile.declaredCoordinates_card] at lower
    exact (Nat.not_lt_of_ge lower) rankDrop
  have noninjective : ∃ candidate : system.Candidate,
      ¬Set.InjOn (system.code candidate)
        (profile.declaredCoordinates : Set system.Coordinate) := by
    by_contra absent
    apply notSurvives
    refine ⟨Finset.Subset.rfl, ?_⟩
    intro candidate
    by_contra notInjective
    exact absent ⟨candidate, notInjective⟩
  obtain ⟨candidate, notInjective⟩ := noninjective
  simp only [Set.InjOn] at notInjective
  push Not at notInjective
  obtain ⟨left, leftMem, right, rightMem, identified, distinct⟩ := notInjective
  exact ⟨{
    candidate := candidate
    determined := right
    basisCoordinate := left
    determined_mem := rightMem
    basis_mem := leftMem
    distinct := distinct
    identified := identified
  }⟩

noncomputable def pairCircuitOfRankDrop
    (rankDrop : profile.targetRank < profile.coordinates.card) :
    profile.PairCircuit :=
  Classical.choice (profile.pairCircuit_nonempty_of_rankDrop rankDrop)

def rankDecisionBudget : Core.PolynomialCheckBudget Unit :=
  Core.PolynomialCheckBudget.zero (fun _ => profile.coordinates.card)

end Profile

end StructuralExhaustion.CT15.CertifiedDeterminationRank
