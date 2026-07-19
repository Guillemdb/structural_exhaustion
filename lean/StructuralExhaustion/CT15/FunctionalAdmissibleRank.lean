import StructuralExhaustion.CT15.CertifiedDeterminationRank

namespace StructuralExhaustion.CT15.FunctionalAdmissibleRank

open StructuralExhaustion

universe uCoordinate uCarrier uProposal uRealization uImage

/-!
# Rank over functional admissible quotients

This is the literal rank universe used by the manuscript.  It deliberately
does not identify an exact-profile realization with an outside context.  A
graph application supplies its carrier-indexed quotient proposals, admission
predicate, realizations, quotient-image values, and quotient-image map.

The framework then packages exactly the proposals that are both admissible and
functional as the candidates seen by CT15.  No quotient, realization, carrier,
or coordinate subfamily is enumerated.
-/

/-- Carrier-indexed semantics of quotients of one declared coordinate family.
Every member of `Realization carrier proposal` is, by construction, one
realization of the exact response profile under that proposal. -/
structure Family where
  Coordinate : Type uCoordinate
  Carrier : Type uCarrier
  Proposal : Carrier → Type uProposal
  code : {carrier : Carrier} → Proposal carrier → Coordinate → Nat
  Admissible : {carrier : Carrier} → Proposal carrier → Prop
  Realization : (carrier : Carrier) → Proposal carrier → Type uRealization
  ImageValue : (carrier : Carrier) → Proposal carrier → Type uImage
  qImage : {carrier : Carrier} → (proposal : Proposal carrier) →
    Realization carrier proposal → Coordinate → ImageValue carrier proposal
  identifiedImages : {carrier : Carrier} → (proposal : Proposal carrier) →
    ∀ {left right : Coordinate}, code proposal left = code proposal right →
      ∀ realization,
        qImage proposal realization left = qImage proposal realization right

/-- One finite declared coordinate family evaluated under `family`. -/
structure Profile (family : Family) where
  coordinates : FinEnum family.Coordinate

namespace Profile

variable {family : Family} (profile : Profile family)

def declaredCoordinates : Finset family.Coordinate :=
  @List.toFinset family.Coordinate profile.coordinates.decEq
    profile.coordinates.orderedValues

/-- A vector that is actually attained by a realization of the quotient exact
profile.  The evaluator below is therefore defined only on the realized
vectors required by the manuscript, rather than on an artificially enlarged
Cartesian power. -/
def RealizedVector {carrier : family.Carrier}
    (proposal : family.Proposal carrier)
    (basis : Finset family.Coordinate) :=
  {values : basis → family.ImageValue carrier proposal //
    ∃ realization : family.Realization carrier proposal,
      values = fun coordinate ↦
        family.qImage proposal realization coordinate.1}

/-- The quotient-image value of `coordinate` is a function of the realized
quotient-image vector on `basis`, exactly as in the manuscript definition. -/
def Determines {carrier : family.Carrier}
    (proposal : family.Proposal carrier)
    (basis : Finset family.Coordinate) (coordinate : family.Coordinate) : Prop :=
  ∃ evaluate : RealizedVector proposal basis →
      family.ImageValue carrier proposal,
    ∀ realization : family.Realization carrier proposal,
      family.qImage proposal realization coordinate =
        evaluate ⟨fun basisCoordinate ↦
          family.qImage proposal realization basisCoordinate.1,
          ⟨realization, rfl⟩⟩

/-- The manuscript's functional quotient axiom on the declared family. -/
def Functional {carrier : family.Carrier}
    (proposal : family.Proposal carrier) : Prop :=
  ∀ (independent : Finset family.Coordinate)
      (coordinate : family.Coordinate),
    independent ⊆ profile.declaredCoordinates →
    coordinate ∈ profile.declaredCoordinates →
    coordinate ∉ independent →
    Set.InjOn (family.code proposal) (independent : Set family.Coordinate) →
    ¬Set.InjOn (family.code proposal)
      (Set.insert coordinate (independent : Set family.Coordinate)) →
    ∃ basis : Finset family.Coordinate,
      basis ⊆ independent ∧ Determines proposal basis coordinate

/-- Exactly one member of the paper's rank-quotient universe: a carrier, a raw
proposal on that carrier, its admission certificate, and its functional
certificate. -/
structure Candidate where
  carrier : family.Carrier
  proposal : family.Proposal carrier
  admissible : family.Admissible proposal
  functional : profile.Functional proposal

/-- The generic CT15 rank engine sees precisely the code of a functional
admissible quotient; all semantic evidence stays in the retained candidate. -/
@[reducible] def system : CertifiedDeterminationRank.System where
  Coordinate := family.Coordinate
  Candidate := profile.Candidate
  code := fun candidate ↦ family.code candidate.proposal

def rankProfile : CertifiedDeterminationRank.Profile profile.system where
  coordinates := profile.coordinates

abbrev Survives (coordinates : Finset family.Coordinate) : Prop :=
  profile.rankProfile.Survives coordinates

noncomputable abbrev targetRank : Nat := profile.rankProfile.targetRank

abbrev RankDecision := profile.rankProfile.RankDecision

noncomputable def rankDecision : profile.RankDecision :=
  profile.rankProfile.rankDecision

theorem rankDecision_exhaustive :
    profile.targetRank < profile.coordinates.card ∨
      profile.targetRank = profile.coordinates.card :=
  profile.rankProfile.rankDecision_exhaustive

abbrev PairCircuit := profile.rankProfile.PairCircuit

noncomputable def pairCircuitOfRankDrop
    (rankDrop : profile.targetRank < profile.coordinates.card) :
    profile.PairCircuit :=
  profile.rankProfile.pairCircuitOfRankDrop rankDrop

def rankDecisionBudget : Core.PolynomialCheckBudget Unit :=
  profile.rankProfile.rankDecisionBudget

/-- The explicit singleton case in the paper: if a quotient identifies `a`
with `b`, the realized image of `a` is determined by the one-coordinate basis
`{b}`. -/
theorem determines_singleton_of_identified
    {carrier : family.Carrier} (proposal : family.Proposal carrier)
    {basisCoordinate coordinate : family.Coordinate}
    (identified : family.code proposal basisCoordinate =
      family.code proposal coordinate) :
    Determines proposal {basisCoordinate} coordinate := by
  classical
  let basisMember : ({basisCoordinate} : Finset family.Coordinate) :=
    ⟨basisCoordinate, by simp⟩
  refine ⟨fun realized ↦ realized.1 basisMember, ?_⟩
  intro realization
  exact (family.identifiedImages proposal identified realization).symm

/-- The label-identification clause of quotient semantics proves the paper's
functional axiom with a singleton basis at the first loss of injectivity. -/
theorem functional_of_identified_images {carrier : family.Carrier}
    (proposal : family.Proposal carrier) : profile.Functional proposal := by
  letI : DecidableEq family.Coordinate := profile.coordinates.decEq
  intro independent coordinate _independentDeclared _coordinateDeclared
    coordinateNotMem independentInjective insertedNotInjective
  have codeMem : family.code proposal coordinate ∈
      family.code proposal '' (independent : Set family.Coordinate) := by
    by_contra codeNotMem
    apply insertedNotInjective
    have coordinateNotMemSet :
        coordinate ∉ (independent : Set family.Coordinate) := by
      simpa using coordinateNotMem
    exact (Set.injOn_insert coordinateNotMemSet).2
      ⟨independentInjective, codeNotMem⟩
  rcases codeMem with ⟨basisCoordinate, basisMem, identified⟩
  refine ⟨{basisCoordinate}, ?_,
    determines_singleton_of_identified proposal identified⟩
  intro member memberInBasis
  have memberEq : member = basisCoordinate := by
    simpa using memberInBasis
  simpa [memberEq] using basisMem

/-- A strict loss retains the literal functional-admissible quotient candidate
and its realized singleton determination.  No support certificate is assumed
or reconstructed at rank-definition time. -/
theorem pairCircuit_determines (circuit : profile.PairCircuit) :
    Determines circuit.candidate.proposal circuit.basis circuit.determined := by
  exact determines_singleton_of_identified circuit.candidate.proposal
    circuit.identified

end Profile

end StructuralExhaustion.CT15.FunctionalAdmissibleRank
