import StructuralExhaustion.CT15.FunctionalAdmissibleRank
import StructuralExhaustion.Graph.SupportStratifiedDetermination

namespace StructuralExhaustion.Graph.SupportStratifiedFunctionalRank

open StructuralExhaustion
open StructuralExhaustion.Graph.PackedBoundariedGluing

universe u v

variable (input : PackedMinimumDegreeCycle.StaticInput)
variable (ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target)
variable (Coordinate : Type v)

abbrev Carrier := SupportStratifiedDetermination.Interface input ctx Coordinate

/-- A raw quotient proposal on one exact boundaried carrier.  Its realization
and image-value types are part of the proposal because the manuscript allows
different quotient codomains `Q`; no realization family is enumerated. -/
structure Proposal (carrier : Carrier input ctx Coordinate) : Type (max u v + 1) where
  code : Coordinate → Nat
  Realization : Type (max u v)
  ImageValue : Type (max u v)
  carrierRealization : Realization
  qImage : Realization → Coordinate → ImageValue
  identifiedImages : ∀ {left right}, code left = code right →
    ∀ realization, qImage realization left = qImage realization right

/-- The paper's admission audit at the proposal's actual carrier interface.
It requires declared-coordinate support, boundary-profile preservation,
context-universal target response, and the proper/whole representative clause.
-/
structure Admissible
    (coordinateSupport : Coordinate → Finset ctx.G.Vertex)
    (declared : Finset Coordinate) {carrier : Carrier input ctx Coordinate}
    (proposal : Proposal input ctx Coordinate carrier) : Prop where
  carriesDeclared : ∀ coordinate ∈ declared,
    coordinateSupport coordinate ⊆ carrier.vertices
  preservesBoundary : ∀ {left right}, proposal.code left = proposal.code right →
    (carrier.coordinatePiece left).boundaryDegree carrier.boundaries =
      (carrier.coordinatePiece right).boundaryDegree carrier.boundaries
  targetComplete : ∀ {left right}, proposal.code left = proposal.code right →
    ∀ outside : Context carrier.Boundary,
      SupportStratifiedDetermination.response input ctx Coordinate carrier left outside =
        SupportStratifiedDetermination.response input ctx Coordinate carrier right outside
  representedReduction : ¬Function.Injective proposal.code →
    Nonempty
      (SupportStratifiedDetermination.Representative input ctx Coordinate carrier)

def declaredCoordinates (coordinates : FinEnum Coordinate) : Finset Coordinate :=
  @List.toFinset Coordinate coordinates.decEq coordinates.orderedValues

/-- Exact graph specialization of the manuscript's functional-admissible rank
family.  Candidates range propositionally over every proof-carrying connected
carrier and every admitted proposal on it. -/
def family (coordinateSupport : Coordinate → Finset ctx.G.Vertex)
    (coordinates : FinEnum Coordinate) : CT15.FunctionalAdmissibleRank.Family where
  Coordinate := Coordinate
  Carrier := Carrier input ctx Coordinate
  Proposal := Proposal input ctx Coordinate
  code := fun proposal ↦ proposal.code
  Admissible := fun proposal ↦
    Admissible input ctx Coordinate coordinateSupport
      (@declaredCoordinates Coordinate coordinates) proposal
  Realization := fun _carrier proposal ↦ proposal.Realization
  ImageValue := fun _carrier proposal ↦ proposal.ImageValue
  qImage := fun proposal ↦ proposal.qImage
  identifiedImages := fun proposal ↦ proposal.identifiedImages

def profile (coordinateSupport : Coordinate → Finset ctx.G.Vertex)
    (coordinates : FinEnum Coordinate) :
    CT15.FunctionalAdmissibleRank.Profile
      (family input ctx Coordinate coordinateSupport coordinates) where
  coordinates := coordinates

namespace Admissible

variable {input ctx Coordinate}
variable {coordinateSupport : Coordinate → Finset ctx.G.Vertex}
variable {coordinates : FinEnum Coordinate}
variable {carrier : Carrier input ctx Coordinate}
variable {proposal : Proposal input ctx Coordinate carrier}

/-- Admission's representative clause closes every non-injective proposal on
an eligible proper carrier, using exactly the existing CT3 representative. -/
theorem injective_of_originalEligible
    (admissible : Admissible input ctx Coordinate coordinateSupport
      (@declaredCoordinates Coordinate coordinates) proposal)
    (eligible : carrier.OriginalEligible) : Function.Injective proposal.code := by
  by_contra noninjective
  exact SupportStratifiedDetermination.Representative.impossible_of_originalEligible eligible
    (Classical.choice (admissible.representedReduction noninjective))

/-- The same admission clause closes a non-injective proposal on the literal
whole carrier through its certified closed reduction. -/
theorem injective_of_whole
    (admissible : Admissible input ctx Coordinate coordinateSupport
      (@declaredCoordinates Coordinate coordinates) proposal)
    (whole : carrier.IsWhole) : Function.Injective proposal.code := by
  by_contra noninjective
  exact SupportStratifiedDetermination.Representative.impossible_of_whole whole
    (Classical.choice (admissible.representedReduction noninjective))

end Admissible

namespace Profile

variable {input ctx Coordinate}
variable (coordinateSupport : Coordinate → Finset ctx.G.Vertex)
variable (coordinates : FinEnum Coordinate)

abbrev ExactProfile :=
  profile input ctx Coordinate coordinateSupport coordinates

/-- Under the manuscript's current admission definition, every candidate code
is injective: its carrier is either an eligible proper interface or the whole
graph, and the representative clause contradicts non-injectivity in either
case. -/
theorem candidate_code_injective
    (candidate : (ExactProfile coordinateSupport coordinates).Candidate) :
    Function.Injective candidate.proposal.code := by
  have admitted : Admissible input ctx Coordinate coordinateSupport
      (@declaredCoordinates Coordinate coordinates) candidate.proposal :=
    candidate.admissible
  rcases candidate.carrier.scope_exhaustive with eligible | whole
  · exact admitted.injective_of_originalEligible eligible
  · exact admitted.injective_of_whole whole

theorem declared_survives :
    (ExactProfile coordinateSupport coordinates).Survives
      (ExactProfile coordinateSupport coordinates).rankProfile.declaredCoordinates := by
  refine ⟨Finset.Subset.rfl, ?_⟩
  intro candidate
  exact (candidate_code_injective coordinateSupport coordinates candidate).injOn

/-- Consequently the functional-admissible target rank is definitionally
forced to the full declared-coordinate cardinality. -/
theorem targetRank_eq_coordinatesCard :
    (ExactProfile coordinateSupport coordinates).targetRank = coordinates.card := by
  apply Nat.le_antisymm
  · exact (ExactProfile coordinateSupport coordinates).rankProfile.targetRank_le_coordinates
  · have lower :=
      (ExactProfile coordinateSupport coordinates).rankProfile
        |>.surviving_card_le_targetRank
          (declared_survives coordinateSupport coordinates)
    rw [(ExactProfile coordinateSupport coordinates).rankProfile.declaredCoordinates_card]
      at lower
    exact lower

theorem no_rankDrop :
    ¬(ExactProfile coordinateSupport coordinates).targetRank < coordinates.card :=
  Nat.not_lt_of_ge (targetRank_eq_coordinatesCard coordinateSupport coordinates).ge

end Profile

end StructuralExhaustion.Graph.SupportStratifiedFunctionalRank
