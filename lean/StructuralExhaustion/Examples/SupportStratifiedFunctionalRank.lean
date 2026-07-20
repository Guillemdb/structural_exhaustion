import StructuralExhaustion.Graph.SupportStratifiedFunctionalRank

namespace StructuralExhaustion.Examples.SupportStratifiedFunctionalRank

open StructuralExhaustion

universe u v

variable {input : Graph.PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
variable {Coordinate : Type v}
variable (coordinateSupport : Coordinate → Finset ctx.G.Vertex)
variable (coordinates : FinEnum Coordinate)

def rankProfile :=
  Graph.SupportStratifiedFunctionalRank.profile
    input ctx Coordinate coordinateSupport coordinates

def admittedRankProfile :=
  Graph.SupportStratifiedFunctionalRank.admittedProfile
    input ctx Coordinate coordinateSupport coordinates

/-- A non-Erdős consumer of the graph-owned proper/whole decision.  The
decision reads only the interface tag and its negative branch is returned as
the literal whole-support certificate. -/
def carrierScopeDecision
    (carrier : Graph.SupportStratifiedFunctionalRank.Carrier
      input ctx Coordinate) :
    Decidable carrier.OriginalEligible :=
  carrier.originalEligibleDecidable

theorem carrierWhole_of_not_originalEligible
    (carrier : Graph.SupportStratifiedFunctionalRank.Carrier
      input ctx Coordinate)
    (absent : ¬ carrier.OriginalEligible) : carrier.IsWhole :=
  carrier.whole_of_not_originalEligible absent

/-- A raw graph proposal enters the restriction-audit universe without
acquiring context-universality or representative clauses. -/
def candidate
    {carrier : Graph.SupportStratifiedFunctionalRank.Carrier input ctx Coordinate}
    (proposal : Graph.SupportStratifiedFunctionalRank.Proposal
      input ctx Coordinate carrier)
    (proposed : Graph.SupportStratifiedFunctionalRank.Proposed
      input ctx Coordinate coordinateSupport
      (@Graph.SupportStratifiedFunctionalRank.declaredCoordinates
        Coordinate coordinates) proposal) :
    (rankProfile coordinateSupport coordinates).Candidate where
  carrier := carrier
  proposal := proposal
  admissible := proposed
  functional :=
    (rankProfile coordinateSupport coordinates).functional_of_identified_images
      proposal

theorem candidate_code
    {carrier : Graph.SupportStratifiedFunctionalRank.Carrier input ctx Coordinate}
    (proposal : Graph.SupportStratifiedFunctionalRank.Proposal
      input ctx Coordinate carrier)
    (proposed : Graph.SupportStratifiedFunctionalRank.Proposed
      input ctx Coordinate coordinateSupport
      (@Graph.SupportStratifiedFunctionalRank.declaredCoordinates
        Coordinate coordinates) proposal) :
    (rankProfile coordinateSupport coordinates).system.code
        (candidate coordinateSupport coordinates proposal proposed) =
      proposal.code := rfl

/-- Full admission is a separate, explicit promotion of the same proposal.
This fixture prevents a restricted raw proposal from silently acquiring
outside-context validity. -/
def admit
    {carrier : Graph.SupportStratifiedFunctionalRank.Carrier input ctx Coordinate}
    (proposal : Graph.SupportStratifiedFunctionalRank.Proposal
      input ctx Coordinate carrier)
    (proposed : Graph.SupportStratifiedFunctionalRank.Proposed
      input ctx Coordinate coordinateSupport
      (@Graph.SupportStratifiedFunctionalRank.declaredCoordinates
        Coordinate coordinates) proposal)
    (targetComplete : ∀ {left right}, proposal.code left = proposal.code right →
      ∀ outside : Graph.PackedBoundariedGluing.Context carrier.Boundary,
        Graph.SupportStratifiedDetermination.response
            input ctx Coordinate carrier left outside =
          Graph.SupportStratifiedDetermination.response
            input ctx Coordinate carrier right outside)
    (representedReduction : ¬Function.Injective proposal.code →
      Nonempty (Graph.SupportStratifiedDetermination.Representative
        input ctx Coordinate carrier)) :
    Graph.SupportStratifiedFunctionalRank.Admissible
      input ctx Coordinate coordinateSupport
      (@Graph.SupportStratifiedFunctionalRank.declaredCoordinates
        Coordinate coordinates) proposal :=
  Graph.SupportStratifiedFunctionalRank.Admissible.ofProposed
    proposed targetComplete representedReduction

end StructuralExhaustion.Examples.SupportStratifiedFunctionalRank
