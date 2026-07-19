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

/-- A graph-admitted proposal enters the canonical paper rank universe without
an application-specific wrapper.  Functionality is derived from the quotient
image law, not from outside-context Boolean responses. -/
def candidate
    {carrier : Graph.SupportStratifiedFunctionalRank.Carrier input ctx Coordinate}
    (proposal : Graph.SupportStratifiedFunctionalRank.Proposal
      input ctx Coordinate carrier)
    (admissible : Graph.SupportStratifiedFunctionalRank.Admissible
      input ctx Coordinate coordinateSupport
      (@Graph.SupportStratifiedFunctionalRank.declaredCoordinates
        Coordinate coordinates) proposal) :
    (rankProfile coordinateSupport coordinates).Candidate where
  carrier := carrier
  proposal := proposal
  admissible := admissible
  functional :=
    (rankProfile coordinateSupport coordinates).functional_of_identified_images
      proposal

theorem candidate_code
    {carrier : Graph.SupportStratifiedFunctionalRank.Carrier input ctx Coordinate}
    (proposal : Graph.SupportStratifiedFunctionalRank.Proposal
      input ctx Coordinate carrier)
    (admissible : Graph.SupportStratifiedFunctionalRank.Admissible
      input ctx Coordinate coordinateSupport
      (@Graph.SupportStratifiedFunctionalRank.declaredCoordinates
        Coordinate coordinates) proposal) :
    (rankProfile coordinateSupport coordinates).system.code
        (candidate coordinateSupport coordinates proposal admissible) =
      proposal.code := rfl

end StructuralExhaustion.Examples.SupportStratifiedFunctionalRank
