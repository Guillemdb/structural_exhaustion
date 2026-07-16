import StructuralExhaustion.Routes.InducedPathCrossWindowIncidencePair

namespace StructuralExhaustion.Examples.CrossWindowIncidencePairRoute

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Routes
open InducedPathColdCorridor

universe u

variable {V : Type u} {object : FiniteObject V}
variable (stub : CubicStub object)
variable (residual :
  InducedPathBranchExcessComponentEntry.CrossWindowResidual stub)

/-! A problem-independent fixture pins the route's exact literal-edge
provenance.  No Erdős-specific target or packing theorem is used. -/

noncomputable def routed :=
  InducedPathCrossWindowIncidencePair.route stub residual

example : (routed stub residual).leftToken = stub.token :=
  (routed stub residual).leftTokenExact

example : (routed stub residual).leftWindow ≠
    (routed stub residual).rightWindow :=
  (routed stub residual).windowsDistinct

example : (routed stub residual).rightToken.2.2.1 =
    InducedPathWindowLedger.selectedWindow object stub.window stub.position :=
  (routed stub residual).rightTokenNeighbor

example : (routed stub residual).rightToken =
    InducedPathColdBranchExcess.toToken
      (routed stub residual).rightLocalToken :=
  (routed stub residual).rightTokenExact

example (producer : Producer object) :
    ∃ reverseResidual,
      InducedPathBranchExcessComponentEntry.route producer stub =
        .crossWindow reverseResidual :=
  InducedPathBranchExcessComponentEntry.route_crossWindow_of_endpointDeleted
    producer stub residual.endpointDeleted

example {otherStub : CubicStub object}
    {otherResidual :
      InducedPathBranchExcessComponentEntry.CrossWindowResidual otherStub}
    (equal : (routed stub residual).rightToken =
      (routed otherStub otherResidual).rightToken) :
    (routed stub residual).leftToken =
      (routed otherStub otherResidual).leftToken :=
  InducedPathCrossWindowIncidencePair.leftToken_eq_of_rightToken_eq
    (routed stub residual) (routed otherStub otherResidual) equal

example : (routed stub residual).leftToken ≠
    (routed stub residual).rightToken :=
  (routed stub residual).tokensDistinct

example : InducedPathCrossWindowIncidencePair.additionalChecks = 0 :=
  InducedPathCrossWindowIncidencePair.additionalChecks_eq_zero

end StructuralExhaustion.Examples.CrossWindowIncidencePairRoute
