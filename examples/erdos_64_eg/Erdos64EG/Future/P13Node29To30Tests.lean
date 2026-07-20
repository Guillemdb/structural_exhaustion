import Erdos64EG.Future.P13Node29To30

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
  {node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21}
  {node26 : VerifiedP13Node26RemainderContinuation ctx node21 node24}
  {node27 : VerifiedP13Node27NoInternalThreeCore ctx node21 node24 node26}
  {node28 : VerifiedP13Node28PositiveDeficiency
    ctx node21 node24 node26 node27}

example (node29 : VerifiedP13Node29ExternalIncidenceSupply
    ctx node21 node24 node26 node27 node28) :
    (node29.node30).previous = node29 :=
  (node29.node30).previousExact

example (node29 : VerifiedP13Node29ExternalIncidenceSupply
    ctx node21 node24 node26 node27 node28) :
    3 * (p13RemainderVertices ctx).card ≤
      (p13RemainderCurvatureProfile ctx).wedgeCount +
        30 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
        2 * Graph.InducedPathWindowLedger.totalSurplus ctx.G.object :=
  (node29.node30).windowFiniteSupply

#print axioms VerifiedP13Node29ExternalIncidenceSupply.node30

end Erdos64EG.Internal
