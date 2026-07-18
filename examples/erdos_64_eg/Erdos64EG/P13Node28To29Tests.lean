import Erdos64EG.P13Node28To29

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
  {node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21}
  {node26 : VerifiedP13Node26RemainderContinuation ctx node21 node24}
  {node27 : VerifiedP13Node27NoInternalThreeCore ctx node21 node24 node26}

example (node28 : VerifiedP13Node28PositiveDeficiency
    ctx node21 node24 node26 node27) :
    (node28.node29).previous = node28 :=
  (node28.node29).previousExact

example (node28 : VerifiedP13Node28PositiveDeficiency
    ctx node21 node24 node26 node27) :
    (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
      15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
        Graph.InducedPathWindowLedger.windowSurplus ctx.G.object :=
  (node28.node29).incidenceSupply

example (node28 : VerifiedP13Node28PositiveDeficiency
    ctx node21 node24 node26 node27) :
    (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ≤
      surplusScaleCoefficient node21.previous.windowSize
          node21.previous.remainderSize node21.previous.primitiveSize *
        ctx.G.object.input.vertices.card :=
  (node28.node29).nearCubic.surplus_sq_le

#print axioms VerifiedP13Node28PositiveDeficiency.node29

end Erdos64EG.Internal
