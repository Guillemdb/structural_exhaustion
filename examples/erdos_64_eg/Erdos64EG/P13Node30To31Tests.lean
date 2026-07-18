import Erdos64EG.P13Node30To31

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

example
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21}
    {node26 : VerifiedP13Node26RemainderContinuation ctx node21 node24}
    {node27 : VerifiedP13Node27NoInternalThreeCore ctx node21 node24 node26}
    {node28 : VerifiedP13Node28PositiveDeficiency
      ctx node21 node24 node26 node27}
    {node29 : VerifiedP13Node29ExternalIncidenceSupply
      ctx node21 node24 node26 node27 node28}
    (node30 : VerifiedP13Node30WedgeLower
      ctx node21 node24 node26 node27 node28 node29) :
    (node30.node31).previous = node30 :=
  (node30.node31).previousExact

#print axioms VerifiedP13Node30WedgeLower.node31

end Erdos64EG.Internal
