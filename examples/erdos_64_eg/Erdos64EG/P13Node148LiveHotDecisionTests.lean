import Erdos64EG.P13Node148LiveHotDecision

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

example
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    p13Node148TotalDemand ctx =
      p13Node148HotDemand ctx node21 + p13Node148ColdDemand ctx node21 :=
  p13Node148_totalDemand_eq_hot_add_cold ctx node21

example
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node146No : P13Node146To148 ctx node21) :
    (∃ payload, runP13Node148 ctx node21 node146No = .to149 payload) ∨
      (∃ payload, runP13Node148 ctx node21 node146No = .to150 payload) :=
  runP13Node148_exhaustive ctx node21 node146No

example
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node146No : P13Node146To148 ctx node21)
    (payload : P13Node148To150 ctx node21 node146No) :
    p13Node148TotalDemand ctx - p13Node148Allowance ctx node21 ≤
      p13Node148ColdDemand ctx node21 :=
  payload.coldShortfall

example
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node146No : P13Node146To148 ctx node21)
    (payload : P13Node148To149 ctx node21 node146No) :
    payload.previous = node146No :=
  payload.exactPrevious

#print axioms p13Node148_hotDemand_le_allowance
#print axioms p13Node148_totalDemand_le_allowance_add_cold
#print axioms runP13Node148
#print axioms runP13Node148_exhaustive

end Erdos64EG.Internal
