import Erdos64EG.TypeANode89SaturationDecision

namespace Erdos64EG.Internal.TypeANode89SaturationDecision

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

example {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} {node87 : Node87 node86}
    (node88 : Node88 node87) :
    (∃ payload, run (ctx := ctx) node88 = Outcome.to93 payload) ∨
      (∃ payload, run (ctx := ctx) node88 = Outcome.to90 payload) :=
  run_exhaustive (ctx := ctx) node88

example {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} {node87 : Node87 node86}
    (node88 : Node88 node87)
    (cubic : {vertex // vertex ∈ (input (ctx := ctx) node88).cubicSet}) :
    ((routing (ctx := ctx) node88).route cubic).1 =
      (node63.typeAProfile.receiverSelection ctx.G.object
        ⟨cubic.1, (Core.FiniteReceiverDischarge.Input.mem_cubicSet_iff
          (input (ctx := ctx) node88) cubic.1).1 cubic.2 |>.2⟩).vertex :=
  routedReceiver_eq_canonical (ctx := ctx) node88 cubic

#print axioms routing
#print axioms run
#print axioms run_exhaustive

end Erdos64EG.Internal.TypeANode89SaturationDecision
