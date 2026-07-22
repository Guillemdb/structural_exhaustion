import Hypostructure.Core.Metadata
import Hypostructure.Graph.External.HegdeSandeepShashank
import HypostructureErdos64EG.Node15
import HypostructureErdos64EG.TargetAlgebra

/-!
# Diagram node 16: close the `P13`-free branch via HSS

Node 16 closes node-15's avoiding branch through CT1's focused continuation.
The active focus and literal predecessor ledger remain framework-owned.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u v

/-- P13-freeness of the selected branch yields a cycle with power-of-two length. -/
theorem node16_closedCycleFromP13Free (stage : Node15Stage.{u, v})
    (active : Node15Focus.Active stage)
    (p13free : Graph.InducedObstructionFree p13Obstruction
      (node15ObjectQuery.read stage.previous active)) :
    Graph.HasCycleWithLength PowerOfTwoLength
      (node15ObjectQuery.read stage.previous active) := by
  let context := node4ContextAtNode14Query.read stage.previous active
  have hssCycle :=
    Hypostructure.Graph.External.HegdeSandeepShashank.finiteObject_p13Free_hasPowerOfTwoCycle
      (node15ObjectQuery.read stage.previous active)
      context.baseline
      p13free
  exact ⟨{
    vertex := hssCycle.some.vertex,
    walk := hssCycle.some.walk,
    isCycle := hssCycle.some.isCycle,
    length_ok := (powerOfTwoLength_iff _).2 hssCycle.some.length_ok
  }⟩

def Node16PublicTarget (stage : Node15Stage.{u, v})
    (active : Node15Focus.Active stage) : Prop :=
  Graph.HasInducedObstruction p13Obstruction
    (node15ObjectQuery.read stage.previous active)

theorem node16_target_possible (stage : Node15Stage.{u, v})
    (active : Node15Focus.Active stage) : Node16PublicTarget stage active := by
  classical
  by_contra absent
  have cycle := node16_closedCycleFromP13Free stage active absent
  exact (node4ContextAtNode14Query.read stage.previous active).avoids cycle

set_option maxHeartbeats 1000000 in
def node16TargetPossibleQuery :
    Core.Residual.Focus.ActiveQuery Node15Focus.{u, v}
      (fun stage active => Node16PublicTarget stage active) := by
  apply Core.Residual.Focus.ActiveQuery.ofFunction
  intro stage active
  exact node16_target_possible stage active

abbrev Node16Stage := node15Encoding.{u, v}.C1Stage
set_option maxHeartbeats 1000000 in
abbrev Node16Focus := node15Encoding.{u, v}.C1Profile

set_option maxHeartbeats 1000000 in
noncomputable def node16 (previous : Node15Stage.{u, v}) : Node16Stage.{u, v} :=
  node15Encoding.{u, v}.closeAvoidingContinueC1 previous
    node16TargetPossibleQuery

#print axioms node16_closedCycleFromP13Free
#print axioms node16

end HypostructureErdos64EG
