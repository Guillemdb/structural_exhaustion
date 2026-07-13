import Erdos64EG.CT1

namespace Erdos64EG.Tests

open StructuralExhaustion.Graph
open Erdos64EG.Internal

/-!
Small executable smoke fixture for the first slice.  `K₄` satisfies the
official baseline and contains the explicitly certified four-cycle below, so
the generated CT1 machine is forced to its C1 terminal.
-/

def k4 : Object (Fin 4) where
  graph := ⊤
  input := {
    vertices := inferInstance
    decideAdj := inferInstance
  }

theorem k4_baseline : Baseline k4 := by
  change 3 ≤ (⊤ : SimpleGraph (Fin 4)).minDegree
  simp

def fourCycleWalk : k4.graph.Walk (0 : Fin 4) 0 :=
  letI : DecidableRel k4.graph.Adj := k4.input.decideAdj
  .cons (show k4.graph.Adj 0 1 by decide) <|
    .cons (show k4.graph.Adj 1 2 by decide) <|
      .cons (show k4.graph.Adj 2 3 by decide) <|
        .cons (show k4.graph.Adj 3 0 by decide) .nil

theorem fourCycleWalk_isCycle : fourCycleWalk.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · rw [SimpleGraph.Walk.isPath_def]
    decide
  · decide

theorem fourCycleWalk_powerOfTwo :
    PowerOfTwoLength fourCycleWalk.length := by
  change PowerOfTwoLength 4
  exact ⟨⟨2, by decide⟩, by decide, rfl⟩

def k4Cycle : CycleWithLength k4.graph PowerOfTwoLength :=
  {
    vertex := 0
    walk := fourCycleWalk
    isCycle := fourCycleWalk_isCycle
    length_ok := fourCycleWalk_powerOfTwo
  }

def k4Target : Target k4 := ⟨k4Cycle⟩

/-- End-to-end local validation of the explicit cycle certificate. -/
def k4CT1Run :
    StructuralExhaustion.CT1.CertifiedC1Run
      (ct1Spec (Fin 4)) (ct1Input k4 k4_baseline) :=
  runCT1 k4 k4_baseline k4Cycle

end Erdos64EG.Tests
