import Hypostructure.Graph.Target

namespace HypostructureGraphQuickstart

open Hypostructure

abbrev K4 : Graph.FiniteObject where
  Vertex := Fin 4
  graph := ⊤
  vertices := inferInstance
  decideAdj := inferInstance

def Baseline (object : Graph.FiniteObject) : Prop :=
  2 <= object.vertexCount

def problem : Core.Problem :=
  Graph.problem Baseline (fun _object => Unit)

def baselineInvariant :
    Graph.FiniteObject.IsomorphismInvariant Baseline where
  iff_of_iso := by
    intro left right equivalent
    rw [Baseline, Baseline,
      Graph.FiniteObject.vertexCount_eq_of_isomorphic equivalent]

def semantics : Core.SemanticEquivalence problem :=
  Graph.isomorphismEquivalence Baseline (fun _object => Unit)
    baselineInvariant

def LengthOK (length : Nat) : Prop := length = 4

def Target (object : Graph.FiniteObject) : Prop :=
  Graph.HasCycleWithLength LengthOK object

def targetInterface : Graph.TargetInterface Target :=
  Graph.cycleTargetInterface LengthOK

def targetInvariant : Core.TargetInvariant semantics Target :=
  targetInterface.coreInvariant Baseline (fun _object => Unit)
    baselineInvariant

theorem k4_vertex_count : K4.vertexCount = 4 := by
  simp [K4, Graph.FiniteObject.vertexCount]

#print axioms targetInvariant

end HypostructureGraphQuickstart
