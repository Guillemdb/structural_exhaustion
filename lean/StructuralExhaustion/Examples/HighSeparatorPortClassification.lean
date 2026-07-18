import Mathlib.Combinatorics.SimpleGraph.Basic
import StructuralExhaustion.Graph.HighSeparatorPortClassificationRoutes

namespace StructuralExhaustion.Examples.HighSeparatorPortClassificationK34

open StructuralExhaustion

/-! Non-Erdős transfer on `K₃,₄`: a left vertex is high, every right
endpoint is cubic, and two recovered right ports are open but fail the final
fan field because their two left shoulders coincide. -/

abbrev Vertex := Fin 3 ⊕ Fin 4

def graph : SimpleGraph Vertex := completeBipartiteGraph (Fin 3) (Fin 4)

def input : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    intro left right
    cases left <;> cases right <;>
      simp [graph, completeBipartiteGraph] <;> infer_instance

local instance : DecidableEq Vertex := input.vertices.decEq

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

def center : Vertex := Sum.inl 0

def centerHigh : 4 ≤ object.degree center := by native_decide

def firstPort : Graph.HighCenterPort.Port object center := ⟨0, by native_decide⟩

def secondPort : Graph.HighCenterPort.Port object center := ⟨1, by native_decide⟩

theorem rightDegree (vertex : Fin 4) :
    object.degree (Sum.inr vertex) = 3 := by
  fin_cases vertex <;> native_decide

theorem deletionCritical : ∀ dart : object.graph.Dart,
    object.degree dart.fst = 3 ∨ object.degree dart.snd = 3 := by
  rintro ⟨⟨left, right⟩, adjacent⟩
  cases left with
  | inl left =>
      cases right with
      | inl right => simp [object, graph, completeBipartiteGraph] at adjacent
      | inr right => exact Or.inr (rightDegree right)
  | inr left =>
      cases right with
      | inl right => exact Or.inl (rightDegree left)
      | inr right => simp [object, graph, completeBipartiteGraph] at adjacent

noncomputable def table :=
  Graph.HighSeparatorPortClassification.pairTable object center centerHigh
    deletionCritical firstPort secondPort

def typeCase :=
  Graph.HighSeparatorPortClassification.classifyPairCase object center centerHigh
    deletionCritical firstPort secondPort

example : Graph.HighCenterPort.portType object center centerHigh
    deletionCritical firstPort = .open := by native_decide

example : Graph.HighCenterPort.portType object center centerHigh
    deletionCritical secondPort = .open := by native_decide

theorem firstEndpoint : Graph.HighCenterPort.endpoint object center firstPort =
    (Sum.inr 0 : Vertex) := by native_decide

theorem secondEndpoint : Graph.HighCenterPort.endpoint object center secondPort =
    (Sum.inr 1 : Vertex) := by native_decide

theorem firstShoulders :
    Graph.HighCenterPort.shoulderVertices object center firstPort =
      [Sum.inl 1, Sum.inl 2] := by native_decide

theorem secondShoulders :
    Graph.HighCenterPort.shoulderVertices object center secondPort =
      [Sum.inl 1, Sum.inl 2] := by native_decide

theorem firstOutside : Graph.HighCenterPort.endpoint object center firstPort ∉
    Graph.HighCenterPort.shoulderVertices object center secondPort := by
  rw [firstEndpoint, secondShoulders]
  simp

theorem secondOutside : Graph.HighCenterPort.endpoint object center secondPort ∉
    Graph.HighCenterPort.shoulderVertices object center firstPort := by
  rw [secondEndpoint, firstShoulders]
  simp

theorem sharedFirst : (Sum.inl 1 : Vertex) ∈
    Graph.HighCenterPort.shoulderVertices object center firstPort := by
  rw [firstShoulders]
  simp

theorem sharedSecond : (Sum.inl 1 : Vertex) ∈
    Graph.HighCenterPort.shoulderVertices object center secondPort := by
  rw [secondShoulders]
  simp

theorem shouldersNotDisjoint : ¬List.Disjoint
    (Graph.HighCenterPort.shoulderVertices object center firstPort)
    (Graph.HighCenterPort.shoulderVertices object center secondPort) := by
  intro disjoint
  exact (List.disjoint_left.mp disjoint) sharedFirst sharedSecond

theorem portsNe : firstPort ≠ secondPort := by native_decide

/-- The generic failure consumer reconstructs an actual square in `K₃,₄`. -/
theorem squareExit : Graph.HasCycleWithLength object.graph
    Graph.HighCenterStructure.FourLength :=
  Graph.HighSeparatorPortClassification.hasFourCycle_of_shouldersNotDisjoint
    object center portsNe shouldersNotDisjoint

def expectedFailure : Graph.HighSeparatorPortClassification.FanFailure
    object center firstPort secondPort :=
  .shouldersNotDisjoint firstOutside secondOutside shouldersNotDisjoint

theorem fan_exact : table.fan = .failed expectedFailure := by
  unfold table Graph.HighSeparatorPortClassification.pairTable
  unfold Graph.HighSeparatorPortClassification.classifyFan
  simp only [dif_pos firstOutside, dif_pos secondOutside,
    dif_neg shouldersNotDisjoint]
  rfl

example : ¬Graph.HighCenterPort.FanCompatible object center
    firstPort secondPort :=
  Graph.HighSeparatorPortClassification.failure_not_compatible object center
    expectedFailure

example : table.fan.Valid :=
  Graph.HighSeparatorPortClassification.classifyFan_valid object center _ _

example : Graph.HighSeparatorPortClassification.checks = 10 :=
  Graph.HighSeparatorPortClassification.checks_eq_ten

/-- The complete first semantic split is reusable outside the Erdős
instantiation and consumes only the two declared `K₃,₄` ports. -/
noncomputable example :
    Graph.HighSeparatorPortClassification.PairSemanticOutcome object center
      centerHigh deletionCritical firstPort secondPort :=
  Graph.HighSeparatorPortClassification.classifyPairSemantics object center
    centerHigh deletionCritical firstPort secondPort portsNe

example : Nonempty
    (Graph.HighSeparatorPortClassification.PairSemanticOutcome object center
      centerHigh deletionCritical firstPort secondPort) :=
  Graph.HighSeparatorPortClassification.classifyPairSemantics_total object center
    centerHigh deletionCritical firstPort secondPort portsNe

example : Graph.HighSeparatorPortClassification.pairSemanticChecks = 10 :=
  Graph.HighSeparatorPortClassification.pairSemanticChecks_eq_ten

end StructuralExhaustion.Examples.HighSeparatorPortClassificationK34
