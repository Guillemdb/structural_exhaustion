import Hypostructure.Graph.Finite
import Hypostructure.Core.SemanticEquivalence

/-!
# Isomorphism semantics for finite graph objects

Execution schedules are representation data and need not be preserved by an
isomorphism.  Mathematical observables are transported through Mathlib's
`SimpleGraph.Iso`.
-/

namespace Hypostructure.Graph

universe u v

namespace FiniteObject

/-- A concrete graph isomorphism between two packed finite objects. -/
abbrev Iso (left right : FiniteObject) :=
  left.graph ≃g right.graph

/-- Semantic equivalence of packed finite graph objects. -/
def Isomorphic (left right : FiniteObject) : Prop :=
  Nonempty (left.Iso right)

@[refl]
theorem isomorphic_refl (object : FiniteObject) : object.Isomorphic object :=
  ⟨SimpleGraph.Iso.refl⟩

@[symm]
theorem Isomorphic.symm {left right : FiniteObject}
    (equivalent : left.Isomorphic right) : right.Isomorphic left := by
  rcases equivalent with ⟨iso⟩
  exact ⟨iso.symm⟩

@[trans]
theorem Isomorphic.trans {left middle right : FiniteObject}
    (leftMiddle : left.Isomorphic middle)
    (middleRight : middle.Isomorphic right) : left.Isomorphic right := by
  rcases leftMiddle with ⟨leftMiddle⟩
  rcases middleRight with ⟨middleRight⟩
  exact ⟨leftMiddle.trans middleRight⟩

/-- Packed graph isomorphism is an equivalence relation. -/
theorem isomorphic_equivalence : Equivalence Isomorphic :=
  ⟨isomorphic_refl, Isomorphic.symm, Isomorphic.trans⟩

/-- A proposition on packed graphs that depends only on graph isomorphism. -/
structure IsomorphismInvariant (Property : FiniteObject → Prop) : Prop where
  iff_of_iso : ∀ {left right}, left.Isomorphic right →
    (Property left ↔ Property right)

namespace IsomorphismInvariant

theorem transport {Property : FiniteObject → Prop}
    (invariant : IsomorphismInvariant Property)
    {left right : FiniteObject} (equivalent : left.Isomorphic right) :
    Property left → Property right :=
  (invariant.iff_of_iso equivalent).mp

end IsomorphismInvariant

theorem vertexCount_eq_of_iso {left right : FiniteObject}
    (iso : left.Iso right) : left.vertexCount = right.vertexCount := by
  letI : FinEnum left.Vertex := left.vertices
  letI : FinEnum right.Vertex := right.vertices
  simpa [vertexCount, FinEnum.card_eq_fintypeCard] using iso.card_eq

theorem edgeCount_eq_of_iso {left right : FiniteObject}
    (iso : left.Iso right) : left.edgeCount = right.edgeCount := by
  letI : FinEnum left.Vertex := left.vertices
  letI : DecidableRel left.graph.Adj := left.decideAdj
  letI : FinEnum right.Vertex := right.vertices
  letI : DecidableRel right.graph.Adj := right.decideAdj
  simpa [edgeCount] using iso.card_edgeFinset_eq

@[simp]
theorem degree_eq_of_iso {left right : FiniteObject}
    (iso : left.Iso right) (vertex : left.Vertex) :
    right.degree (iso vertex) = left.degree vertex := by
  letI : FinEnum left.Vertex := left.vertices
  letI : DecidableRel left.graph.Adj := left.decideAdj
  letI : FinEnum right.Vertex := right.vertices
  letI : DecidableRel right.graph.Adj := right.decideAdj
  exact iso.degree_eq vertex

theorem minDegree_eq_of_iso {left right : FiniteObject}
    (iso : left.Iso right) : left.minDegree = right.minDegree := by
  letI : FinEnum left.Vertex := left.vertices
  letI : DecidableRel left.graph.Adj := left.decideAdj
  letI : FinEnum right.Vertex := right.vertices
  letI : DecidableRel right.graph.Adj := right.decideAdj
  simpa [minDegree] using iso.minDegree_eq

theorem maxDegree_eq_of_iso {left right : FiniteObject}
    (iso : left.Iso right) : left.maxDegree = right.maxDegree := by
  letI : FinEnum left.Vertex := left.vertices
  letI : DecidableRel left.graph.Adj := left.decideAdj
  letI : FinEnum right.Vertex := right.vertices
  letI : DecidableRel right.graph.Adj := right.decideAdj
  simpa [maxDegree] using iso.maxDegree_eq

theorem vertexCount_eq_of_isomorphic {left right : FiniteObject}
    (equivalent : left.Isomorphic right) :
    left.vertexCount = right.vertexCount := by
  rcases equivalent with ⟨iso⟩
  exact vertexCount_eq_of_iso iso

theorem edgeCount_eq_of_isomorphic {left right : FiniteObject}
    (equivalent : left.Isomorphic right) :
    left.edgeCount = right.edgeCount := by
  rcases equivalent with ⟨iso⟩
  exact edgeCount_eq_of_iso iso

theorem minDegree_eq_of_isomorphic {left right : FiniteObject}
    (equivalent : left.Isomorphic right) :
    left.minDegree = right.minDegree := by
  rcases equivalent with ⟨iso⟩
  exact minDegree_eq_of_iso iso

theorem maxDegree_eq_of_isomorphic {left right : FiniteObject}
    (equivalent : left.Isomorphic right) :
    left.maxDegree = right.maxDegree := by
  rcases equivalent with ⟨iso⟩
  exact maxDegree_eq_of_iso iso

end FiniteObject

/-- Core semantic equivalence supplied by graph isomorphism.

The caller proves only that its baseline is isomorphism invariant.  Execution
schedules are deliberately absent from that obligation.
-/
def isomorphismEquivalence
    (Baseline : FiniteObject.{u} → Prop)
    (BranchState : FiniteObject.{u} → Type v)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline) :
    Core.SemanticEquivalence (problem Baseline BranchState) where
  equivalent := FiniteObject.Isomorphic
  equivalence := FiniteObject.isomorphic_equivalence
  baseline_iff := baselineInvariant.iff_of_iso

end Hypostructure.Graph
