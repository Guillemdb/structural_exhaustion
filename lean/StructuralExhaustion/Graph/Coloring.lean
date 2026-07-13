import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import StructuralExhaustion.CT1.TargetEncoding
import StructuralExhaustion.Graph.FiniteObject

namespace StructuralExhaustion.Graph.Coloring

open StructuralExhaustion

universe u

/-- Framework problem used by deterministic coloring machines.  Coloring has
no extra baseline assumption; the branch state is intentionally trivial. -/
abbrev problem (V : Type u) : Core.Problem.{u, 0} := FiniteObject.problem V

/-- Canonical branch context for an unconditional finite-graph coloring run. -/
abbrev context {V : Type u} (object : FiniteObject V) :
    Core.BranchContext (problem V) := FiniteObject.context object

/-- Executable proper-coloring predicate on a total color function. -/
def Proper (object : FiniteObject V) {colorCount : Nat}
    (color : V → Fin colorCount) : Prop :=
  ∀ left right, object.graph.Adj left right → color left ≠ color right

/-- Properness is decidable from the object's two explicit finite inputs. -/
def properDecidable (object : FiniteObject V) {colorCount : Nat}
    (color : V → Fin colorCount) : Decidable (Proper object color) :=
  Core.Enumeration.forallDecidable object.input.vertices
    (fun left => ∀ right, object.graph.Adj left right →
      color left ≠ color right)
    (fun left =>
      Core.Enumeration.forallDecidable object.input.vertices
        (fun right => object.graph.Adj left right →
          color left ≠ color right)
        (fun right => by
          letI : DecidableRel object.graph.Adj := object.input.decideAdj
          infer_instance))

/-- Certificate-driven CT1 encoding for Mathlib's public
`SimpleGraph.Colorable` target. -/
def targetEncoding (V : Type u) (colorCount : Nat) :
    CT1.TargetCertificateEncoding (P := problem V)
      (fun object => object.graph.Colorable colorCount) where
  Code := fun object => V → Fin colorCount
  Accepts := fun object color => Proper object color
  encode := by
    intro object target
    rcases target with ⟨coloring⟩
    exact ⟨fun vertex => coloring vertex,
      fun left right adjacent => coloring.valid adjacent⟩
  decode := by
    intro object color accepts
    exact ⟨SimpleGraph.Coloring.mk color
      (fun {_left _right} adjacent => accepts _left _right adjacent)⟩

/-- A proper coloring on an explicit subset of vertices.  The color function
is total only to make deterministic extension executable; `valid` exposes
exactly the colored-subgraph invariant. -/
structure Partial (object : FiniteObject V) (colorCount : Nat)
    (vertices : Finset V) where
  color : V → Fin colorCount
  valid : ∀ {left right}, left ∈ vertices → right ∈ vertices →
    object.graph.Adj left right → color left ≠ color right

namespace Partial

/-- Empty partial coloring for a nonempty palette. -/
def empty (object : FiniteObject V) (colorCount : Nat)
    (positive : 0 < colorCount) : Partial object colorCount ∅ where
  color := fun _vertex => ⟨0, positive⟩
  valid := by simp

/-- Extend a partial coloring by one fresh vertex using a color absent from
all of its already-colored neighbours. -/
def insert (object : FiniteObject V) [DecidableEq V] {colorCount : Nat}
    {vertices : Finset V} (current : Partial object colorCount vertices)
    (vertex : V) (fresh : vertex ∉ vertices) (newColor : Fin colorCount)
    (available : ∀ neighbor, neighbor ∈ vertices →
      object.graph.Adj vertex neighbor →
        newColor ≠ current.color neighbor) :
    Partial object colorCount (insert vertex vertices) := by
  refine {
    color := Function.update current.color vertex newColor
    valid := ?_
  }
  intro left right leftMember rightMember adjacent
  simp only [Finset.mem_insert] at leftMember rightMember
  rcases leftMember with leftEqual | leftOld
  · subst left
    rcases rightMember with rightEqual | rightOld
    · subst right
      exact (object.graph.ne_of_adj adjacent rfl).elim
    · have rightNe : right ≠ vertex := by
        intro equal
        subst right
        exact fresh rightOld
      simpa [Function.update_self, Function.update_of_ne rightNe] using
        available right rightOld adjacent
  · rcases rightMember with rightEqual | rightOld
    · subst right
      have leftNe : left ≠ vertex := by
        intro equal
        subst left
        exact fresh leftOld
      simpa [Function.update_self, Function.update_of_ne leftNe] using
        (available left leftOld adjacent.symm).symm
    · have leftNe : left ≠ vertex := by
        intro equal
        subst left
        exact fresh leftOld
      have rightNe : right ≠ vertex := by
        intro equal
        subst right
        exact fresh rightOld
      simpa [Function.update_of_ne leftNe, Function.update_of_ne rightNe] using
        current.valid leftOld rightOld adjacent

/-- Forget the subset index after proving that every vertex was colored. -/
def toColoring (object : FiniteObject V) {colorCount : Nat}
    {vertices : Finset V} (current : Partial object colorCount vertices)
    (covers : ∀ vertex, vertex ∈ vertices) :
    object.graph.Coloring (Fin colorCount) :=
  SimpleGraph.Coloring.mk current.color fun {left right} adjacent =>
    current.valid (covers left) (covers right) adjacent

end Partial

end StructuralExhaustion.Graph.Coloring
