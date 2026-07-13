import StructuralExhaustion.Graph.InducedPathPacking

namespace StructuralExhaustion.Graph.MaximumMatching

open StructuralExhaustion

universe u uAmbient uBranch

variable {V : Type u}

/-!
# Maximum matchings from induced-`P₂` packing

An edge is exactly an induced path on two vertices.  The general induced-path
packing profile therefore proof-selects a maximum matching, and CT12 audits
only the selected edge list.  No edge universe or matching powerset is
executed by the CT12 runner.
-/

private theorem two_positive : 0 < 2 := by decide

noncomputable def profile (object : FiniteObject V) :=
  InducedPathPacking.profile object 2 two_positive

abbrev Edge (object : FiniteObject V) :=
  InducedPathPacking.Window object 2

abbrev Matching (object : FiniteObject V) :=
  InducedPathPacking.Packing object 2 two_positive

noncomputable def edges (object : FiniteObject V) : List (Edge object) :=
  InducedPathPacking.windows object 2 two_positive

noncomputable def matchingNumber (object : FiniteObject V) : Nat :=
  InducedPathPacking.packingNumber object 2 two_positive

noncomputable def remainderVertices (object : FiniteObject V) : Finset V :=
  InducedPathPacking.remainderVertices object 2 two_positive

noncomputable def remainder (object : FiniteObject V) :=
  InducedPathPacking.remainder object 2 two_positive

noncomputable def run {P : Core.Problem.{uAmbient, uBranch}}
    (object : FiniteObject V) (context : Core.BranchContext P) :=
  (profile object).run context

theorem run_terminal_exhausted {P : Core.Problem.{uAmbient, uBranch}}
    (object : FiniteObject V) (context : Core.BranchContext P) :
    (run object context).terminal = .exhausted :=
  (profile object).run_terminal_exhausted context

theorem run_iterations_le_vertices {P : Core.Problem.{uAmbient, uBranch}}
    (object : FiniteObject V) (context : Core.BranchContext P) :
    (run object context).iterations ≤ object.input.vertices.card :=
  (profile object).run_iterations_le_vertices context

theorem run_iterations_exact {P : Core.Problem.{uAmbient, uBranch}}
    (object : FiniteObject V) (context : Core.BranchContext P) :
    (run object context).iterations = matchingNumber object :=
  (profile object).run_iterations_eq_values context

theorem run_trace_length_le_vertices {P : Core.Problem.{uAmbient, uBranch}}
    (object : FiniteObject V) (context : Core.BranchContext P) :
    (run object context).trace.length ≤
      4 * object.input.vertices.card + 3 :=
  (profile object).run_trace_le_vertices context

theorem maximum (object : FiniteObject V) (other : Matching object) :
    other.1.card ≤ matchingNumber object :=
  InducedPathPacking.maximum object 2 two_positive other

theorem partition (object : FiniteObject V) :
    (remainderVertices object).card + 2 * matchingNumber object =
      object.input.vertices.card :=
  InducedPathPacking.remainder_partition object 2 two_positive

/-- The unmatched remainder of a maximum matching is edgeless. -/
theorem remainder_no_edges (object : FiniteObject V)
    (left right : {vertex : V // vertex ∈ remainderVertices object}) :
    ¬(remainder object).graph.Adj left right := by
  intro adjacent
  exact InducedPathPacking.remainder_free object 2 two_positive
    (hasInducedPath_two_of_adj adjacent)

abbrev VerifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (object : FiniteObject V) (context : Core.BranchContext P) :=
  InducedPathPacking.VerifiedStage object 2 two_positive context

noncomputable def verifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (object : FiniteObject V) (context : Core.BranchContext P) :
    VerifiedStage object context :=
  InducedPathPacking.verifiedStage object 2 two_positive context

end StructuralExhaustion.Graph.MaximumMatching
