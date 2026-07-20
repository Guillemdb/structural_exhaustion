import StructuralExhaustion.Core.GreedyDisjointPacking
import StructuralExhaustion.CT12.ListPeeling

namespace StructuralExhaustion.CT12.GreedyDisjointPacking

open StructuralExhaustion

universe uAmbient uBranch uVertex uItem

/-!
# CT12 audit for an ordered maximal disjoint packing

The core profile constructs one deterministic inclusion-maximal family from
an explicit item order.  CT12 sees only that selected list and performs the
usual head/tail peeling audit.  Maximum-cardinality comparison is deliberately
absent from this contract.
-/

abbrev Profile (Vertex : Type uVertex) (Item : Type uItem) :=
  Core.GreedyDisjointPacking.Profile Vertex Item

namespace Profile

variable {Vertex : Type uVertex} {Item : Type uItem}
variable (profile : Profile Vertex Item)

/-- Exact CT12 input whose schedule is the deterministic maximal packing. -/
noncomputable def input {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    CT12.Input (CT12.ListPeeling.capability P Item) where
  context := context
  load := profile.values.length
  state := CT12.ListPeeling.initialState profile.values

/-- Audit only the selected packing list. -/
noncomputable def run {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    CT12.ExecutionResult (CT12.ListPeeling.capability P Item)
      (profile.input context) :=
  CT12.run (CT12.ListPeeling.capability P Item) (profile.input context)

theorem run_terminal_exhausted {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    (profile.run context).terminal = .exhausted :=
  CT12.ListPeeling.run_terminal_exhausted context profile.values

theorem run_verified {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    (profile.run context).outcome.Valid :=
  CT12.run_verified (CT12.ListPeeling.capability P Item)
    (profile.input context)

theorem run_trace_valid {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    CT12.Graph.ValidTrace (CT12.ListPeeling.capability P Item)
      (profile.run context).trace :=
  CT12.run_trace_valid (CT12.ListPeeling.capability P Item)
    (profile.input context)

theorem run_iterations_eq_values {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    (profile.run context).iterations = profile.values.length :=
  CT12.ListPeeling.run_iterations_eq_length context profile.values

theorem run_iterations_le_vertices {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    (profile.run context).iterations ≤ profile.vertices.card := by
  rw [profile.run_iterations_eq_values context]
  exact profile.values_length_le_vertices

theorem run_trace_le_vertices {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    (profile.run context).trace.length ≤ 4 * profile.vertices.card + 3 := by
  have native := CT12.run_trace_bounded
    (CT12.ListPeeling.capability P Item) (profile.input context)
  have scaled : 4 * profile.values.length ≤ 4 * profile.vertices.card :=
    Nat.mul_le_mul_left 4 profile.values_length_le_vertices
  exact native.trans (Nat.add_le_add_right scaled 3)

theorem run_total {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    ∃ result : CT12.ExecutionResult
        (CT12.ListPeeling.capability P Item) (profile.input context),
      result.outcome.Valid ∧
      CT12.Graph.ValidTrace (CT12.ListPeeling.capability P Item)
        result.trace ∧
      result.iterations ≤ profile.vertices.card ∧
      result.trace.length ≤ 4 * profile.vertices.card + 3 := by
  exact ⟨profile.run context, profile.run_verified context,
    profile.run_trace_valid context, profile.run_iterations_le_vertices context,
    profile.run_trace_le_vertices context⟩

/-- Uniform linear budget for the selected-list CT12 audit.  The proof-level
construction of the maximal family is not evaluated by this runner. -/
noncomputable def workBudget {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) : Core.PolynomialCheckBudget Unit where
  size := fun _ => profile.vertices.card
  checks := fun _ => (profile.run context).iterations
  coefficient := 1
  degree := 1
  bounded := by
    intro _input
    simpa using (profile.run_iterations_le_vertices context).trans
      (Nat.le_succ profile.vertices.card)

/-- Complete CT12 result for a deterministic inclusion-maximal packing. -/
structure VerifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) : Prop where
  nodup : profile.values.Nodup
  pairwise : profile.values.Pairwise
    (Function.onFun Disjoint profile.support)
  saturated : ∀ item : Item, ∃ selected ∈ profile.values,
    ¬Disjoint (profile.support item) (profile.support selected)
  terminal : (profile.run context).terminal = .exhausted
  iterations_eq_values :
    (profile.run context).iterations = profile.values.length
  verified : (profile.run context).outcome.Valid
  traceValid : CT12.Graph.ValidTrace
    (CT12.ListPeeling.capability P Item) (profile.run context).trace
  iterations_le_vertices :
    (profile.run context).iterations ≤ profile.vertices.card
  trace_length_le_vertices :
    (profile.run context).trace.length ≤ 4 * profile.vertices.card + 3
  total : ∃ result : CT12.ExecutionResult
      (CT12.ListPeeling.capability P Item) (profile.input context),
    result.outcome.Valid ∧
    CT12.Graph.ValidTrace (CT12.ListPeeling.capability P Item)
      result.trace ∧
    result.iterations ≤ profile.vertices.card ∧
    result.trace.length ≤ 4 * profile.vertices.card + 3

noncomputable def verifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) : profile.VerifiedStage context where
  nodup := profile.values_nodup
  pairwise := profile.values_pairwise
  saturated := profile.values_saturated
  terminal := profile.run_terminal_exhausted context
  iterations_eq_values := profile.run_iterations_eq_values context
  verified := profile.run_verified context
  traceValid := profile.run_trace_valid context
  iterations_le_vertices := profile.run_iterations_le_vertices context
  trace_length_le_vertices := profile.run_trace_le_vertices context
  total := profile.run_total context

end Profile

end StructuralExhaustion.CT12.GreedyDisjointPacking
