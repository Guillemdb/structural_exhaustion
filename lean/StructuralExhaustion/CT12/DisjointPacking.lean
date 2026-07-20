import StructuralExhaustion.Core.FiniteDisjointPacking
import StructuralExhaustion.CT12.ListPeeling

namespace StructuralExhaustion.CT12.DisjointPacking

open StructuralExhaustion

universe uAmbient uBranch uVertex uItem

/-!
# CT12 profile for finite disjoint packings

The core layer selects a maximum family of pairwise-disjoint nonempty
supports.  CT12 receives only that selected list and audits its complete
head/tail peeling schedule.  Thus the executable loop has at most one step
per host vertex and never scans the universe of items or packings.
-/

/-- The reusable static packing contract. -/
abbrev Profile (Vertex : Type uVertex) (Item : Type uItem) :=
  Core.FiniteDisjointPacking.Profile Vertex Item

namespace Profile

variable {Vertex : Type uVertex} {Item : Type uItem}
variable (profile : Profile Vertex Item)

/-- Exact CT12 input whose schedule is the selected maximum packing. -/
noncomputable def input {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    CT12.Input (CT12.ListPeeling.capability P Item) where
  context := context
  load := profile.values.length
  state := CT12.ListPeeling.initialState profile.values

/-- Execute the framework's canonical list-peeling loop on the selected
packing only. -/
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

/-- The CT12 loop performs at most one iteration per selected item. -/
theorem run_iterations_le_values {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    (profile.run context).iterations ≤ profile.values.length :=
  CT12.run_iterations_bounded (CT12.ListPeeling.capability P Item)
    (profile.input context)

/-- The packing audit performs exactly one iteration per selected item. -/
theorem run_iterations_eq_values {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    (profile.run context).iterations = profile.values.length :=
  CT12.ListPeeling.run_iterations_eq_length context profile.values

/-- The representative injection upgrades CT12's native load bound to a
linear host-vertex bound. -/
theorem run_iterations_le_vertices {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    (profile.run context).iterations ≤ profile.vertices.card :=
  (profile.run_iterations_le_values context).trans
    profile.values_length_le_vertices

/-- The typed CT12 trace is linear in the number of host vertices. -/
theorem run_trace_le_vertices {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    (profile.run context).trace.length ≤ 4 * profile.vertices.card + 3 := by
  have native := CT12.run_trace_bounded
    (CT12.ListPeeling.capability P Item) (profile.input context)
  have scaled : 4 * profile.values.length ≤ 4 * profile.vertices.card :=
    Nat.mul_le_mul_left 4 profile.values_length_le_vertices
  exact native.trans (Nat.add_le_add_right scaled 3)

/-- Totality of the exact selected-packing execution. -/
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

/-- The selected-list CT12 audit has a uniform linear primitive-check budget
in the host-vertex count. Applications reuse this certificate instead of
restating the iteration estimate at each packing node. -/
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

/-- Complete reusable CT12 result for a maximum disjoint packing. -/
structure VerifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) : Prop where
  nodup : profile.values.Nodup
  pairwise : profile.values.Pairwise
    (Function.onFun Disjoint profile.support)
  maximum : ∀ other : profile.Packing,
    other.1.card ≤ profile.values.length
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

/-- Maximal-only public view of a selected disjoint packing.  This is the
contract used by proof nodes that need disjointness, saturation, and the
selected-list CT12 audit but do not establish or consume a
maximum-cardinality assertion. -/
structure MaximalVerifiedStage {P : Core.Problem.{uAmbient, uBranch}}
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

/-- Construct the complete stage entirely from the static finite-support
profile and inherited branch context. -/
noncomputable def verifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) : profile.VerifiedStage context where
  nodup := profile.values_nodup
  pairwise := profile.values_pairwise
  maximum := by
    intro other
    rw [profile.values_length]
    exact profile.maximum_spec other
  saturated := profile.values_saturated
  terminal := profile.run_terminal_exhausted context
  iterations_eq_values := profile.run_iterations_eq_values context
  verified := profile.run_verified context
  traceValid := profile.run_trace_valid context
  iterations_le_vertices := profile.run_iterations_le_vertices context
  trace_length_le_vertices := profile.run_trace_le_vertices context
  total := profile.run_total context

/-- Forget only the maximum-cardinality field of a verified packing stage.
All maximality and selected-list execution evidence is retained verbatim. -/
def VerifiedStage.toMaximal {P : Core.Problem.{uAmbient, uBranch}}
    {context : Core.BranchContext P}
    (stage : profile.VerifiedStage context) :
    profile.MaximalVerifiedStage context where
  nodup := stage.nodup
  pairwise := stage.pairwise
  saturated := stage.saturated
  terminal := stage.terminal
  iterations_eq_values := stage.iterations_eq_values
  verified := stage.verified
  traceValid := stage.traceValid
  iterations_le_vertices := stage.iterations_le_vertices
  trace_length_le_vertices := stage.trace_length_le_vertices
  total := stage.total

/-- Framework-owned maximal-only projection of the existing proof-selected
packing.  The internal producer may know maximum cardinality; application
nodes consuming this API cannot access or claim it. -/
noncomputable def maximalVerifiedStage
    {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    profile.MaximalVerifiedStage context :=
  (profile.verifiedStage context).toMaximal

end Profile

end StructuralExhaustion.CT12.DisjointPacking
