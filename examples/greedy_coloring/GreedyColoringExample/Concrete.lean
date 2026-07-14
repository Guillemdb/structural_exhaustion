import GreedyColoringExample.Run
import StructuralExhaustion.Graph.DegeneracyPeeling

namespace GreedyColoringExample.ConcreteK4

open StructuralExhaustion

/-! A tight fixture: `K₄` has maximum degree three, and the deterministic
framework run uses all four colors. -/

abbrev Vertex := Fin 4

@[implicit_reducible]
def vertices : FinEnum Vertex := inferInstance

def graph : SimpleGraph Vertex := ⊤

def input : Graph.FiniteInput graph where
  vertices := vertices
  decideAdj := by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

def generatedColoring := coloring object

def peelingExecution := ct12Run object

def validationRun := ct1Run object

/-- The final one-vertex step exposes CT4 independently of the surrounding
fold, so the fixture pins its exact terminal as well. -/
def emptyPartial : Graph.Coloring.Partial object 4
    (Graph.EliminationOrder.verticesFinset object []) :=
  Graph.Coloring.Partial.empty object 4 (by decide)

def finalStepExecution :=
  Graph.GreedyColoring.stepRun object 3 (3 : Vertex) [] emptyPartial

theorem maxDegree_exact : object.maxDegree = 3 := by
  native_decide

theorem coloring_values :
    [generatedColoring 0, generatedColoring 1,
      generatedColoring 2, generatedColoring 3] = [3, 2, 1, 0] := by
  native_decide

theorem coloring_is_proper {left right : Vertex}
    (adjacent : graph.Adj left right) :
    generatedColoring left ≠ generatedColoring right :=
  generatedColoring.valid adjacent

theorem ct12_terminal_exhausted :
    peelingExecution.terminal = .exhausted :=
  Graph.GreedyColoring.peeling_terminal_exhausted object

theorem ct12_iterations_exact : peelingExecution.iterations = 4 := by
  native_decide

theorem ct4_terminal_missing : finalStepExecution.terminal = .missing :=
  Graph.GreedyColoring.step_terminal_missing object 3 (3 : Vertex) []
    emptyPartial (by decide)

theorem ct4_trace_exact :
    finalStepExecution.trace =
      [.entry, .assignment, .availability, .missingTerminal] := by
  native_decide

theorem ct1_terminal_c1 : validationRun.result.terminal = .c1 :=
  validationRun.terminal_eq

theorem ct1_trace_exact :
    validationRun.result.trace =
      [.entry, .equivalenceCertification, .realizationDecision, .c1Terminal] :=
  validationRun.trace_eq

end GreedyColoringExample.ConcreteK4

namespace GreedyColoringExample.DegeneracyTriangle

open StructuralExhaustion

/-! The textbook triangle independently instantiates the same graph-owned
degeneracy certificate and exact CT12 runner used by the Erdős sparse-envelope
stage. -/

abbrev Vertex := Fin 3

def graph : SimpleGraph Vertex := ⊤

def input : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

theorem vertexCount : object.input.vertices.card = 3 := by
  decide

theorem coreFree : object.InternalMinDegreeFree 3 :=
  object.internalMinDegreeFree_of_vertexCount_le (by decide) (by
    rw [vertexCount])

noncomputable def profile : Graph.DegeneracyPeeling.Profile object 2 where
  free := by simpa using coreFree

noncomputable def execution :=
  profile.run (Graph.FiniteObject.context object)

theorem terminal_exhausted : execution.terminal = .exhausted :=
  (profile.verifiedStage (Graph.FiniteObject.context object)).terminal

theorem trace_exact : execution.trace =
    CT12.ListPeeling.expectedTrace 3 := by
  unfold execution
  change (profile.certificate.run
    (Graph.FiniteObject.context object)).trace = _
  simpa [vertexCount] using
    (profile.verifiedStage (Graph.FiniteObject.context object)).trace

theorem trace_valid :
    CT12.Graph.ValidTrace
      (CT12.ListPeeling.capability (Graph.FiniteObject.problem Vertex) Vertex)
      execution.trace :=
  (profile.verifiedStage (Graph.FiniteObject.context object)).traceValid

theorem iterations_exact : execution.iterations = 3 := by
  unfold execution
  change (profile.certificate.run
    (Graph.FiniteObject.context object)).iterations = _
  simpa [vertexCount] using
    (profile.verifiedStage (Graph.FiniteObject.context object)).linearWork

theorem total :
    ∃ result, result = execution ∧ result.outcome.Valid ∧
      CT12.Graph.ValidTrace
        (CT12.ListPeeling.capability (Graph.FiniteObject.problem Vertex) Vertex)
        result.trace ∧
      result.iterations ≤ 3 := by
  unfold execution
  change ∃ result,
    result = profile.certificate.run (Graph.FiniteObject.context object) ∧
      result.outcome.Valid ∧
      CT12.Graph.ValidTrace
        (CT12.ListPeeling.capability (Graph.FiniteObject.problem Vertex) Vertex)
        result.trace ∧ result.iterations ≤ 3
  simpa [vertexCount] using
    (profile.verifiedStage (Graph.FiniteObject.context object)).total

theorem linear_budget :
    (profile.budget (Graph.FiniteObject.context object)).checks () ≤
      (profile.budget (Graph.FiniteObject.context object)).coefficient *
        ((profile.budget (Graph.FiniteObject.context object)).size () + 1) ^
          (profile.budget (Graph.FiniteObject.context object)).degree :=
  (profile.budget (Graph.FiniteObject.context object)).bounded ()

theorem sharp_edge_bound : object.edgeCount ≤ 2 * 3 - 3 := by
  simpa [vertexCount] using
    profile.edgeCount_le_two_mul_vertexCount_sub_three (by
      rw [vertexCount]
      decide)

end GreedyColoringExample.DegeneracyTriangle
