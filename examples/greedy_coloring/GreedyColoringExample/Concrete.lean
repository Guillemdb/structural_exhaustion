import GreedyColoringExample.Run

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
