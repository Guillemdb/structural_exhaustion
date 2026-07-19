import EvenCycleExample.Run

namespace EvenCycleExample.ConcreteK4

open StructuralExhaustion

/-! Closed executable fixture for the complete CT6→CT9→CT1 pipeline. -/

inductive Vertex where
  | v0 | v1 | v2 | v3
  deriving Repr, DecidableEq

/-- The machine schedule is explicit and independent of Mathlib's unordered
finite-set views. -/
@[implicit_reducible]
def vertices : FinEnum Vertex :=
  FinEnum.ofNodupList [.v0, .v1, .v2, .v3]
    (by intro vertex; cases vertex <;> simp) (by decide)

def graph : SimpleGraph Vertex := ⊤

def input : Graph.FiniteInput graph where
  vertices := vertices
  decideAdj := by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance

instance graphDecidableAdj : DecidableRel graph.Adj := input.decideAdj

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

theorem minimumDegreeThree : Baseline object := by
  change 3 ≤ object.minDegree
  native_decide

def path := (chosenMaximalPath object minimumDegreeThree).2.path

def ct6Execution := (ct6Run object minimumDegreeThree).execution

def ct9Execution := (ct9Run object minimumDegreeThree).execution

def evenCycle := evenCycleCertificate object minimumDegreeThree

def ct1Run := finalCT1Run object minimumDegreeThree

theorem chosen_path_vertices :
    path.vertices = [.v3, .v2, .v1, .v0] := by
  native_decide

theorem endpoint_neighbor_items_exact :
    (endpointNeighborItems object minimumDegreeThree).values =
      [.v0, .v1, .v2] := by
  native_decide

theorem extracted_even_cycle_support :
    evenCycle.walk.support = [.v3, .v2, .v1, .v0, .v3] := by
  native_decide

theorem extracted_even_cycle_length : evenCycle.walk.length = 4 := by
  native_decide

theorem ct6_terminal_activeLedger :
    ct6Execution.terminal = .activeLedger :=
  (ct6Run object minimumDegreeThree).terminal_eq

theorem ct6_trace_exact :
    ct6Execution.trace =
      [.entry, .firstFailureSearch, .activeLedgerTerminal] :=
  (ct6Run object minimumDegreeThree).trace_eq

theorem ct9_terminal_overloaded :
    ct9Execution.terminal = .overloaded :=
  (ct9Run object minimumDegreeThree).terminal_eq

theorem ct9_trace_exact :
    ct9Execution.trace =
      [.entry, .partition, .overload, .overloadedTerminal] :=
  (ct9Run object minimumDegreeThree).trace_eq

theorem ct1_terminal_c1 :
    ct1Run.result.terminal = .c1 :=
  ct1Run.terminal_eq

theorem ct1_trace_exact :
    ct1Run.result.trace =
      [.entry, .equivalenceCertification, .realizationDecision, .c1Terminal] :=
  ct1Run.trace_eq

end EvenCycleExample.ConcreteK4
