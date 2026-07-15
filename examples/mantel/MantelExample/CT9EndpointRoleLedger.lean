import MantelExample.CT15EdgeResponses
import StructuralExhaustion.CT9.TokenRoleLedger

namespace MantelExample.CT9EndpointRoleLedger

open StructuralExhaustion

/-!
# CT9 transfer: the endpoint--side ledger of `K₂`

The two labelled endpoints of the textbook graph `K₂` are assigned their
literal endpoint token and a two-valued side role.  This external package
executes the same exact token--role CT9 profile used by the Erdős surplus-pair
route.
-/

abbrev Vertex := CT15EdgeResponses.Vertex

@[implicit_reducible]
def endpoints : FinEnum Vertex := CT15EdgeResponses.coordinates

def endpointToken (vertex : Vertex) : Vertex := vertex

def endpointRole (vertex : Vertex) : Bool := decide (vertex = 0)

/-- The transfer exercises only the finite CT9 ledger, so its branch context
contains no additional Mantel hypothesis. -/
def ledgerProblem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ ↦ True
  rank := fun _ ↦ 0
  BranchState := fun _ ↦ Unit

def ledgerContext : Core.BranchContext ledgerProblem :=
  ⟨(), trivial, ()⟩

noncomputable def stage :=
  CT9.TokenRoleLedger.verifiedStage endpoints Core.Enumeration.bool
    endpointToken endpointRole ledgerContext
    endpoints.toOrderedCollection

theorem exact_partition : endpoints.orderedValues.length =
    ((CT9.TokenRoleLedger.labels endpoints Core.Enumeration.bool).orderedValues.map
      fun labelValue ↦
        CT9.fibreCount
          (CT9.TokenRoleLedger.capability
            ledgerProblem Vertex
            endpoints Core.Enumeration.bool endpointToken endpointRole)
          (CT9.TokenRoleLedger.input (capacity := fun _ _ ↦ 0)
            ledgerContext
            endpoints.toOrderedCollection)
          labelValue).sum :=
  stage.exactLedger

theorem execution_verified :
    (CT9.TokenRoleLedger.run endpoints Core.Enumeration.bool
      endpointToken endpointRole ledgerContext
      endpoints.toOrderedCollection).outcome.Valid :=
  stage.verified

/-- The textbook input has two endpoints, so the zero-capacity product
ledger takes the overloaded terminal. -/
theorem terminal_exact :
    (CT9.TokenRoleLedger.run endpoints Core.Enumeration.bool
      endpointToken endpointRole ledgerContext
      endpoints.toOrderedCollection).terminal = .overloaded := by
  apply CT9.TokenRoleLedger.run_terminal_overloaded_of_items_nonempty
  decide

/-- Exact four-node CT9 trace of the same nonempty endpoint ledger. -/
theorem trace_exact :
    (CT9.TokenRoleLedger.run endpoints Core.Enumeration.bool
      endpointToken endpointRole ledgerContext
      endpoints.toOrderedCollection).trace =
      [.entry, .partition, .overload, .overloadedTerminal] := by
  apply CT9.TokenRoleLedger.run_trace_overloaded_of_items_nonempty
  decide

theorem trace_valid :
    CT9.Graph.ValidTrace
      (CT9.TokenRoleLedger.capability
        ledgerProblem Vertex
        endpoints Core.Enumeration.bool endpointToken endpointRole)
      (CT9.TokenRoleLedger.input (capacity := fun _ _ ↦ 0)
        ledgerContext
        endpoints.toOrderedCollection)
      (CT9.TokenRoleLedger.run endpoints Core.Enumeration.bool
        endpointToken endpointRole ledgerContext
        endpoints.toOrderedCollection).trace :=
  stage.traceValid

theorem execution_total : ∃ result,
    result = CT9.TokenRoleLedger.run endpoints Core.Enumeration.bool
      endpointToken endpointRole ledgerContext
      endpoints.toOrderedCollection ∧
    result.outcome.Valid ∧
    CT9.Graph.ValidTrace
      (CT9.TokenRoleLedger.capability
        ledgerProblem Vertex
        endpoints Core.Enumeration.bool endpointToken endpointRole)
      (CT9.TokenRoleLedger.input (capacity := fun _ _ ↦ 0)
        ledgerContext
        endpoints.toOrderedCollection)
      result.trace :=
  stage.total

/-- Two endpoints times two endpoint tokens times two roles. -/
theorem checks_exact :
    CT9.TokenRoleLedger.checks endpoints Core.Enumeration.bool
      endpoints.toOrderedCollection = 8 := by
  decide

end MantelExample.CT9EndpointRoleLedger
