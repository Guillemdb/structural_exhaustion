import StructuralExhaustion.Core.FiniteRefinedLedger
import StructuralExhaustion.CT12.Automation
import StructuralExhaustion.CT12.ListPeeling
import StructuralExhaustion.Routes.Accumulated

namespace StructuralExhaustion.CT12.RefinedLedgerCompletion

open StructuralExhaustion

universe uAmbient uBranch uDemand uCandidate uCarrier uSource

/-!
# CT12 finite refined-ledger completion

CT12 audits only the explicit demand schedule.  The semantic choice-versus-
obstruction theorem remains proof-level, so neither all candidate tuples nor
all demand subfamilies are constructed in memory.
-/

abbrev Profile (Demand : Type uDemand) (Carrier : Type uCarrier) :=
  Core.FiniteRefinedLedger.Profile.{uDemand, uCandidate, uCarrier}
    Demand Carrier

namespace Profile

variable {Demand : Type uDemand} {Carrier : Type uCarrier}
variable (profile : Profile.{uDemand, uCandidate, uCarrier} Demand Carrier)

def input {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    CT12.Input (CT12.ListPeeling.capability P Demand) where
  context := context
  load := profile.demands.orderedValues.length
  state := CT12.ListPeeling.initialState profile.demands.orderedValues

/-- Canonical executable target for a refined-ledger completion. -/
noncomputable def executableTarget
    (_profile : Profile.{uDemand, uCandidate, uCarrier} Demand Carrier)
    (P : Core.Problem.{uAmbient, uBranch}) :=
  (CT12.ListPeeling.capability P Demand).executableInterface

/-- Reusable accumulated-transition adapter.  Applications provide only the
source theorem type; the refined ledger owns the inherited context and exact
indexed peeling trigger. -/
noncomputable def transitionAdapter
    {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (Source : Sort uSource) :
    Routes.Accumulated.Adapter Source (profile.executableTarget P) where
  targetContext := fun _source => context
  trigger := fun _source =>
    let input := profile.input context
    { load := input.load, state := input.state }

def run {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    CT12.ExecutionResult (CT12.ListPeeling.capability P Demand)
      (profile.input context) :=
  CT12.run (CT12.ListPeeling.capability P Demand) (profile.input context)

theorem run_terminal_exhausted {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    (profile.run context).terminal = .exhausted :=
  CT12.ListPeeling.run_terminal_exhausted context
    profile.demands.orderedValues

theorem run_iterations_eq_demands {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    (profile.run context).iterations = profile.demands.card := by
  rw [show (profile.run context).iterations =
      profile.demands.orderedValues.length from
    CT12.ListPeeling.run_iterations_eq_length context
      profile.demands.orderedValues]
  exact profile.demands.orderedValues_length

theorem run_trace_le_demands {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    (profile.run context).trace.length ≤ 4 * profile.demands.card + 3 := by
  simpa [run, input] using CT12.run_trace_bounded
    (CT12.ListPeeling.capability P Demand) (profile.input context)

/-- Complete framework result for every finite demand system, including the
empty schedule. -/
structure VerifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) : Prop where
  scheduleNodup : profile.demands.orderedValues.Nodup
  alternative : Nonempty profile.FullChoice ∨ profile.FullObstruction
  minimalAlternative : Nonempty profile.FullChoice ∨
    ∃ selected : List Demand,
      selected.Sublist profile.fullSchedule ∧
        profile.MinimalOverlapObstruction selected
  terminal : (profile.run context).terminal = .exhausted
  iterationsExact : (profile.run context).iterations = profile.demands.card
  traceValid : CT12.Graph.ValidTrace
    (CT12.ListPeeling.capability P Demand) (profile.run context).trace
  traceLinear : (profile.run context).trace.length ≤
    4 * profile.demands.card + 3
  total : ∃ result : CT12.ExecutionResult
      (CT12.ListPeeling.capability P Demand) (profile.input context),
    result.outcome.Valid ∧
    CT12.Graph.ValidTrace (CT12.ListPeeling.capability P Demand) result.trace ∧
    result.iterations ≤ profile.demands.orderedValues.length ∧
    result.trace.length ≤ 4 * profile.demands.orderedValues.length + 3

def verifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) :
    profile.VerifiedStage context where
  scheduleNodup := profile.demands.nodup_orderedValues
  alternative := profile.fullChoice_or_obstruction
  minimalAlternative := profile.fullChoice_or_minimal_obstruction
  terminal := profile.run_terminal_exhausted context
  iterationsExact := profile.run_iterations_eq_demands context
  traceValid := CT12.run_trace_valid
    (CT12.ListPeeling.capability P Demand) (profile.input context)
  traceLinear := profile.run_trace_le_demands context
  total := CT12.run_total
    (CT12.ListPeeling.capability P Demand) (profile.input context)

end Profile

end StructuralExhaustion.CT12.RefinedLedgerCompletion
