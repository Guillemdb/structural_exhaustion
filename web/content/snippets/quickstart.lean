import Hypostructure.CT1.Automation
import Hypostructure.Core.Problem
import Hypostructure.Routes.Accumulated

namespace HypostructureQuickstart

open Hypostructure

def problem : Core.Problem where
  Ambient := Bool
  Baseline := fun _candidate => True
  BranchState := fun _candidate => Unit

def PublicTarget (candidate : problem.Ambient) : Prop :=
  candidate = true

structure Residual where
  candidates : Core.Finite.Enumeration Bool
  card_le_two : candidates.card <= 2

abbrev Previous := Core.Residual.Ledger Residual

def spec : CT1.Spec Previous where
  Candidate := fun _previous => Bool
  Realizes := fun _previous candidate => PublicTarget candidate

def schedule : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Candidate previous) :=
  (Core.Residual.Query.residual
    (Source := Previous) (Residual := Residual)).map
      fun _previous residual => residual.candidates

def capability : CT1.Capability spec where
  schedule := schedule
  realizesDecidable := fun _previous candidate => Bool.decEq candidate true
  inputSize := fun _previous => 0
  workCoefficient := 2
  workDegree := 0
  workBound := by
    intro previous
    change (Core.Residual.residualOf previous).candidates.card <= 2
    exact (Core.Residual.residualOf previous).card_le_two

def root : Residual where
  candidates := Core.Finite.Enumeration.ofNodupList [false] (by decide)
  card_le_two := by decide

def previous : Previous := Core.Residual.Ledger.initial root

def result : CT1.ExecutionResult spec capability :=
  CT1.execute spec capability previous

def rootQuery : Core.Residual.Query (CT1.Stage spec capability) fun _ => Residual :=
  Core.Residual.Query.residual

theorem queried_root : rootQuery.read result.stage = root := rfl
theorem literal_previous : result.stage.previous = previous := rfl
theorem selected_avoidance : result.terminal = .avoiding := rfl
theorem target_avoided :
    Not (CT1.Target spec previous (capability.scheduleAt previous)) :=
  by
    simpa [CT1.OutcomeClaim, selected_avoidance, literal_previous] using
      result.verified
theorem exact_checks : result.checks = 1 := rfl

/-!
The application now exposes one public route API.  It owns the target
specification, deterministic capability, and semantic discovery profile.
Core owns target execution, provenance, and the sole ledger extension.
-/
namespace PublicRoute

abbrev Source := CT1.Stage spec capability

def targetSpec : Core.Execution.Spec Source where
  Input := fun _source => PUnit
  Outcome := fun _source _input => Nat
  Trace := fun source _input outcome =>
    PLift (outcome = (Core.Residual.residualOf source).candidates.card)
  Sound := fun source _input outcome _trace =>
    outcome = (Core.Residual.residualOf source).candidates.card
  Exhaustive := fun source _input outcome =>
    outcome = (Core.Residual.residualOf source).candidates.card

def targetCapability : Core.Execution.Capability targetSpec where
  reference := fun source _input => ⟨⟨
    (Core.Residual.residualOf source).candidates.card,
    ⟨rfl⟩
  ⟩, 0⟩
  sound := by
    intro source input
    rfl
  exhaustive := by
    intro source input
    rfl
  work := Core.PolynomialCheckBudget.proofOnly
    (Core.Execution.PackedInput targetSpec)
  checks_eq := by
    intro source input
    rfl

def profile : Core.Routing.Profile Source where
  Target := targetSpec
  executor := targetCapability
  Seed := fun _source => PUnit
  Blocked := fun _source => Empty
  discover := fun _source => .enabled PUnit.unit
  targetInput := fun _source _seed => PUnit.unit

def transition : Core.Routing.Transition
    Routes.Registry.ct1ToCt9Accumulated.edge Source :=
  Routes.Accumulated.register
    Routes.Registry.ct1ToCt9Accumulated rfl profile

/-- The application-facing route entry point consumes the literal CT1 stage. -/
def execute (source : Source) : Core.Routing.Stage transition :=
  Routes.Accumulated.advance transition source

end PublicRoute

def routed := PublicRoute.execute result.stage

theorem route_preserves_complete_predecessor :
    routed.previous = result.stage :=
  Routes.Accumulated.advance_previous
    PublicRoute.transition result.stage

theorem route_preserves_root :
    Core.Residual.residualOf routed =
      Core.Residual.residualOf result.stage :=
  Routes.Accumulated.advance_residual
    PublicRoute.transition result.stage

theorem route_provenance :
    routed.added.provenance.recorded =
      Routes.Registry.ct1ToCt9Accumulated.edge :=
  rfl

#print axioms selected_avoidance
#print axioms route_preserves_complete_predecessor

end HypostructureQuickstart
