import Hypostructure.Graph.CT12
import Hypostructure.PDE.CT12

/-!
# CT12 axiom-free fixtures

The neutral fixtures cover exhaustion, demand, and tier terminals, including a
three-step decreasing run.  Additional fixtures execute the derived Graph
vertex and PDE observable list profiles.
-/

namespace Hypostructure.Fixtures.CT12

namespace Neutral

inductive Mode where
  | exhaust
  | demand
  | tier
  deriving DecidableEq, Repr

structure Residual where
  mode : Mode
  load : Nat
  deriving DecidableEq, Repr

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def spec : _root_.Hypostructure.CT12.Spec Previous where
  State := fun _previous _load => PUnit
  Peeled := fun {_previous} {_load} _state => PUnit
  DemandResidual := fun _previous => Nat
  TierResidual := fun _previous => Nat
  peel := fun _state => PUnit.unit
  restorations := fun {previous} {load} {_state} _peeled =>
    match (Core.Residual.residualOf previous).mode with
    | .exhaust => {
        first := .continue load PUnit.unit (Nat.lt_succ_self load)
      }
    | .demand => { first := .demand 12 }
    | .tier => { first := .tier 24 }

def capability : _root_.Hypostructure.CT12.Capability spec where
  initial := residualQuery.map fun _previous residual => {
    load := residual.load
    state := PUnit.unit
  }
  inputSize := fun previous => (Core.Residual.residualOf previous).load
  workCoefficient := 5
  workDegree := 1
  workBound := by
    intro previous
    change 4 * (Core.Residual.residualOf previous).load + 1 <=
      5 * ((Core.Residual.residualOf previous).load + 1) ^ 1
    simp only [pow_one]
    omega

def exhaustedPrevious : Previous :=
  Core.Residual.Ledger.initial ⟨.exhaust, 3⟩

def demandPrevious : Previous :=
  Core.Residual.Ledger.initial ⟨.demand, 2⟩

def tierPrevious : Previous :=
  Core.Residual.Ledger.initial ⟨.tier, 4⟩

def exhaustedRun :=
  _root_.Hypostructure.CT12.execute spec capability exhaustedPrevious

def demandRun :=
  _root_.Hypostructure.CT12.execute spec capability demandPrevious

def tierRun :=
  _root_.Hypostructure.CT12.execute spec capability tierPrevious

private theorem exhaustLoop_terminal (load : Nat) :
    (_root_.Hypostructure.CT12.runLoop spec exhaustedPrevious load
      PUnit.unit).terminal = .exhausted := by
  induction load with
  | zero => rw [_root_.Hypostructure.CT12.runLoop]
  | succ load induction =>
      rw [_root_.Hypostructure.CT12.runLoop]
      simp only [_root_.Hypostructure.CT12.inspect, spec,
        exhaustedPrevious,
        Core.Residual.Ledger.residualOf_initial,
        _root_.Hypostructure.CT12.RestorationOptions.selected]
      exact induction

private theorem exhaustLoop_iterations (load : Nat) :
    (_root_.Hypostructure.CT12.runLoop spec exhaustedPrevious load
      PUnit.unit).trace.iterations = load := by
  induction load with
  | zero =>
      rw [_root_.Hypostructure.CT12.runLoop]
      rfl
  | succ load induction =>
      rw [_root_.Hypostructure.CT12.runLoop]
      simp only [_root_.Hypostructure.CT12.inspect, spec,
        exhaustedPrevious,
        Core.Residual.Ledger.residualOf_initial,
        _root_.Hypostructure.CT12.RestorationOptions.selected,
        _root_.Hypostructure.CT12.LoopTrace.iterations]
      change (_root_.Hypostructure.CT12.runLoop spec exhaustedPrevious load
        PUnit.unit).trace.iterations + 1 = load + 1
      rw [induction]

private theorem exhaustLoop_checks (load : Nat) :
    (_root_.Hypostructure.CT12.runLoop spec exhaustedPrevious load
      PUnit.unit).trace.checks = 4 * load + 1 := by
  induction load with
  | zero =>
      rw [_root_.Hypostructure.CT12.runLoop]
      rfl
  | succ load induction =>
      rw [_root_.Hypostructure.CT12.runLoop]
      simp only [_root_.Hypostructure.CT12.inspect, spec,
        exhaustedPrevious,
        Core.Residual.Ledger.residualOf_initial,
        _root_.Hypostructure.CT12.RestorationOptions.selected,
        _root_.Hypostructure.CT12.LoopTrace.checks]
      change (_root_.Hypostructure.CT12.runLoop spec exhaustedPrevious load
        PUnit.unit).trace.checks + 4 = 4 * (load + 1) + 1
      rw [induction]
      omega

private theorem exhaustLoop_nodes (load : Nat) :
    (_root_.Hypostructure.CT12.runLoop spec exhaustedPrevious load
      PUnit.unit).trace.nodes =
      _root_.Hypostructure.CT12.ListPeeling.expectedLoopTrace load := by
  induction load with
  | zero =>
      rw [_root_.Hypostructure.CT12.runLoop]
      rfl
  | succ load induction =>
      rw [_root_.Hypostructure.CT12.runLoop]
      simp only [_root_.Hypostructure.CT12.inspect, spec,
        exhaustedPrevious,
        Core.Residual.Ledger.residualOf_initial,
        _root_.Hypostructure.CT12.RestorationOptions.selected,
        _root_.Hypostructure.CT12.LoopTrace.nodes]
      change [.saturation, .peel, .restoration, .decrease] ++
          (_root_.Hypostructure.CT12.runLoop spec exhaustedPrevious load
            PUnit.unit).trace.nodes =
        [.saturation, .peel, .restoration, .decrease] ++
          _root_.Hypostructure.CT12.ListPeeling.expectedLoopTrace load
      rw [induction]

private theorem demandLoop_terminal (load : Nat) :
    (_root_.Hypostructure.CT12.runLoop spec demandPrevious (load + 1)
      PUnit.unit).terminal = .demand := by
  rw [_root_.Hypostructure.CT12.runLoop]
  rfl

private theorem demandLoop_iterations (load : Nat) :
    (_root_.Hypostructure.CT12.runLoop spec demandPrevious (load + 1)
      PUnit.unit).trace.iterations = 1 := by
  rw [_root_.Hypostructure.CT12.runLoop]
  rfl

private theorem demandLoop_nodes (load : Nat) :
    (_root_.Hypostructure.CT12.runLoop spec demandPrevious (load + 1)
      PUnit.unit).trace.nodes =
      [.saturation, .peel, .restoration, .demandTerminal] := by
  rw [_root_.Hypostructure.CT12.runLoop]
  rfl

private theorem tierLoop_terminal (load : Nat) :
    (_root_.Hypostructure.CT12.runLoop spec tierPrevious (load + 1)
      PUnit.unit).terminal = .tier := by
  rw [_root_.Hypostructure.CT12.runLoop]
  rfl

private theorem tierLoop_iterations (load : Nat) :
    (_root_.Hypostructure.CT12.runLoop spec tierPrevious (load + 1)
      PUnit.unit).trace.iterations = 1 := by
  rw [_root_.Hypostructure.CT12.runLoop]
  rfl

private theorem tierLoop_nodes (load : Nat) :
    (_root_.Hypostructure.CT12.runLoop spec tierPrevious (load + 1)
      PUnit.unit).trace.nodes =
      [.saturation, .peel, .restoration, .tierTerminal] := by
  rw [_root_.Hypostructure.CT12.runLoop]
  rfl

theorem exhausted_terminal : exhaustedRun.terminal = .exhausted := by
  change (_root_.Hypostructure.CT12.runLoop spec exhaustedPrevious 3
    PUnit.unit).terminal = .exhausted
  exact exhaustLoop_terminal 3

theorem exhausted_iterations : exhaustedRun.iterations = 3 := by
  change (_root_.Hypostructure.CT12.runLoop spec exhaustedPrevious 3
    PUnit.unit).trace.iterations = 3
  exact exhaustLoop_iterations 3

theorem exhausted_checks : exhaustedRun.checks = 13 := by
  change (_root_.Hypostructure.CT12.runLoop spec exhaustedPrevious 3
    PUnit.unit).trace.checks = 13
  simpa using exhaustLoop_checks 3

theorem exhausted_trace : exhaustedRun.traceNodes = [
    .entry,
    .saturation, .peel, .restoration, .decrease,
    .saturation, .peel, .restoration, .decrease,
    .saturation, .peel, .restoration, .decrease,
    .saturation, .exhaustedTerminal
  ] := by
  change .entry ::
      (_root_.Hypostructure.CT12.runLoop spec exhaustedPrevious 3
        PUnit.unit).trace.nodes = _
  rw [exhaustLoop_nodes 3]
  rfl

theorem demand_terminal : demandRun.terminal = .demand := by
  change (_root_.Hypostructure.CT12.runLoop spec demandPrevious 2
    PUnit.unit).terminal = .demand
  exact demandLoop_terminal 1

theorem demand_checks : demandRun.checks = 4 := by
  rw [demandRun.checks_eq_exact, demand_terminal]
  change 4 *
      (_root_.Hypostructure.CT12.runLoop spec demandPrevious 2
        PUnit.unit).trace.iterations = 4
  rw [demandLoop_iterations 1]

theorem demand_trace : demandRun.traceNodes = [
    .entry, .saturation, .peel, .restoration, .demandTerminal
  ] := by
  change .entry ::
      (_root_.Hypostructure.CT12.runLoop spec demandPrevious 2
        PUnit.unit).trace.nodes = _
  rw [demandLoop_nodes 1]

theorem tier_terminal : tierRun.terminal = .tier := by
  change (_root_.Hypostructure.CT12.runLoop spec tierPrevious 4
    PUnit.unit).terminal = .tier
  exact tierLoop_terminal 3

theorem tier_checks : tierRun.checks = 4 := by
  rw [tierRun.checks_eq_exact, tier_terminal]
  change 4 *
      (_root_.Hypostructure.CT12.runLoop spec tierPrevious 4
        PUnit.unit).trace.iterations = 4
  rw [tierLoop_iterations 3]

theorem tier_trace : tierRun.traceNodes = [
    .entry, .saturation, .peel, .restoration, .tierTerminal
  ] := by
  change .entry ::
      (_root_.Hypostructure.CT12.runLoop spec tierPrevious 4
        PUnit.unit).trace.nodes = _
  rw [tierLoop_nodes 3]

theorem exhausted_sound :
    _root_.Hypostructure.CT12.OutcomeClaim exhaustedRun.outcome :=
  exhaustedRun.verified

theorem demand_sound :
    _root_.Hypostructure.CT12.OutcomeClaim demandRun.outcome :=
  demandRun.verified

theorem tier_sound :
    _root_.Hypostructure.CT12.OutcomeClaim tierRun.outcome :=
  tierRun.verified

theorem exhausted_polynomial :
    exhaustedRun.checks <= capability.workCoefficient *
      (capability.inputSize exhaustedPrevious + 1) ^
        capability.workDegree :=
  exhaustedRun.checks_le_polynomial

end Neutral

namespace Lists

def schedule : Core.Finite.Enumeration Nat :=
  Core.Finite.Enumeration.ofNodupList [4, 7, 9] (by decide)

abbrev Previous := Core.Residual.Ledger (Core.Finite.Enumeration Nat)

def previous : Previous := Core.Residual.Ledger.initial schedule

def profile : _root_.Hypostructure.CT12.ListPeeling.Profile Previous where
  Value := fun _previous => Nat
  schedule := Core.Residual.Query.residual

def result :=
  _root_.Hypostructure.CT12.ListPeeling.run profile previous

theorem schedule_card : schedule.card = 3 := by
  rfl

theorem terminal : result.terminal = .exhausted :=
  _root_.Hypostructure.CT12.ListPeeling.run_terminal_exhausted profile previous

theorem iterations : result.iterations = 3 := by
  calc
    result.iterations = schedule.card :=
      _root_.Hypostructure.CT12.ListPeeling.run_iterations_eq_card
        profile previous
    _ = 3 := schedule_card

theorem checks : result.checks = 13 := by
  calc
    result.checks = 4 * schedule.card + 1 :=
      _root_.Hypostructure.CT12.ListPeeling.run_checks_eq profile previous
    _ = 13 := by rw [schedule_card]

theorem trace : result.traceNodes =
    _root_.Hypostructure.CT12.ListPeeling.expectedTrace 3 := by
  calc
    result.traceNodes =
        _root_.Hypostructure.CT12.ListPeeling.expectedTrace schedule.card :=
      _root_.Hypostructure.CT12.ListPeeling.run_trace_eq_expected
        profile previous
    _ = _root_.Hypostructure.CT12.ListPeeling.expectedTrace 3 := by
      rw [schedule_card]

end Lists

namespace GraphVertices

abbrev object : Graph.FiniteObject where
  Vertex := Fin 3
  graph := (⊥ : SimpleGraph (Fin 3))
  vertices := inferInstance
  decideAdj := inferInstance

abbrev Previous := Core.Residual.Ledger Graph.FiniteObject

def previous : Previous := Core.Residual.Ledger.initial object

def objectQuery : Core.Residual.Query Previous fun _previous =>
    Graph.FiniteObject :=
  Core.Residual.Query.residual

def profile := Graph.CT12.vertexPeelingProfile objectQuery

def result := Graph.CT12.peelVertices objectQuery previous

theorem schedule_card : (profile.schedule.read previous).card = 3 := by
  change (Core.Finite.Enumeration.ofFinEnum
    (inferInstance : FinEnum (Fin 3))).card = 3
  rw [Core.Finite.Enumeration.card_ofFinEnum]
  simp [FinEnum.card_eq_fintypeCard]

theorem terminal : result.terminal = .exhausted :=
  _root_.Hypostructure.CT12.ListPeeling.run_terminal_exhausted
    profile previous

theorem iterations : result.iterations = 3 := by
  calc
    result.iterations = (profile.schedule.read previous).card :=
      _root_.Hypostructure.CT12.ListPeeling.run_iterations_eq_card
        profile previous
    _ = 3 := schedule_card

end GraphVertices

namespace PDEObservables

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ambient => True
  BranchState := fun _ambient => Unit

def atlas : PDE.LocalAtlas problem where
  Point := Unit
  Window := Unit
  contains := fun _point _window => True
  nested := fun _left _right => True
  nested_refl := fun _window => trivial
  nested_trans := by intros; trivial
  core := id
  core_nested := fun _window => trivial
  LocalObject := fun _window => Unit
  restrict := fun _ambient _window => ()
  restrictLocal := fun _nested _object => ()
  restrict_refl := by intros; rfl
  restrict_trans := by intros; rfl
  restrict_global := by intros; rfl

def equation : PDE.RepresentedEquation problem atlas where
  EquationData := fun _window _object => Unit
  satisfies := fun _data => True
  restrictEquation := by intros; exact ()
  restrict_satisfies := by intros; trivial

def model : PDE.LocalModel where
  problem := problem
  atlas := atlas
  equation := equation

def observables : PDE.ObservableInterface model where
  Index := Fin 3
  Value := fun _index => Unit
  observe := fun _ambient _index => ()
  visible := fun _index _window => True
  localObserve := fun _window _object _index => ()
  localReflect := fun _ambient _window _index _visible => rfl

def schedule : Core.Finite.Enumeration observables.Index :=
  Core.Finite.Enumeration.ofFinEnum (inferInstance : FinEnum (Fin 3))

abbrev Previous :=
  Core.Residual.Ledger (Core.Finite.Enumeration observables.Index)

def previous : Previous := Core.Residual.Ledger.initial schedule

def scheduleQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration observables.Index :=
  Core.Residual.Query.residual

def profile := PDE.CT12.observablePeelingProfile observables scheduleQuery

def result := PDE.CT12.peelObservables observables scheduleQuery previous

theorem schedule_card : (profile.schedule.read previous).card = 3 := by
  change (Core.Finite.Enumeration.ofFinEnum
    (inferInstance : FinEnum (Fin 3))).card = 3
  rw [Core.Finite.Enumeration.card_ofFinEnum]
  simp [FinEnum.card_eq_fintypeCard]

theorem terminal : result.terminal = .exhausted :=
  _root_.Hypostructure.CT12.ListPeeling.run_terminal_exhausted
    profile previous

theorem iterations : result.iterations = 3 := by
  calc
    result.iterations = (profile.schedule.read previous).card :=
      _root_.Hypostructure.CT12.ListPeeling.run_iterations_eq_card
        profile previous
    _ = 3 := schedule_card

end PDEObservables

#print axioms Neutral.exhausted_sound
#print axioms Neutral.demand_sound
#print axioms Neutral.tier_sound
#print axioms _root_.Hypostructure.CT12.run_total
#print axioms _root_.Hypostructure.CT12.loadOrder_wellFounded
#print axioms _root_.Hypostructure.CT12.ListPeeling.run_checks_eq
#print axioms Lists.trace
#print axioms GraphVertices.iterations
#print axioms PDEObservables.iterations

end Hypostructure.Fixtures.CT12
