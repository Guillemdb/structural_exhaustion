import Mathlib.Tactic
import StructuralExhaustion.CT5.Automation
import StructuralExhaustion.Graph.SurplusPortActivity
import StructuralExhaustion.Routes.Accumulated

namespace StructuralExhaustion.Graph.PortShoulderLedger

open StructuralExhaustion

universe u uLedger

/-!
# CT5 shoulder-pair ledger

Every canonical surplus slot is a local site.  Its sole witness certifies that
deletion criticality makes the selected port endpoint cubic and hence leaves
exactly two non-centre shoulder vertices.  CT5 verifies every site and sums
the exact shoulder count.  The witness universe is one `Unit` per slot; no
vertex subsets, paths, or graphs are generated.
-/

def spec (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V)
    (_deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    CT5.Spec base.problem where
  Site := SurplusPortActivity.ExcessPortSlot object
  Witness := fun _site => Unit
  Active := fun _ctx _site => True
  Supports := fun _ctx site _witness =>
    (SurplusPortActivity.shoulderVertices object site).length = 2
  contribution := fun _ctx site _witness =>
    (SurplusPortActivity.shoulderVertices object site).length

def capability (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    CT5.Capability (spec base object deletionCritical) where
  sites := SurplusPortActivity.portSlots object
  witnesses := fun _site => Core.Enumeration.unit
  activeDecidable := fun _ctx _site => isTrue trivial
  supportsDecidable := by
    intro _ctx site _witness
    change Decidable
      ((SurplusPortActivity.shoulderVertices object site).length = 2)
    infer_instance
  required := fun _ctx => 0
  capacity := fun _ctx => 2 * (SurplusPortActivity.portSlots object).card

def context (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object) :
    CT5.Input base.problem :=
  ⟨object, baseline, ()⟩

def run (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :=
  CT5.run (spec base object deletionCritical)
    (capability base object deletionCritical) (context base object baseline)

theorem supports
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (site : SurplusPortActivity.ExcessPortSlot object) :
    (spec base object deletionCritical).Supports
      (context base object baseline) site () :=
  SurplusPortActivity.shoulderVertices_length object site deletionCritical

theorem noDeficit
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    ∀ site, ¬CT5.DeficitAt (spec base object deletionCritical)
      (context base object baseline) site := by
  intro site deficit
  exact deficit.2 ()
    (supports base object baseline deletionCritical site)

theorem contributionAt_eq_two
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (site : SurplusPortActivity.ExcessPortSlot object) :
    CT5.contributionAt (spec base object deletionCritical)
      (capability base object deletionCritical)
      (context base object baseline) site = 2 := by
  unfold CT5.contributionAt
  simp only [capability]
  split
  · rename_i witness supported
    exact SurplusPortActivity.shoulderVertices_length
      object site deletionCritical
  · rename_i absent searchAbsent
    exact (absent ()
      (supports base object baseline deletionCritical site)).elim

theorem ledgerTotal_eq_twice_slots
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    CT5.ledgerTotal (spec base object deletionCritical)
      (capability base object deletionCritical)
      (context base object baseline) =
        2 * (SurplusPortActivity.portSlots object).card := by
  unfold CT5.ledgerTotal
  simp_rw [contributionAt_eq_two base object baseline deletionCritical]
  have foldTwo : ∀ (values : List
      (SurplusPortActivity.ExcessPortSlot object)) (initial : Nat),
      values.foldl (fun total _site => total + 2) initial =
        initial + 2 * values.length := by
    intro values
    induction values with
    | nil => intro initial; simp
    | cons head tail ih =>
        intro initial
        rw [List.foldl_cons, ih]
        simp
        omega
  change (SurplusPortActivity.portSlots object).orderedValues.foldl
      (fun total _site => total + 2) 0 =
    2 * (SurplusPortActivity.portSlots object).card
  rw [foldTwo]
  simp only [zero_add]
  congr 1
  simp [FinEnum.orderedValues, FinEnum.toList]

theorem analyzeDeficit_clear
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    ∃ state,
      CT5.analyzeDeficit (spec base object deletionCritical)
        (capability base object deletionCritical)
        (context base object baseline) = .clear state := by
  cases equation : CT5.analyzeDeficit (spec base object deletionCritical)
      (capability base object deletionCritical)
      (context base object baseline) with
  | deficit residual =>
      exact (noDeficit base object baseline deletionCritical residual.site
        ⟨residual.active, residual.noWitness⟩).elim
  | clear state => exact ⟨state, rfl⟩

theorem compare_charge
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (state : CT5.DeficitFreeState (spec base object deletionCritical)
      (capability base object deletionCritical)
      (context base object baseline)) :
    ∃ residual,
      CT5.compare (spec base object deletionCritical)
        (capability base object deletionCritical)
        (context base object baseline)
        (CT5.computeLedger (spec base object deletionCritical)
          (capability base object deletionCritical)
          (context base object baseline) state) = .charge residual := by
  cases equation : CT5.compare (spec base object deletionCritical)
      (capability base object deletionCritical)
      (context base object baseline)
      (CT5.computeLedger (spec base object deletionCritical)
        (capability base object deletionCritical)
        (context base object baseline) state) with
  | closes certificate =>
      have impossible :
          2 * (SurplusPortActivity.portSlots object).card < 0 := by
        simpa [capability, context] using certificate.capacity_lt_required
      omega
  | charge residual => exact ⟨residual, rfl⟩
  | aggregate residual =>
      have totalEq : residual.ledger.total =
          2 * (SurplusPortActivity.portSlots object).card := by
        rw [residual.ledger.computed]
        exact ledgerTotal_eq_twice_slots
          base object baseline deletionCritical
      have tooLarge :
          2 * (SurplusPortActivity.portSlots object).card <
            residual.ledger.total := by
        simpa [capability, context] using residual.capacity_lt_total
      omega

theorem run_terminal_charge
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    (run base object baseline deletionCritical).terminal = .charge := by
  obtain ⟨state, clear⟩ :=
    analyzeDeficit_clear base object baseline deletionCritical
  obtain ⟨residual, compared⟩ :=
    compare_charge base object baseline deletionCritical state
  simp [run, CT5.run, CT5.runReference, clear, compared]

theorem run_trace_charge
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    (run base object baseline deletionCritical).trace =
      [.entry, .deficitSearch, .summation, .comparison, .chargeTerminal] := by
  have terminal := run_terminal_charge
    base object baseline deletionCritical
  generalize resultEquation :
    run base object baseline deletionCritical = result at terminal ⊢
  cases result with
  | mk resultTerminal path outcome =>
      dsimp only at terminal
      subst resultTerminal
      exact CT5.Graph.trace_eq_of_path_to_charge _ _ _ path

def checks (object : FiniteObject V) : Nat :=
  2 * (SurplusPortActivity.portSlots object).card + 2

theorem checks_quadratic (object : FiniteObject V) :
    checks object ≤ 2 * object.input.vertices.card ^ 2 + 2 := by
  unfold checks
  have slotsLe := SurplusPortActivity.portSlots_card_le_square object
  omega

structure VerifiedStage
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) : Prop where
  terminal : (run base object baseline deletionCritical).terminal = .charge
  trace : (run base object baseline deletionCritical).trace =
    [.entry, .deficitSearch, .summation, .comparison, .chargeTerminal]
  verified : (run base object baseline deletionCritical).outcome.Valid
  traceValid : CT5.Graph.ValidTrace
    (spec base object deletionCritical)
    (capability base object deletionCritical)
    (context base object baseline)
    (run base object baseline deletionCritical).trace
  ledgerTotal : CT5.ledgerTotal (spec base object deletionCritical)
    (capability base object deletionCritical)
    (context base object baseline) =
      2 * (SurplusPortActivity.portSlots object).card
  total : ∃ result,
    result = run base object baseline deletionCritical ∧ result.outcome.Valid
  polynomial : checks object ≤ 2 * object.input.vertices.card ^ 2 + 2

def verifiedStage
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    VerifiedStage base object baseline deletionCritical where
  terminal := run_terminal_charge base object baseline deletionCritical
  trace := run_trace_charge base object baseline deletionCritical
  verified := CT5.run_verified _ _ _
  traceValid := CT5.run_trace_valid _ _ _
  ledgerTotal := ledgerTotal_eq_twice_slots
    base object baseline deletionCritical
  total := ⟨_, rfl, CT5.run_verified _ _ _⟩
  polynomial := checks_quadratic object

/- The CT7-to-CT5 accumulated transition selects only CT5's mathematical
context.  The framework retains the complete CT7 ledger and invokes the public
CT5 executable interface. -/
def accumulatedAdapter
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger} :
    Routes.Accumulated.Adapter Ledger
      (capability base object deletionCritical).executableInterface where
  targetContext := fun _ledger => context base object baseline
  trigger := fun _ledger => ()

def transitionStage
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (source : Core.Routing.ResidualStage .ct7 Ledger) :=
  Routes.Accumulated.advance
    (capability base object deletionCritical).executableInterface
    (accumulatedAdapter base object baseline deletionCritical)
    id source

abbrev TransitionLedger
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (source : Core.Routing.ResidualStage .ct7 Ledger) :=
  ((Routes.Accumulated.transition (sourceTactic := .ct7)
    (capability base object deletionCritical).executableInterface
    (accumulatedAdapter base object baseline deletionCritical)).onLedger id
      ).EnabledStage source

abbrev AccumulatedLedger
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (source : Core.Routing.ResidualStage .ct7 Ledger) :=
  Core.Routing.LedgerExtension
    (TransitionLedger base object baseline deletionCritical source)
    (fun _execution => VerifiedStage base object baseline deletionCritical)

/- Complete CT5 ledger: literal CT7 predecessor, public CT5 execution, and
the graph theorem identifying its charge terminal and exact shoulder total. -/
def accumulatedLedgerStage
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {Ledger : Sort uLedger}
    (source : Core.Routing.ResidualStage .ct7 Ledger) :
    Core.Routing.ResidualStage .ct5
      (AccumulatedLedger base object baseline deletionCritical source) :=
  (transitionStage base object baseline deletionCritical source
    ).extend
      (verifiedStage base object baseline deletionCritical)

end StructuralExhaustion.Graph.PortShoulderLedger
