import Mathlib.Tactic
import StructuralExhaustion.CT5.Automation
import StructuralExhaustion.Graph.HighCenterPort

namespace StructuralExhaustion.Graph.FanClosedPort

open StructuralExhaustion

universe u

/-!
# CT5 fan-closed compatible-port profile

The graph layer owns the exact local carrier semantics.  A caller supplies
only its window side, remainder side, and assigned-incidence predicate.  Fan
closure is then derived from membership and four literal assignment facts; it
is never accepted as an author certificate.

The CT5 universe has exactly four sites (two ports times two shoulders) and
one `Unit` witness at every site.  Thus the executable audit performs ten
primitive checks and does not enumerate vertices, paths, graphs, or subsets.
-/

/-- An oriented local incidence carrier, from a cubic port endpoint to one of
its two non-centre neighbours. -/
abbrev LocalCarrier (V : Type u) := V × V

/-- Problem data needed to interpret local fan incidences.  The disjointness
of the window and remainder sides is semantic input; closure conclusions are
not fields of this profile. -/
structure FanWindowProfile (V : Type u) where
  WindowSide : V → Prop
  RemainderSide : V → Prop
  Assigned : LocalCarrier V → Prop
  windowDecidable : ∀ vertex, Decidable (WindowSide vertex)
  remainderDecidable : ∀ vertex, Decidable (RemainderSide vertex)
  assignedDecidable : ∀ carrier, Decidable (Assigned carrier)
  remainder_not_window : ∀ vertex, RemainderSide vertex → ¬WindowSide vertex

inductive IncidenceKind where
  | window
  | nonWindow
  deriving Repr, DecidableEq

inductive SupportType where
  | windowSupported
  | mixedSupported
  | internalSupported
  deriving Repr, DecidableEq

variable {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
variable {object : FiniteObject V} {baseline : base.problem.Baseline object}
variable {center : V} (centerHigh : 4 ≤ object.degree center)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)

abbrev OpenPort :=
  HighCenterPort.OpenPort object center centerHigh deletionCritical

/-- Select one of the two literal non-centre neighbours. -/
def shoulder (port : OpenPort centerHigh deletionCritical) (side : Bool) : V :=
  if side then
    HighCenterPort.secondShoulder object center centerHigh deletionCritical port.1
  else
    HighCenterPort.firstShoulder object center centerHigh deletionCritical port.1

/-- The actual oriented graph incidence used by the Type-B ledger. -/
def carrier (port : OpenPort centerHigh deletionCritical) (side : Bool) :
    LocalCarrier V :=
  (HighCenterPort.endpoint object center port.1,
    shoulder centerHigh deletionCritical port side)

theorem carrier_adjacent (port : OpenPort centerHigh deletionCritical)
    (side : Bool) : object.graph.Adj (carrier centerHigh deletionCritical port side).1
      (carrier centerHigh deletionCritical port side).2 := by
  cases side
  · simpa [carrier, shoulder] using
      (HighCenterPort.firstShoulder_adjacent_endpoint object center centerHigh
        deletionCritical port.1).symm
  · simpa [carrier, shoulder] using
      (HighCenterPort.secondShoulder_adjacent_endpoint object center centerHigh
        deletionCritical port.1).symm

def incidenceKind (profile : FanWindowProfile V)
    (port : OpenPort centerHigh deletionCritical) (side : Bool) : IncidenceKind :=
  @ite IncidenceKind
    (profile.WindowSide (shoulder centerHigh deletionCritical port side))
    (profile.windowDecidable (shoulder centerHigh deletionCritical port side))
    .window .nonWindow

theorem incidenceKind_exact (profile : FanWindowProfile V)
    (port : OpenPort centerHigh deletionCritical) (side : Bool) :
    (incidenceKind centerHigh deletionCritical profile port side = .window ↔
      profile.WindowSide (shoulder centerHigh deletionCritical port side)) ∧
    (incidenceKind centerHigh deletionCritical profile port side = .nonWindow ↔
      ¬profile.WindowSide (shoulder centerHigh deletionCritical port side)) := by
  unfold incidenceKind
  split <;> simp_all

def supportType (profile : FanWindowProfile V)
    (port : OpenPort centerHigh deletionCritical) : SupportType :=
  match incidenceKind centerHigh deletionCritical profile port false,
      incidenceKind centerHigh deletionCritical profile port true with
  | .window, .window => .windowSupported
  | .nonWindow, .nonWindow => .internalSupported
  | _, _ => .mixedSupported

/-- Exact fan-closure predicate from the manuscript.  Its classification
clause is derived by `incidenceKind_exact`, rather than supplied separately. -/
def FanClosed (profile : FanWindowProfile V)
    (port : OpenPort centerHigh deletionCritical) : Prop :=
  profile.RemainderSide (HighCenterPort.endpoint object center port.1) ∧
    ∀ side, profile.Assigned (carrier centerHigh deletionCritical port side)

/-- The four hypotheses furnished by an assigned compatible-pair entry. -/
structure AssignedPair (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical) : Prop where
  firstRemainder : profile.RemainderSide
    (HighCenterPort.endpoint object center first.1)
  secondRemainder : profile.RemainderSide
    (HighCenterPort.endpoint object center second.1)
  firstAssigned : ∀ side,
    profile.Assigned (carrier centerHigh deletionCritical first side)
  secondAssigned : ∀ side,
    profile.Assigned (carrier centerHigh deletionCritical second side)

/-- Pair input matching the manuscript's local lemma. -/
structure CompatiblePair
    (first second : OpenPort centerHigh deletionCritical) : Prop where
  distinct : first ≠ second
  compatible : HighCenterPort.FanCompatible object center first.1 second.1

theorem first_fanClosed (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical)
    (assigned : AssignedPair centerHigh deletionCritical profile first second) :
    FanClosed centerHigh deletionCritical profile first :=
  ⟨assigned.firstRemainder, assigned.firstAssigned⟩

theorem second_fanClosed (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical)
    (assigned : AssignedPair centerHigh deletionCritical profile first second) :
    FanClosed centerHigh deletionCritical profile second :=
  ⟨assigned.secondRemainder, assigned.secondAssigned⟩

theorem endpoint_ne (first second : OpenPort centerHigh deletionCritical)
    (pair : CompatiblePair centerHigh deletionCritical first second) :
    HighCenterPort.endpoint object center first.1 ≠
      HighCenterPort.endpoint object center second.1 := by
  intro equal
  apply pair.distinct
  apply Subtype.ext
  exact HighCenterPort.endpoint_injective object center equal

theorem shoulders_ne (port : OpenPort centerHigh deletionCritical) :
    shoulder centerHigh deletionCritical port false ≠
      shoulder centerHigh deletionCritical port true := by
  simpa [shoulder] using
    HighCenterPort.firstShoulder_ne_secondShoulder object center centerHigh
      deletionCritical port.1

/-- The exact four-carrier local B1 entry. -/
def carriers (first second : OpenPort centerHigh deletionCritical) :
    List (LocalCarrier V) :=
  [carrier centerHigh deletionCritical first false,
    carrier centerHigh deletionCritical first true,
    carrier centerHigh deletionCritical second false,
    carrier centerHigh deletionCritical second true]

theorem carriers_nodup (first second : OpenPort centerHigh deletionCritical)
    (pair : CompatiblePair centerHigh deletionCritical first second) :
    (carriers centerHigh deletionCritical first second).Nodup := by
  have endpoints := endpoint_ne centerHigh deletionCritical first second pair
  have firstShoulders := shoulders_ne centerHigh deletionCritical first
  have secondShoulders := shoulders_ne centerHigh deletionCritical second
  simp [carriers, carrier, Prod.ext_iff, endpoints, firstShoulders,
    secondShoulders]

/-! ## Exact four-site CT5 ledger -/

abbrev Site := Bool × Bool

@[implicit_reducible]
def sites : FinEnum Site :=
  Core.Enumeration.prod Core.Enumeration.bool Core.Enumeration.bool

def selectedPort (first second : OpenPort centerHigh deletionCritical)
    (site : Site) : OpenPort centerHigh deletionCritical :=
  if site.1 then second else first

def selectedCarrier (first second : OpenPort centerHigh deletionCritical)
    (site : Site) : LocalCarrier V :=
  carrier centerHigh deletionCritical
    (selectedPort centerHigh deletionCritical first second site) site.2

def spec (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical) : CT5.Spec base.problem where
  Site := Site
  Witness := fun _site => Unit
  Active := fun _ctx _site => True
  Supports := fun _ctx site _unit =>
    profile.Assigned (selectedCarrier centerHigh deletionCritical first second site)
  contribution := fun _ctx _site _unit => 1

def capability (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical) :
    CT5.Capability (spec (base := base) centerHigh deletionCritical profile first second) where
  sites := sites
  witnesses := fun _site => Core.Enumeration.unit
  activeDecidable := fun _ctx _site => isTrue trivial
  supportsDecidable := fun _ctx site _unit =>
    profile.assignedDecidable
      (selectedCarrier centerHigh deletionCritical first second site)
  required := fun _ctx => 0
  capacity := fun _ctx => 4

def input (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object) :
    CT5.Input base.problem := ⟨object, baseline, ()⟩

def run (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical) :=
  CT5.run (spec (base := base) centerHigh deletionCritical profile first second)
    (capability (base := base) centerHigh deletionCritical profile first second)
    (input base object baseline)

theorem sites_card : sites.card = 4 := by decide

theorem selected_assigned (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical)
    (assigned : AssignedPair centerHigh deletionCritical profile first second)
    (site : Site) :
    profile.Assigned
      (selectedCarrier centerHigh deletionCritical first second site) := by
  rcases site with ⟨portSide, shoulderSide⟩
  cases portSide
  · exact assigned.firstAssigned shoulderSide
  · exact assigned.secondAssigned shoulderSide

theorem noDeficit (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical)
    (assigned : AssignedPair centerHigh deletionCritical profile first second) :
    ∀ site, ¬CT5.DeficitAt
      (spec (base := base) centerHigh deletionCritical profile first second)
      (input base object baseline) site := by
  intro site deficit
  exact deficit.2 () (selected_assigned centerHigh deletionCritical profile
    first second assigned site)

theorem contributionAt_eq_one (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical)
    (assigned : AssignedPair centerHigh deletionCritical profile first second)
    (site : Site) :
    CT5.contributionAt (spec (base := base) centerHigh deletionCritical profile first second)
      (capability (base := base) centerHigh deletionCritical profile first second)
      (input base object baseline) site = 1 := by
  unfold CT5.contributionAt
  simp only [capability]
  split
  · rfl
  · rename_i absent searchAbsent
    exact (absent () (selected_assigned centerHigh deletionCritical profile
      first second assigned site)).elim

theorem ledgerTotal_eq_four (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical)
    (assigned : AssignedPair centerHigh deletionCritical profile first second) :
    CT5.ledgerTotal (spec (base := base) centerHigh deletionCritical profile first second)
      (capability (base := base) centerHigh deletionCritical profile first second)
      (input base object baseline) = 4 := by
  unfold CT5.ledgerTotal
  simp_rw [contributionAt_eq_one centerHigh deletionCritical profile first second
    assigned]
  have foldOne : ∀ (values : List Site) (initial : Nat),
      values.foldl (fun total _site => total + 1) initial =
        initial + values.length := by
    intro values
    induction values with
    | nil => intro initial; simp
    | cons head tail ih =>
        intro initial
        rw [List.foldl_cons, ih]
        simp only [List.length_cons]
        omega
  change sites.orderedValues.foldl (fun total _site => total + 1) 0 = 4
  rw [foldOne]
  simpa [FinEnum.orderedValues, FinEnum.toList] using sites_card

theorem analyzeDeficit_clear (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical)
    (assigned : AssignedPair centerHigh deletionCritical profile first second) :
    ∃ state, CT5.analyzeDeficit
      (spec (base := base) centerHigh deletionCritical profile first second)
      (capability (base := base) centerHigh deletionCritical profile first second)
      (input base object baseline) = .clear state := by
  cases equation : CT5.analyzeDeficit
      (spec (base := base) centerHigh deletionCritical profile first second)
      (capability (base := base) centerHigh deletionCritical profile first second)
      (input base object baseline) with
  | deficit residual =>
      exact (noDeficit centerHigh deletionCritical profile first second assigned
        residual.site ⟨residual.active, residual.noWitness⟩).elim
  | clear state => exact ⟨state, rfl⟩

theorem compare_charge (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical)
    (assigned : AssignedPair centerHigh deletionCritical profile first second)
    (state : CT5.DeficitFreeState
      (spec (base := base) centerHigh deletionCritical profile first second)
      (capability (base := base) centerHigh deletionCritical profile first second)
      (input base object baseline)) :
    ∃ residual, CT5.compare
      (spec (base := base) centerHigh deletionCritical profile first second)
      (capability (base := base) centerHigh deletionCritical profile first second)
      (input base object baseline)
      (CT5.computeLedger
        (spec (base := base) centerHigh deletionCritical profile first second)
        (capability (base := base) centerHigh deletionCritical profile first second)
        (input base object baseline) state) = .charge residual := by
  cases equation : CT5.compare
      (spec (base := base) centerHigh deletionCritical profile first second)
      (capability (base := base) centerHigh deletionCritical profile first second)
      (input base object baseline)
      (CT5.computeLedger
        (spec (base := base) centerHigh deletionCritical profile first second)
        (capability (base := base) centerHigh deletionCritical profile first second)
        (input base object baseline) state) with
  | closes certificate =>
      have impossible : 4 < 0 := by
        simpa [capability, input] using certificate.capacity_lt_required
      omega
  | charge residual => exact ⟨residual, rfl⟩
  | aggregate residual =>
      have totalEq : residual.ledger.total = 4 := by
        rw [residual.ledger.computed]
        exact ledgerTotal_eq_four centerHigh deletionCritical profile first second
          assigned
      have tooLarge : 4 < residual.ledger.total := by
        simpa [capability, input] using residual.capacity_lt_total
      omega

theorem run_terminal_charge (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical)
    (assigned : AssignedPair centerHigh deletionCritical profile first second) :
    (run (base := base) (baseline := baseline) centerHigh deletionCritical
      profile first second).terminal = .charge := by
  obtain ⟨state, clear⟩ := analyzeDeficit_clear (base := base)
    (baseline := baseline) centerHigh deletionCritical profile first second assigned
  obtain ⟨residual, compared⟩ := compare_charge (base := base)
    (baseline := baseline) centerHigh deletionCritical profile first second
    assigned state
  simp [run, CT5.run, CT5.runReference, clear, compared]

theorem run_trace_charge (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical)
    (assigned : AssignedPair centerHigh deletionCritical profile first second) :
    (run (base := base) (baseline := baseline) centerHigh deletionCritical
      profile first second).trace =
      [.entry, .deficitSearch, .summation, .comparison, .chargeTerminal] := by
  have terminal := run_terminal_charge (base := base) (baseline := baseline)
    centerHigh deletionCritical profile first second assigned
  generalize resultEquation : run (base := base) (baseline := baseline)
    centerHigh deletionCritical profile first second =
    result at terminal ⊢
  cases result with
  | mk resultTerminal path outcome =>
      dsimp only at terminal
      subst resultTerminal
      exact CT5.Graph.trace_eq_of_path_to_charge _ _ _ path

def checks : Nat := 4 * 1 + 4 + 2

theorem checks_eq_ten : checks = 10 := by decide

structure VerifiedStage (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical)
    (pair : CompatiblePair centerHigh deletionCritical first second)
    (assigned : AssignedPair centerHigh deletionCritical profile first second) : Prop where
  firstClosed : FanClosed centerHigh deletionCritical profile first
  secondClosed : FanClosed centerHigh deletionCritical profile second
  distinctCarriers : (carriers centerHigh deletionCritical first second).Nodup
  ledgerTotal : CT5.ledgerTotal
    (spec (base := base) centerHigh deletionCritical profile first second)
    (capability (base := base) centerHigh deletionCritical profile first second)
    (input base object baseline) = 4
  terminal : (run (base := base) (baseline := baseline) centerHigh
    deletionCritical profile first second).terminal = .charge
  trace : (run (base := base) (baseline := baseline) centerHigh
    deletionCritical profile first second).trace =
    [.entry, .deficitSearch, .summation, .comparison, .chargeTerminal]
  total : ∃ result : CT5.ExecutionResult
      (spec (base := base) centerHigh deletionCritical profile first second)
      (capability (base := base) centerHigh deletionCritical profile first second)
      (input base object baseline),
    result.outcome.Valid ∧ CT5.Graph.ValidTrace
      (spec (base := base) centerHigh deletionCritical profile first second)
      (capability (base := base) centerHigh deletionCritical profile first second)
      (input base object baseline) result.trace
  constantWork : checks ≤ 10

def verifiedStage (profile : FanWindowProfile V)
    (first second : OpenPort centerHigh deletionCritical)
    (pair : CompatiblePair centerHigh deletionCritical first second)
    (assigned : AssignedPair centerHigh deletionCritical profile first second) :
    VerifiedStage (base := base) (baseline := baseline) centerHigh
      deletionCritical profile first second pair assigned where
  firstClosed := first_fanClosed centerHigh deletionCritical profile first second assigned
  secondClosed := second_fanClosed centerHigh deletionCritical profile first second assigned
  distinctCarriers := carriers_nodup centerHigh deletionCritical first second pair
  ledgerTotal := ledgerTotal_eq_four centerHigh deletionCritical profile first second assigned
  terminal := run_terminal_charge centerHigh deletionCritical profile first second assigned
  trace := run_trace_charge centerHigh deletionCritical profile first second assigned
  total := CT5.run_total
    (spec (base := base) centerHigh deletionCritical profile first second)
    (capability (base := base) centerHigh deletionCritical profile first second)
    (input base object baseline)
  constantWork := by simp [checks]

end StructuralExhaustion.Graph.FanClosedPort
