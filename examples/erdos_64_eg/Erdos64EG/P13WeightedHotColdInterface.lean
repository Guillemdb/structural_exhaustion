import Erdos64EG.P13SelectedWindowCorridor
import StructuralExhaustion.Core.ExactHandoff
import Erdos64EG.P13SequentialEntropyFiltration
import StructuralExhaustion.Core.VariableConditionalFibreProductCost

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Core.FiniteSequentialFiltration

universe u

set_option maxRecDepth 100000

/-!
# Paper-faithful weighted live/cold P13 interface

The manuscript charges the 91 safe/flat ratios by sequential conditional
fibres.  It does not require a Boolean cube.  A live window therefore owns one
complete variable-factor ledger on graph-owned connector tests.  If that exact
package is unavailable, the same selected window is retained as a cold
residual and sent to the geometric surplus/corridor route.
-/

/-- The exact positive package for one selected window.  Coordinates may
repeat a barrier at separated scales; `barrierMultiplicity` records that every
one of the 91 barrier rows occurs equally often. -/
structure P13WeightedLiveWindowPackage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (window : P13SelectedConnectorWindow ctx) : Type (u + 1)
    extends Core.ExactHandoff node21 where
  State : Type u
  Coordinate : Type u
  states : Core.OrderedCollection State
  coordinates : Core.OrderedCollection Coordinate
  barrierIndex : Coordinate → P13BarrierIndex
  separatedScale : Coordinate → Nat
  coordinateKeyInjective : Function.Injective
    (fun coordinate => (barrierIndex coordinate, separatedScale coordinate))
  scaleMultiplicity : Nat
  scaleMultiplicityPositive : 0 < scaleMultiplicity
  scaleLoss : Nat
  scaleCountExact : scaleMultiplicity + scaleLoss =
    Nat.log 2 ctx.G.object.input.vertices.card
  scaleLossBound : scaleLoss ≤ 30
  separatedScaleBound : ∀ coordinate,
    separatedScale coordinate < Nat.log 2 ctx.G.object.input.vertices.card
  barrierMultiplicity : ∀ index,
    (coordinates.values.map barrierIndex).count index = scaleMultiplicity
  connector : State → Coordinate → P13ConnectorSequence ctx
  connectorCodeInjective : Function.Injective
    (fun state => fun coordinate => connector state coordinate)
  accepts : Coordinate → State → Bool
  acceptsSemantic : ∀ coordinate state,
    accepts coordinate state =
      @decide (P13BarrierConnectorValid ctx window (barrierIndex coordinate)
        (connector state coordinate))
        (p13BarrierConnectorValidDecidable ctx window (barrierIndex coordinate)
          (connector state coordinate))
  profile : Core.VariableConditionalFibreProductCost.Profile
  profileExact : profile = {
    State := State
    Coordinate := Coordinate
    states := states
    coordinates := coordinates
    accepts := accepts
    safe := fun coordinate => p13BarrierSafeCount (barrierIndex coordinate)
    flat := fun coordinate => p13BarrierFlatCount (barrierIndex coordinate)
  }
  ledger : CompleteLedger profile.states.values profile.barriers
  finalNonempty : 0 < ledger.finalStates.length

namespace P13WeightedLiveWindowPackage

/-- The safe-product identity is forced by the exact uniform barrier
multiplicity ledger; it is not an author-supplied package field. -/
theorem safeProductExact
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {window : P13SelectedConnectorWindow ctx}
    (package : P13WeightedLiveWindowPackage ctx node21 window) :
    package.profile.safeProduct =
      p13BarrierSafeProduct ^ package.scaleMultiplicity := by
  rw [package.profileExact]
  exact Core.UniformFiniteFibreProduct.mapped_prod_eq_finEnum_prod_pow
    package.coordinates p13BarrierClassification.classes package.barrierIndex
      p13BarrierSafeCount package.scaleMultiplicity package.barrierMultiplicity

/-- The flat-product identity is forced by the same exact uniform barrier
multiplicity ledger. -/
theorem flatProductExact
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {window : P13SelectedConnectorWindow ctx}
    (package : P13WeightedLiveWindowPackage ctx node21 window) :
    package.profile.flatProduct =
      p13BarrierFlatProduct ^ package.scaleMultiplicity := by
  rw [package.profileExact]
  exact Core.UniformFiniteFibreProduct.mapped_prod_eq_finEnum_prod_pow
    package.coordinates p13BarrierClassification.classes package.barrierIndex
      p13BarrierFlatCount package.scaleMultiplicity package.barrierMultiplicity

/-- The exact variable-factor product payment made by one live package. -/
theorem product_le
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {window : P13SelectedConnectorWindow ctx}
    (package : P13WeightedLiveWindowPackage ctx node21 window) :
    package.profile.safeProduct ≤
      package.profile.flatProduct * package.profile.states.values.length := by
  have one_le : 1 ≤ package.ledger.finalStates.length := package.finalNonempty
  have lower : package.profile.safeProduct ≤
      package.profile.safeProduct * package.ledger.finalStates.length := by
    simpa using Nat.mul_le_mul_left package.profile.safeProduct one_le
  exact lower.trans (package.profile.complete_product_le package.ledger)

/-- The executable checker scans only the current local fibre at every
coordinate. -/
theorem checks_local
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {window : P13SelectedConnectorWindow ctx}
    (package : P13WeightedLiveWindowPackage ctx node21 window) :
    package.profile.checks ≤
      package.profile.states.values.length *
        package.profile.coordinates.values.length :=
  package.profile.checks_le_state_mul_coordinate

/-- One complete weighted-live package pays the manuscript's exact 118-bit
rate at every retained separated scale.  This is derived from the audited
node-[21] rate floor, the package's exact repeated products, and its literal
conditional-fibre ledger; it is not a Boolean-realization premise. -/
theorem stateCount_gt_ratePower
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {window : P13SelectedConnectorWindow ctx}
    (package : P13WeightedLiveWindowPackage ctx node21 window) :
    2 ^ (118 * package.scaleMultiplicity) <
      package.profile.states.values.length := by
  have multiplicityNe : package.scaleMultiplicity ≠ 0 :=
    Nat.ne_of_gt package.scaleMultiplicityPositive
  have poweredRate :
      (2 ^ 118 * p13BarrierFlatProduct) ^ package.scaleMultiplicity <
        p13BarrierSafeProduct ^ package.scaleMultiplicity :=
    Nat.pow_lt_pow_left package.previous.rateFloor multiplicityNe
  have productBound := package.product_le
  rw [package.safeProductExact, package.flatProductExact] at productBound
  have chained :
      (2 ^ 118 * p13BarrierFlatProduct) ^ package.scaleMultiplicity <
        p13BarrierFlatProduct ^ package.scaleMultiplicity *
          package.profile.states.values.length :=
    poweredRate.trans_le productBound
  have flatPos : 0 < p13BarrierFlatProduct ^ package.scaleMultiplicity :=
    pow_pos p13Sequential_flatProduct_pos _
  have reshaped :
      p13BarrierFlatProduct ^ package.scaleMultiplicity *
          2 ^ (118 * package.scaleMultiplicity) <
        p13BarrierFlatProduct ^ package.scaleMultiplicity *
          package.profile.states.values.length := by
    calc
      p13BarrierFlatProduct ^ package.scaleMultiplicity *
          2 ^ (118 * package.scaleMultiplicity) =
          (2 ^ 118 * p13BarrierFlatProduct) ^
            package.scaleMultiplicity := by
        rw [pow_mul, mul_pow]
        ac_rfl
      _ < p13BarrierFlatProduct ^ package.scaleMultiplicity *
          package.profile.states.values.length := chained
  exact (Nat.mul_lt_mul_left flatPos).mp reshaped

end P13WeightedLiveWindowPackage

/-- A positive ledger entry owns the weighted package for its exact window. -/
structure P13WeightedHotWindow
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) where
  window : P13SelectedConnectorWindow ctx
  package : P13WeightedLiveWindowPackage ctx node21 window

/-- A negative ledger entry retains the identical selected window and only
the exact failure of the live-package proposition. -/
structure P13WeightedColdWindow
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) where
  window : P13SelectedConnectorWindow ctx
  packageAbsent : ¬Nonempty (P13WeightedLiveWindowPackage ctx node21 window)

/-- Exhaustive paper-level split for one window.  This is a proof split, not a
search through states, assignments, contexts, or graphs. -/
noncomputable def classifyP13WeightedWindow
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (window : P13SelectedConnectorWindow ctx) :
    P13WeightedHotWindow ctx node21 ⊕ P13WeightedColdWindow ctx node21 := by
  by_cases live : Nonempty (P13WeightedLiveWindowPackage ctx node21 window)
  · exact .inl ⟨window, Classical.choice live⟩
  · exact .inr ⟨window, live⟩

/-- Both constructors of the weighted split retain the supplied selected
window definitionally. -/
theorem classifyP13WeightedWindow_window
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (window : P13SelectedConnectorWindow ctx) :
    (match classifyP13WeightedWindow ctx node21 window with
      | .inl hot => hot.window
      | .inr cold => cold.window) = window := by
  classical
  by_cases live : Nonempty (P13WeightedLiveWindowPackage ctx node21 window)
  · simp [classifyP13WeightedWindow, live]
  · simp [classifyP13WeightedWindow, live]

private noncomputable def p13WeightedHotOfList
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    List (P13SelectedConnectorWindow ctx) → List (P13WeightedHotWindow ctx node21)
  | [] => []
  | window :: tail =>
      match classifyP13WeightedWindow ctx node21 window with
      | .inl hot => hot :: p13WeightedHotOfList ctx node21 tail
      | .inr _ => p13WeightedHotOfList ctx node21 tail

private noncomputable def p13WeightedColdOfList
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    List (P13SelectedConnectorWindow ctx) → List (P13WeightedColdWindow ctx node21)
  | [] => []
  | window :: tail =>
      match classifyP13WeightedWindow ctx node21 window with
      | .inl _ => p13WeightedColdOfList ctx node21 tail
      | .inr cold => cold :: p13WeightedColdOfList ctx node21 tail

private theorem p13Weighted_hot_cold_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (windows : List (P13SelectedConnectorWindow ctx)) :
    (p13WeightedHotOfList ctx node21 windows).length +
      (p13WeightedColdOfList ctx node21 windows).length = windows.length := by
  induction windows with
  | nil => rfl
  | cons window tail ih =>
      simp only [p13WeightedHotOfList, p13WeightedColdOfList]
      cases classifyP13WeightedWindow ctx node21 window <;> simp_all <;> omega

private theorem p13WeightedColdOfList_windows_sublist
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (windows : List (P13SelectedConnectorWindow ctx)) :
    List.Sublist
      ((p13WeightedColdOfList ctx node21 windows).map (fun cold => cold.window))
      windows := by
  induction windows with
  | nil => exact .slnil
  | cons window tail ih =>
      simp only [p13WeightedColdOfList]
      cases splitExact : classifyP13WeightedWindow ctx node21 window with
      | inl hot =>
          simpa [splitExact] using List.Sublist.cons window ih
      | inr cold =>
          have retained : cold.window = window := by
            have exactWindow := classifyP13WeightedWindow_window ctx node21 window
            simpa [splitExact] using exactWindow
          simpa [splitExact, retained] using List.Sublist.cons_cons window ih

noncomputable def p13WeightedHotWindows
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    List (P13WeightedHotWindow ctx node21) :=
  p13WeightedHotOfList ctx node21 (p13Windows ctx).attach

noncomputable def p13WeightedColdWindows
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    List (P13WeightedColdWindow ctx node21) :=
  p13WeightedColdOfList ctx node21 (p13Windows ctx).attach

/-- Exact partition of the node-[21] selected packing. -/
theorem p13WeightedHotCount_add_coldCount
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    (p13WeightedHotWindows ctx node21).length +
      (p13WeightedColdWindows ctx node21).length = p13 ctx := by
  rw [p13WeightedHotWindows, p13WeightedColdWindows,
    p13Weighted_hot_cold_length]
  simp only [List.length_attach]
  rfl

/-- Pure finite aggregation behind the manuscript's hot-failure payment.
Once a separately verified semantic producer bounds the contribution of the
exact hot list by `budget`, the exact partition forces the remaining total
demand to be paid by the cold list.  This theorem does not construct or assume
cross-window response independence. -/
theorem p13WeightedHotBudget_total_le_budget_add_cold
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (rate budget : Nat)
    (hotBound : rate * (p13WeightedHotWindows ctx node21).length ≤ budget) :
    rate * p13 ctx ≤
      budget + rate * (p13WeightedColdWindows ctx node21).length := by
  calc
    rate * p13 ctx = rate *
        ((p13WeightedHotWindows ctx node21).length +
          (p13WeightedColdWindows ctx node21).length) := by
      rw [p13WeightedHotCount_add_coldCount]
    _ = rate * (p13WeightedHotWindows ctx node21).length +
        rate * (p13WeightedColdWindows ctx node21).length := by
      rw [Nat.mul_add]
    _ ≤ budget + rate * (p13WeightedColdWindows ctx node21).length :=
      Nat.add_le_add_right hotBound _

/-- Exact unpaid-demand form of the hot/cold payment.  This is the useful
finite precursor of the manuscript's normalized estimate
`C >= (theta - theta_win) n - o(n)`: no division or asymptotic notation is
introduced, and the conclusion is obtained solely from the exact partition
and the separately proved hot budget. -/
theorem p13WeightedHotBudget_shortfall_le_cold
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (rate budget : Nat)
    (hotBound : rate * (p13WeightedHotWindows ctx node21).length <= budget) :
    rate * p13 ctx - budget <=
      rate * (p13WeightedColdWindows ctx node21).length := by
  have payment := p13WeightedHotBudget_total_le_budget_add_cold
    ctx node21 rate budget hotBound
  omega

/-- On a strict total-demand overflow, any valid hot contribution bound forces
an actual cold window.  This is the exact natural-number form of the first
conclusion of `hot failure forces cold mass`; the stronger numerical lower
bound is retained by the preceding payment inequality. -/
theorem p13WeightedHotOverflow_forces_cold_nonempty
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (rate budget : Nat)
    (hotBound : rate * (p13WeightedHotWindows ctx node21).length ≤ budget)
    (overflow : budget < rate * p13 ctx) :
    0 < (p13WeightedColdWindows ctx node21).length := by
  have payment := p13WeightedHotBudget_total_le_budget_add_cold
    ctx node21 rate budget hotBound
  by_contra notPositive
  have coldZero : (p13WeightedColdWindows ctx node21).length = 0 :=
    Nat.eq_zero_of_not_pos notPositive
  simp [coldZero] at payment
  omega

/-- The negative ledger contains no selected window twice.  This is the
provenance fact needed to pay its non-cubic subfamily from the disjoint packing
surplus ledger. -/
theorem p13WeightedColdWindows_window_nodup
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    (p13WeightedColdWindows ctx node21).map (fun cold => cold.window) |>.Nodup := by
  exact (p13WeightedColdOfList_windows_sublist ctx node21
    (p13Windows ctx).attach).nodup
      (inducedP13PackingProfile ctx).values_nodup.attach

/-- Paper-faithful negative handoff: classify the exact stored cold window by
its graph geometry and run the existing same-window surplus/corridor route. -/
noncomputable def P13WeightedColdWindow.corridorRoute
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (cold : P13WeightedColdWindow ctx node21) :
    P13SelectedWindowCorridorRoute ctx cold.window :=
  routeSelectedWindowCorridor ctx cold.window

end Erdos64EG.Internal
