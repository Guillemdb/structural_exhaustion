import Erdos64EG.P13SelectedWindowCorridor
import StructuralExhaustion.Core.VariableConditionalFibreProductCost

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Core.FiniteSequentialFiltration

universe u

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
    (window : P13SelectedConnectorWindow ctx) : Type (u + 1) where
  previous : VerifiedP13MultiScaleCurvaturePrefix ctx
  previousExact : previous = node21
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

/-- Paper-faithful negative handoff: classify the exact stored cold window by
its graph geometry and run the existing same-window surplus/corridor route. -/
noncomputable def P13WeightedColdWindow.corridorRoute
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (cold : P13WeightedColdWindow ctx node21) :
    P13SelectedWindowCorridorRoute ctx cold.window :=
  routeSelectedWindowCorridor ctx cold.window

end Erdos64EG.Internal
