import Erdos64EG.Shared.P13MultiScaleConnectorState
import Erdos64EG.Shared.P13SequentialEntropyFiltration
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
    (node21 : P13BarrierRateCertificate)
    (window : P13SelectedConnectorWindow ctx) : Type (u + 3) where
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
    {node21 : P13BarrierRateCertificate}
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
    {node21 : P13BarrierRateCertificate}
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
    {node21 : P13BarrierRateCertificate}
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
    {node21 : P13BarrierRateCertificate}
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
    {node21 : P13BarrierRateCertificate}
    {window : P13SelectedConnectorWindow ctx}
    (package : P13WeightedLiveWindowPackage ctx node21 window) :
    2 ^ (118 * package.scaleMultiplicity) <
      package.profile.states.values.length := by
  have multiplicityNe : package.scaleMultiplicity ≠ 0 :=
    Nat.ne_of_gt package.scaleMultiplicityPositive
  have poweredRate :
      (2 ^ 118 * p13BarrierFlatProduct) ^ package.scaleMultiplicity <
        p13BarrierSafeProduct ^ package.scaleMultiplicity :=
    Nat.pow_lt_pow_left node21.rateFloor multiplicityNe
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
    (node21 : P13BarrierRateCertificate) where
  window : P13SelectedConnectorWindow ctx
  package : P13WeightedLiveWindowPackage ctx node21 window

end Erdos64EG.Internal
