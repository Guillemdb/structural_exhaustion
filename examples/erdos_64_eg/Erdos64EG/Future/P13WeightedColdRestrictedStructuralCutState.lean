import Erdos64EG.Future.P13WeightedColdRestrictedD4D7State
import Erdos64EG.Future.P13WeightedColdRestrictedPriorPiecePair
import StructuralExhaustion.Core.BoundedListCode
import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Core.FiniteExactStateCorridor
import StructuralExhaustion.Core.FiniteObservedColumn
import StructuralExhaustion.Core.FiniteStructuralCutState

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph


universe u

/-!
# Available-ledger projection of the node-[153] structural cold cut-state

This is the structural state read at one literal restricted-prefix stage.  Its
two active boundary interfaces are the fixed anchor outside endpoint and the
moving prefix endpoint.  Their half-edge endpoint roles are stored separately
from the anchor-window and cyclic-successor-window offsets.  The local tail is
exactly the observed D4--D7 fixed-code lists.

No target-response bit or outside-context response is a field.  Consequently
equal codes feed the later F2 comparison and imply no response equality.

The D6 field is complete only for the supplied produced-prior-support ledger.
Thus this module is reusable internal support, not an unconditional node-[153]
producer, until the missing node-[70], [72], and [73] families and the complete
prior-handoff ledger are supplied by their existing manuscript nodes.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

noncomputable section

abbrev BoundaryRole := Core.FixedTwoBoundaryCutState.BoundaryRole
abbrev CappedDegree := Core.FixedTwoBoundaryCutState.CappedDegree
abbrev WindowOffset := Core.FixedTwoBoundaryCutState.WindowOffset

/-- The two active outside endpoints of the actual prefix cut. -/
noncomputable def activeBoundaryEndpoint (stage : package.Stage) :
    BoundaryRole → ctx.G.Vertex
  | role => Fin.cases package.input.anchor.neighbor
      (fun _ => package.currentAmbientEndpoint stage) role

theorem activeBoundaryEndpoint_zero (stage : package.Stage) :
    package.activeBoundaryEndpoint stage 0 = package.input.anchor.neighbor := by
  rfl

theorem activeBoundaryEndpoint_one (stage : package.Stage) :
    package.activeBoundaryEndpoint stage 1 =
      package.currentAmbientEndpoint stage := by
  rfl

theorem activeBoundaryEndpoint_mem (stage : package.Stage)
    (role : BoundaryRole) :
    package.activeBoundaryEndpoint stage role ∈
      package.boundedActiveInterface stage := by
  refine Fin.cases ?_ (fun index => ?_) role
  · exact (package.mem_boundedActiveInterface_iff_role stage _).2
      ⟨.inr (.inr false), rfl⟩
  · have indexZero : index = 0 := Fin.eq_zero index
    subst indexZero
    exact package.currentAmbientEndpoint_mem_boundedActiveInterface stage

/-- The half-edge identity stored by the finite state is its outside endpoint
role.  Together with `role` and `activeWindowOffset`, this identifies the
oriented active half-edge without storing an ambient vertex. -/
noncomputable def activeHalfEdgeEndpointRole (stage : package.Stage) :
    BoundaryRole → BoundedCarrierRole :=
  fun role => package.d6CarrierRole stage
    (package.activeBoundaryEndpoint stage role)
    (package.activeBoundaryEndpoint_mem stage role)

/-- Literal capped boundary-degree profile of the two active endpoints. -/
noncomputable def activeBoundaryDegree (stage : package.Stage) :
    BoundaryRole → CappedDegree :=
  fun role => Core.FixedTwoBoundaryCutState.capDegree
    (ctx.G.object.degree (package.activeBoundaryEndpoint stage role))

/-- The two original cold-window offsets: anchor and cyclic successor. -/
noncomputable def activeWindowOffset : BoundaryRole → WindowOffset
  | role => if role = 0 then package.input.anchor.offset
      else (InducedPathRestrictedComponentBoundarySchedule.successor
        package.input).offset

theorem activeWindowOffset_zero : package.activeWindowOffset 0 =
    package.input.anchor.offset := by simp [activeWindowOffset]

theorem activeWindowOffset_one : package.activeWindowOffset 1 =
    (InducedPathRestrictedComponentBoundarySchedule.successor
      package.input).offset := by simp [activeWindowOffset]

/-! ## Observed D4 structural code list -/

abbrev FixedD4Code := D4FixedCoordinate

noncomputable def fixedD4Code (stage : package.Stage)
    (coordinate : package.D4Coordinate stage) : FixedD4Code :=
  package.d4FixedCoordinate stage coordinate

theorem fixedD4Code_injective (stage : package.Stage) :
    Function.Injective (package.fixedD4Code stage) := by
  intro left right equal
  exact package.d4FixedCoordinate_injective stage equal

noncomputable def fixedD4Codes (stage : package.Stage) : List FixedD4Code :=
  (package.d4Coordinates stage).orderedValues.map
    (package.fixedD4Code stage)

theorem fixedD4Codes_nodup (stage : package.Stage) :
    (package.fixedD4Codes stage).Nodup :=
  (package.d4Coordinates stage).nodup_orderedValues.map
    (package.fixedD4Code_injective stage)

theorem fixedD4Codes_length_le_alphabet (stage : package.Stage) :
    (package.fixedD4Codes stage).length ≤ Fintype.card FixedD4Code :=
  (package.fixedD4Codes_nodup stage).length_le_card

/-! ## Framework-owned symbolically padded observed columns -/

noncomputable def coldColumns :=
  Core.FiniteObservedColumn.FourEncoding.ofFintype
    FixedD4Code D5Available.FixedD5Code D6DeclaredStructuralCode FixedD7Code

noncomputable abbrev d4Column := coldColumns.d4
noncomputable abbrev d5Column := coldColumns.d5
noncomputable abbrev d6Column := coldColumns.d6
noncomputable abbrev d7Column := coldColumns.d7

abbrev D4ListBound := d4Column.alphabetCard
abbrev D5ListBound := d5Column.alphabetCard
abbrev D6ListBound := d6Column.alphabetCard
abbrev D7ListBound := d7Column.alphabetCard

abbrev D4ListCode := d4Column.Code
abbrev D5ListCode := d5Column.Code
abbrev D6ListCode := d6Column.Code
abbrev D7ListCode := d7Column.Code

abbrev D4ListCard := d4Column.codeCard
abbrev D5ListCard := d5Column.codeCard
abbrev D6ListCard := d6Column.codeCard
abbrev D7ListCard := d7Column.codeCard

noncomputable abbrev d4ListCodeEquivFin := d4Column.codeEquivFin
noncomputable abbrev d5ListCodeEquivFin := d5Column.codeEquivFin
noncomputable abbrev d6ListCodeEquivFin := d6Column.codeEquivFin
noncomputable abbrev d7ListCodeEquivFin := d7Column.codeEquivFin

noncomputable def d4ListCode (stage : package.Stage) : D4ListCode :=
  d4Column.encodeNodup (package.fixedD4Codes stage)
    (package.fixedD4Codes_nodup stage)

noncomputable def d5ListCode {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (stage : package.Stage) : D5ListCode :=
  d5Column.encodeNodup
    (survivor.clear stage).available.normalizedFullBaseCodes
    (survivor.clear stage).available.normalizedFullBaseCodes_nodup

noncomputable def d6ListCode {ledger : package.PriorD6Ledger}
    (_survivor : package.LocalCorridorSurvivor ledger)
    (stage : package.Stage) : D6ListCode :=
  d6Column.encodeNodup
    (package.normalizedD6DeclaredStructuralCodes ledger stage)
    (package.normalizedD6DeclaredStructuralCodes_nodup ledger stage)

noncomputable def d7ListCode {ledger : package.PriorD6Ledger}
    (_survivor : package.LocalCorridorSurvivor ledger)
    (stage : package.Stage) : D7ListCode :=
  d7Column.encodeNodup (package.fixedD7Codes stage)
    (package.fixedD7Codes_nodup stage)

/-- Exactly the original structural field shape, instantiated from the
framework-owned finite two-boundary product.  Completeness of the observed
D4--D7 lists remains a separate graph-semantic producer obligation. -/
abbrev ColdStructuralStateCode := Core.FiniteStructuralCutState.State
  BoundedCarrierRole WindowOffset D4ListCode D5ListCode D6ListCode D7ListCode

noncomputable def coldStructuralStateEncoding :=
  Core.FiniteStructuralCutState.stateEncodingOfColumnBundle
    (halfEdgeCard := Fintype.card BoundedCarrierRole)
    (offsetCard := 13)
    (Fintype.equivFin BoundedCarrierRole) (Equiv.refl WindowOffset)
    coldColumns

noncomputable def coldStructuralStateCode {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (stage : package.Stage) : ColdStructuralStateCode where
  boundaryDegree := package.activeBoundaryDegree stage
  activeHalfEdge := package.activeHalfEdgeEndpointRole stage
  windowOffset := package.activeWindowOffset
  d4 := package.d4ListCode stage
  d5 := package.d5ListCode survivor stage
  d6 := package.d6ListCode survivor stage
  d7 := package.d7ListCode survivor stage

theorem coldStructuralStateCode_boundaryDegree
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (stage : package.Stage) :
    (package.coldStructuralStateCode survivor stage).boundaryDegree =
      package.activeBoundaryDegree stage := rfl

theorem coldStructuralStateCode_activeHalfEdge
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (stage : package.Stage) :
    (package.coldStructuralStateCode survivor stage).activeHalfEdge =
      package.activeHalfEdgeEndpointRole stage := rfl

theorem coldStructuralStateCode_windowOffset
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (stage : package.Stage) :
    (package.coldStructuralStateCode survivor stage).windowOffset =
      package.activeWindowOffset := rfl

noncomputable abbrev QCold : Nat := coldStructuralStateEncoding.finite.bound

/-- The manuscript's uniform first-failure exchange allowance.  The additive
`30` is exactly the already verified two-window active-interface allowance. -/
noncomputable abbrev MCold : Nat :=
  coldStructuralStateEncoding.finite.exchangeWith 30

/-- The manuscript's subcubic ball factor at radius `MCold + 2`. -/
noncomputable def ColdSubcubicBallInterior : Nat :=
  3 * (2 ^ (MCold + 2) - 1)

noncomputable def coldSubcubicBallBoundWithPos : {bound : Nat // 0 < bound} :=
  Core.FiniteStructuralCutState.successorWithPos ColdSubcubicBallInterior

noncomputable def ColdSubcubicBallBound : {bound : Nat // 0 < bound} :=
  coldSubcubicBallBoundWithPos

/-- The fifteen possible source stubs times the subcubic localization ball. -/
noncomputable def BCold : {bound : Nat // 0 < bound} :=
  Core.FiniteStructuralCutState.productWithPos ColdSubcubicBallBound
    ⟨15, by decide⟩

/-- The exact denominator used by the bounded-overlap extraction. -/
noncomputable def DCold : Nat :=
  Core.FiniteStructuralCutState.overlapDenominator MCold BCold.1

theorem MCold_eq_exchangeBound :
    MCold = coldStructuralStateEncoding.finite.exchangeWith 30 := rfl

theorem DCold_eq_overlapDenominator :
    DCold = Core.FiniteStructuralCutState.overlapDenominator MCold BCold.1 := rfl

/-- Exact symbolic cardinality of the structural product.  This proves that
`QCold` depends only on its fixed finite alphabets, not on the graph order or
the length of the actual corridor schedule. -/
theorem QCold_eq_fixed_product :
    coldStructuralStateEncoding.finite.bound =
      coldStructuralStateEncoding.productCard :=
  coldStructuralStateEncoding.bound_eq_productCard

/-- Every support already bounded by `QCold + 1` fits inside the paper's
larger `MCold` exchange allowance. -/
def QCold_add_one_le_MCold :=
  coldStructuralStateEncoding.finite.add_le_exchangeWith_of_le
    (by decide : 1 ≤ 30)

def MCold_pos :=
  coldStructuralStateEncoding.finite.exchangeWith_pos_of_allowance_pos
    (by decide : 0 < 30)

theorem ColdSubcubicBallBound_pos : 0 < ColdSubcubicBallBound.1 :=
  ColdSubcubicBallBound.2

theorem BCold_pos : 0 < BCold.1 := BCold.2

theorem DCold_pos : 0 < DCold := by
  unfold DCold
  exact Core.FiniteStructuralCutState.overlapDenominator_pos MCold BCold.1

noncomputable def coldStructuralStateToFin :=
  coldStructuralStateEncoding.finite.encode

/-! ## Positive-prefix schedule -/

/-- F5 starts after the zero prefix.  Hence each inspected cut has two
genuinely distinct active boundary vertices and needs no degenerate case. -/
noncomputable def positiveStages : Core.OrderedCollection package.Stage :=
  package.profile.positiveStages

theorem positiveStages_mem_positive {stage : package.Stage}
    (member : stage ∈ package.positiveStages.values) : 0 < stage.val := by
  exact package.profile.positiveStages_mem_positive member

theorem positiveStages_getElem_val (index : Nat)
    (inBounds : index < package.positiveStages.values.length) :
    package.positiveStages.values[index].val = index + 1 := by
  exact package.profile.positiveStages_getElem_val index inBounds

theorem positiveStages_pairwise_val_lt :
    package.positiveStages.values.Pairwise
      (fun earlier later => earlier.val < later.val) := by
  exact package.profile.positiveStages_pairwise_val_lt

/-- The refactored structural-only corridor profile.  `code` evaluates the
actual stage and four observed lists; `encode` is symbolic and the alphabet is
never traversed. -/
noncomputable def coldStructuralCorridorProfile
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger) :
    Core.FiniteExactStateCorridor.Profile package.Stage
      ColdStructuralStateCode where
  stages := package.positiveStages
  stateBound := coldStructuralStateEncoding.finite.bound
  encode := coldStructuralStateToFin
  encode_injective := coldStructuralStateEncoding.finite.encode_injective
  code := package.coldStructuralStateCode survivor

noncomputable def runColdStructuralCorridor
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger) :=
  (package.coldStructuralCorridorProfile survivor).run

/-- Equality returned by the repeated Core outcome is only equality of the
structural state.  F2 must still compare exact target responses. -/
theorem repeated_equal_structural_code
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    package.coldStructuralStateCode survivor repetition.first =
      package.coldStructuralStateCode survivor repetition.second :=
  repetition.equalCode

theorem repeated_first_positive
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    0 < repetition.first.val :=
  package.positiveStages_mem_positive repetition.first_mem

theorem repeated_second_positive
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated) :
    0 < repetition.second.val :=
  package.positiveStages_mem_positive repetition.second_mem

end

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
