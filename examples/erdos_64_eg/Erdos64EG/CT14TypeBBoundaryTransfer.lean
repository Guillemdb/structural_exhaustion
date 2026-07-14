import Erdos64EG.CT14TypeARemainingDischarge
import StructuralExhaustion.Core.FiniteBoundaryTransfer
import StructuralExhaustion.Graph.FiniteInducedBoundary

namespace Erdos64EG.Internal

open StructuralExhaustion
open scoped BigOperators

universe u

/-!
# Literal Type B boundary transfer

The induced Type A remainder has four extra quarter-units for each incidence
deleted by the B-ledger.  This file does not assume that those units are free.
It constructs the exact finite transfer problem whose demand is the actual
deleted-incidence count and whose supply is the actual selected-fan plus
center-correction bracket.

An injective transfer proves the original Type B net charge nonnegative.  If
no injection exists, the framework returns the strict numerical overload as
the remaining graph branch.  No assignment space is enumerated.
-/

namespace TypeBAssignedSupport

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (support : TypeBAssignedSupport ctx)

/-- The two nonnegative processed brackets in the exact post-ledger identity. -/
noncomputable def processedQuarterReserve
    (choice : support.completionProfile.FullChoice) : Int :=
  (support.assignedChargeProfile.centerQuarterCharge +
      ∑ vertex ∈ support.usedCore choice,
        support.assignedChargeProfile.coreQuarterChargeAt vertex) +
    ((∑ center ∈ support.centers,
        support.assignedChargeProfile.coreQuarterChargeAt center) +
      (support.centers.card : Int))

theorem processedQuarterReserve_nonnegative
    (choice : support.completionProfile.FullChoice) :
    0 ≤ support.processedQuarterReserve choice := by
  unfold processedQuarterReserve
  exact Int.add_nonneg
    (support.processedFanCharge_nonnegative choice)
    support.centerCoreCharge_add_card_nonnegative

theorem netQuarterCharge_eq_processedReserve_add_remaining
    (choice : support.completionProfile.FullChoice) :
    support.assignedChargeProfile.netQuarterCharge =
      support.processedQuarterReserve choice +
        support.remainingQuarterCharge choice := by
  rw [support.netQuarterCharge_eq_processed_add_centerCorrection_add_remaining
    choice]
  rfl

/-- Finite transfer profile indexed by the literal vertices of the remaining
induced graph.  Each lost original-core incidence requires four quarter-units;
the supply is exactly the nonnegative processed bracket. -/
noncomputable def boundaryTransferProfile
    (choice : support.completionProfile.FullChoice) :
    Core.FiniteBoundaryTransfer.Profile
      {vertex : ctx.G.Vertex // vertex ∈ support.remainingCore choice} where
  items := (support.remainingObject choice).input.vertices
  multiplicity := support.remainingBoundaryLoss choice
  unitsPerIncidence := 4
  availableUnits := Int.toNat (support.processedQuarterReserve choice)

abbrev BoundaryTransfer
    (choice : support.completionProfile.FullChoice) :=
  (support.boundaryTransferProfile choice).Transfer

abbrev BoundaryOverload
    (choice : support.completionProfile.FullChoice) : Prop :=
  (support.boundaryTransferProfile choice).Overloaded

/-- The same deletion as a literal induced-boundary graph profile. -/
noncomputable def inducedBoundaryProfile
    (choice : support.completionProfile.FullChoice) :
    Graph.FiniteInducedBoundary.Profile ctx.G.object where
  whole := support.vertices
  processed := support.processedCore choice
  processed_subset_whole := support.processedCore_subset_core choice

abbrev BoundaryIncidence
    (choice : support.completionProfile.FullChoice) :=
  (support.inducedBoundaryProfile choice).Incidence

/-- Every cut incidence lands either at an assigned high center or at the
literal actual core support consumed by one concrete local demand. -/
inductive BoundaryLanding
    (choice : support.completionProfile.FullChoice) : Type u where
  | center
      (incidence : support.BoundaryIncidence choice)
      (center_mem : incidence.deleted ∈ support.centers)
  | selected
      (incidence : support.BoundaryIncidence choice)
      (demand : support.Demand)
      (selected_mem : incidence.deleted ∈
        support.fullActualCoreSupport choice demand)

@[simp]
theorem inducedBoundary_remaining
    (choice : support.completionProfile.FullChoice) :
    (support.inducedBoundaryProfile choice).remaining =
      support.remainingCore choice := by
  rfl

theorem inducedBoundary_loss_eq_remainingBoundaryLoss
    (choice : support.completionProfile.FullChoice)
    (vertex : {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice}) :
    (support.inducedBoundaryProfile choice).loss vertex.1 =
      support.remainingBoundaryLoss choice vertex := by
  rw [show
    (support.inducedBoundaryProfile choice).loss vertex.1 =
      support.assignedChargeProfile.internalDegree vertex.1 -
        support.remainingNeighborCount choice vertex by rfl]
  unfold remainingBoundaryLoss
  rw [support.remainingObject_degree_eq_remainingNeighborCount choice vertex]

theorem boundaryIncidence_lands
    (choice : support.completionProfile.FullChoice)
    (incidence : support.BoundaryIncidence choice) :
    Nonempty (support.BoundaryLanding choice) := by
  letI : DecidableEq support.Demand := support.demands.decEq
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  have processed : incidence.deleted ∈
      support.usedCore choice ∪ support.centers := by
    exact incidence.deleted_mem
  rcases Finset.mem_union.mp processed with used | center
  · unfold usedCore at used
    rcases Finset.mem_biUnion.mp used with
      ⟨demand, _demandMem, selected⟩
    exact ⟨BoundaryLanding.selected incidence demand selected⟩
  · exact ⟨BoundaryLanding.center incidence center⟩

theorem boundaryTransfer_totalIncidences
    (choice : support.completionProfile.FullChoice) :
    (support.boundaryTransferProfile choice).totalIncidences =
      ∑ vertex : {vertex : ctx.G.Vertex //
          vertex ∈ support.remainingCore choice},
        support.remainingBoundaryLoss choice vertex := by
  letI : FinEnum {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice} :=
    (support.remainingObject choice).input.vertices
  letI : DecidableEq {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice} :=
    (support.remainingObject choice).input.vertices.decEq
  unfold boundaryTransferProfile
    Core.FiniteBoundaryTransfer.Profile.totalIncidences
  rw [show
    (support.remainingObject choice).input.vertices.orderedValues.toFinset =
      (Finset.univ : Finset {vertex : ctx.G.Vertex //
        vertex ∈ support.remainingCore choice}) by
      ext vertex
      simp]

theorem boundaryTransfer_requiredUnits
    (choice : support.completionProfile.FullChoice) :
    (support.boundaryTransferProfile choice).requiredUnits =
      4 * ∑ vertex : {vertex : ctx.G.Vertex //
          vertex ∈ support.remainingCore choice},
        support.remainingBoundaryLoss choice vertex := by
  unfold Core.FiniteBoundaryTransfer.Profile.requiredUnits
  rw [support.boundaryTransfer_totalIncidences choice]
  rfl

theorem remainingBoundaryCredit_eq_requiredUnits
    (choice : support.completionProfile.FullChoice) :
    support.remainingBoundaryCredit choice =
      ((support.boundaryTransferProfile choice).requiredUnits : Int) := by
  rw [support.boundaryTransfer_requiredUnits choice]
  unfold remainingBoundaryCredit
  norm_cast

theorem boundaryTransfer_availableUnits_cast
    (choice : support.completionProfile.FullChoice) :
    ((support.boundaryTransferProfile choice).availableUnits : Int) =
      support.processedQuarterReserve choice := by
  unfold boundaryTransferProfile
  exact Int.toNat_of_nonneg
    (support.processedQuarterReserve_nonnegative choice)

/-- A strict unit overload is supported by an actual graph edge crossing from
the remaining induced core to the processed B-ledger vertices. -/
theorem boundaryOverload_has_incidence
    (choice : support.completionProfile.FullChoice)
    (overload : support.BoundaryOverload choice) :
    Nonempty (support.BoundaryIncidence choice) := by
  letI : FinEnum {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice} :=
    (support.remainingObject choice).input.vertices
  letI : DecidableEq {vertex : ctx.G.Vertex //
      vertex ∈ support.remainingCore choice} :=
    (support.remainingObject choice).input.vertices.decEq
  have requiredPositive :
      0 < (support.boundaryTransferProfile choice).requiredUnits := by
    unfold BoundaryOverload Core.FiniteBoundaryTransfer.Profile.Overloaded at overload
    omega
  rw [support.boundaryTransfer_requiredUnits choice] at requiredPositive
  have totalPositive :
      0 < ∑ vertex : {vertex : ctx.G.Vertex //
          vertex ∈ support.remainingCore choice},
        support.remainingBoundaryLoss choice vertex := by
    omega
  have positiveVertex :
      ∃ vertex : {vertex : ctx.G.Vertex //
          vertex ∈ support.remainingCore choice},
        0 < support.remainingBoundaryLoss choice vertex := by
    have witnessed := (Finset.sum_pos_iff.mp totalPositive)
    simpa using witnessed
  rcases positiveVertex with ⟨vertex, positive⟩
  apply (support.inducedBoundaryProfile choice).exists_incidence_of_loss_pos
    vertex.1
  · simpa using vertex.2
  · rw [support.inducedBoundary_loss_eq_remainingBoundaryLoss choice vertex]
    exact positive

theorem boundaryOverload_has_landing
    (choice : support.completionProfile.FullChoice)
    (overload : support.BoundaryOverload choice) :
    Nonempty (support.BoundaryLanding choice) := by
  let incidence := Classical.choice
    (support.boundaryOverload_has_incidence choice overload)
  exact support.boundaryIncidence_lands choice incidence

/-- An actual injection of boundary demand units into processed ledger slots
is exactly the inequality needed to put the induced Type A charge back into
the original Type B identity. -/
theorem remainingBoundaryCredit_le_processedReserve
    (choice : support.completionProfile.FullChoice)
    (transfer : support.BoundaryTransfer choice) :
    support.remainingBoundaryCredit choice ≤
      support.processedQuarterReserve choice := by
  have unitBound :=
    (support.boundaryTransferProfile choice).requiredUnits_le_availableUnits
      transfer
  have unitBoundInt :
      ((support.boundaryTransferProfile choice).requiredUnits : Int) ≤
        ((support.boundaryTransferProfile choice).availableUnits : Int) := by
    exact_mod_cast unitBound
  calc
    support.remainingBoundaryCredit choice =
        ((support.boundaryTransferProfile choice).requiredUnits : Int) :=
      support.remainingBoundaryCredit_eq_requiredUnits choice
    _ ≤ ((support.boundaryTransferProfile choice).availableUnits : Int) :=
      unitBoundInt
    _ = support.processedQuarterReserve choice :=
      support.boundaryTransfer_availableUnits_cast choice

/-- Successful transfer plus unsaturated Type A discharging closes the
literal original Type B net charge. -/
theorem netQuarterCharge_nonnegative_of_unsaturated_boundaryTransfer
    (choice : support.completionProfile.FullChoice)
    (unsaturated : support.RemainingUnsaturated choice)
    (transfer : support.BoundaryTransfer choice) :
    0 ≤ support.assignedChargeProfile.netQuarterCharge := by
  have adjusted := support.raw_add_boundary_nonnegative_of_unsaturated
    choice unsaturated
  have transferBound :=
    support.remainingBoundaryCredit_le_processedReserve choice transfer
  rw [support.netQuarterCharge_eq_processedReserve_add_remaining choice]
  omega

end TypeBAssignedSupport

end Erdos64EG.Internal
