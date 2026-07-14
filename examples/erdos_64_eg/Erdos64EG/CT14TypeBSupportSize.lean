import Erdos64EG.CT14TypeBAssignedCharge

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Linear size of literal Type B ledger supports

Every local Type B entry uses a bounded number of actual core vertices.  The
bound is derived from the marked-fan degree cap and the exact two-incidence
universe of each cubic-closed neighbour.  It is later used to bound deleted
boundary incidences by assigned center surplus.
-/

namespace TypeBLocalEntry

theorem actualCoreSupport_card_le_twentyFour
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex)
    (entry : TypeBLocalEntry ctx)
    (candidate : (entry.selectionProfile reserve).Candidate) :
    (entry.actualCoreSupport reserve candidate).card ≤ 24 := by
  cases entry with
  | certificate marked =>
      letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
      rw [actualCoreSupport_certificate]
      unfold certificateCoreSupport
      have candidateBound :=
        Core.FiniteWeightedSelection.Profile.Candidate.card_le_items
          ((TypeBLocalEntry.certificate marked).selectionProfile reserve)
          candidate
      calc
        (candidate.1.image fun (item : ULift.{u, 0}
            (Graph.HighCenterPort.Port ctx.G.object marked.fan.center)) =>
            Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center
              item.down).card ≤ candidate.1.card := Finset.card_image_le
        _ ≤ ((TypeBLocalEntry.certificate marked).selectionProfile
              reserve).items.card := candidateBound
        _ = (Graph.HighCenterPort.ports ctx.G.object
              marked.fan.center).card := by
          change (Core.Enumeration.ulift
              (Graph.HighCenterPort.ports ctx.G.object
                marked.fan.center)).card = _
          exact Core.Enumeration.ulift_card _
        _ = ctx.G.object.degree marked.fan.center :=
          Graph.HighCenterPort.ports_card_eq_degree _ _
        _ ≤ 8 := marked.fan.degree_le_eight
        _ ≤ 24 := by omega
  | positive positive =>
      letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
      rw [actualCoreSupport_positive]
      unfold positiveCombinedCoreSupport
      have fanBound :
          (positiveFanCoreSupport positive).card ≤ 8 := by
        unfold positiveFanCoreSupport
        let ports := Graph.HighCenterPort.ports ctx.G.object
          positive.fan.center
        calc
          (ports.orderedValues.toFinset.image fun port =>
                Graph.HighCenterPort.endpoint ctx.G.object
                  positive.fan.center port).card ≤
              ports.orderedValues.toFinset.card := Finset.card_image_le
          _ = ctx.G.object.degree positive.fan.center := by
            rw [List.toFinset_card_of_nodup ports.nodup_orderedValues,
              ports.orderedValues_length]
            exact Graph.HighCenterPort.ports_card_eq_degree _ _
          _ ≤ 8 := positive.degree_le_eight
      have ordinaryBound :
          (positiveOrdinaryCoreSupport reserve positive candidate).card ≤ 16 := by
        unfold positiveOrdinaryCoreSupport
        let profile := p13FanWindowProfile ctx positive.Assigned
          positive.assignedDecidable
        have closedCard :
            (Graph.HybridFanIncidence.closedMembers
              (object := ctx.G.object) (center := positive.fan.center)
              profile).card ≤
              ctx.G.object.degree positive.fan.center := by
          letI : FinEnum
              (Graph.HybridFanIncidence.ClosedMember
                (object := ctx.G.object) (center := positive.fan.center)
                profile) :=
            Graph.HybridFanIncidence.closedMembers
              (object := ctx.G.object) (center := positive.fan.center) profile
          letI : FinEnum
              (Graph.HighCenterPort.Port ctx.G.object positive.fan.center) :=
            Graph.HighCenterPort.ports ctx.G.object positive.fan.center
          have injected := Fintype.card_le_of_injective
            (Graph.HybridFanIncidence.memberPort
              (object := ctx.G.object) (center := positive.fan.center) profile)
            (Graph.HybridFanIncidence.memberPort_injective
              (object := ctx.G.object) (center := positive.fan.center) profile)
          rw [FinEnum.card_eq_fintypeCard]
          calc
            Fintype.card (Graph.HybridFanIncidence.ClosedMember
                (object := ctx.G.object) (center := positive.fan.center)
                profile) ≤
              Fintype.card (Graph.HighCenterPort.Port ctx.G.object
                positive.fan.center) := injected
            _ = (Graph.HighCenterPort.ports ctx.G.object
                positive.fan.center).card := by
              rw [FinEnum.card_eq_fintypeCard]
            _ = ctx.G.object.degree positive.fan.center :=
              Graph.HighCenterPort.ports_card_eq_degree _ _
        have incidenceCard :
            (Graph.HybridFanIncidence.incidences
              (object := ctx.G.object) (center := positive.fan.center)
              profile).card ≤ 16 := by
          rw [Graph.HybridFanIncidence.incidence_card]
          have degreeBound := positive.degree_le_eight
          omega
        have candidateBound :=
          Core.FiniteWeightedSelection.Profile.Candidate.card_le_items
            ((TypeBLocalEntry.positive positive).selectionProfile reserve)
            candidate
        have candidateIncidenceBound :
            candidate.1.card ≤
              (Graph.HybridFanIncidence.incidences
                (object := ctx.G.object) (center := positive.fan.center)
                profile).card := by
          calc
            candidate.1.card ≤
                ((TypeBLocalEntry.positive positive).selectionProfile
                  reserve).items.card := candidateBound
            _ = (Graph.HybridFanIncidence.incidences
                (object := ctx.G.object) (center := positive.fan.center)
                profile).card := by rfl
        calc
          ((candidate.1.filter fun incidence =>
              Graph.HybridFanIncidence.incidenceKind
                (object := ctx.G.object) (center := positive.fan.center)
                profile incidence = .nonWindow).image fun incidence =>
                  Graph.HybridFanIncidence.other
                    (object := ctx.G.object) (center := positive.fan.center)
                    profile incidence.1 incidence.2).card ≤
              (candidate.1.filter fun incidence =>
                Graph.HybridFanIncidence.incidenceKind
                  (object := ctx.G.object) (center := positive.fan.center)
                  profile incidence = .nonWindow).card := Finset.card_image_le
          _ ≤ candidate.1.card := Finset.card_filter_le _ _
          _ ≤ (Graph.HybridFanIncidence.incidences
                (object := ctx.G.object) (center := positive.fan.center)
                profile).card := candidateIncidenceBound
          _ ≤ 16 := incidenceCard
      calc
        (positiveFanCoreSupport positive ∪
            positiveOrdinaryCoreSupport reserve positive candidate).card ≤
          (positiveFanCoreSupport positive).card +
            (positiveOrdinaryCoreSupport reserve positive candidate).card :=
          Finset.card_union_le _ _
        _ ≤ 24 := by omega

end TypeBLocalEntry

namespace TypeBAssignedSupport

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (support : TypeBAssignedSupport ctx)

theorem fullDemandSet_card_eq_centers :
    support.fullDemandSet.card = support.centers.card := by
  letI : DecidableEq support.Demand := support.demands.decEq
  letI : FinEnum support.Demand := support.demands
  unfold fullDemandSet
  rw [List.toFinset_card_of_nodup support.demands.nodup_orderedValues,
    support.demands.orderedValues_length,
    FinEnum.card_eq_fintypeCard, Fintype.card_coe]

theorem fullActualCoreSupport_card_le_twentyFour
    (choice : support.completionProfile.FullChoice)
    (demand : support.Demand) :
    (support.fullActualCoreSupport choice demand).card ≤ 24 := by
  unfold fullActualCoreSupport
  exact TypeBLocalEntry.actualCoreSupport_card_le_twentyFour
    support.reserve (support.entry demand)
      (support.fullChosenLocalCandidate choice demand)

theorem usedCore_card_le_twentyFour_mul_centers
    (choice : support.completionProfile.FullChoice) :
    (support.usedCore choice).card ≤ 24 * support.centers.card := by
  letI : DecidableEq support.Demand := support.demands.decEq
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  unfold usedCore
  calc
    (support.fullDemandSet.biUnion
        (support.fullActualCoreSupport choice)).card ≤
      support.fullDemandSet.card * 24 :=
        Finset.card_biUnion_le_card_mul support.fullDemandSet
          (support.fullActualCoreSupport choice) 24
          (fun demand _member =>
            support.fullActualCoreSupport_card_le_twentyFour choice demand)
    _ = support.centers.card * 24 := by
      rw [support.fullDemandSet_card_eq_centers]
    _ = 24 * support.centers.card := Nat.mul_comm _ _

theorem processedCore_card_le_twentyFive_mul_centers
    (choice : support.completionProfile.FullChoice) :
    (support.processedCore choice).card ≤ 25 * support.centers.card := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  unfold processedCore Graph.AssignedSupportCharge.Profile.processedCore
    assignedChargeProfile
  change (support.usedCore choice ∪ support.centers).card ≤
    25 * support.centers.card
  have unionBound := Finset.card_union_le
    (support.usedCore choice) support.centers
  have usedBound := support.usedCore_card_le_twentyFour_mul_centers choice
  omega

theorem processedVertex_degree_le_eight
    (choice : support.completionProfile.FullChoice)
    {vertex : ctx.G.Vertex}
    (processed : vertex ∈ support.processedCore choice) :
    ctx.G.object.degree vertex ≤ 8 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  change vertex ∈ support.usedCore choice ∪ support.centers at processed
  rcases Finset.mem_union.mp processed with used | center
  · have notCenter : vertex ∉ support.centers := by
      exact (Finset.disjoint_left.mp (support.usedCore_disjoint_centers choice))
        used
    have notHigh : ¬4 ≤ ctx.G.object.degree vertex := by
      intro high
      apply notCenter
      rw [support.centers_exact]
      exact Finset.mem_filter.mpr
        ⟨support.usedCore_subset_core choice used, high⟩
    omega
  · let demand : support.Demand := ⟨vertex, center⟩
    have centerEq := support.entry_center demand
    cases entryEq : support.entry demand with
    | certificate marked =>
        rw [entryEq] at centerEq
        change marked.fan.center = vertex at centerEq
        rw [← centerEq]
        exact marked.fan.degree_le_eight
    | positive positive =>
        rw [entryEq] at centerEq
        change positive.fan.center = vertex at centerEq
        rw [← centerEq]
        exact positive.degree_le_eight

theorem processedDegreeSum_le_twoHundred_mul_centers
    (choice : support.completionProfile.FullChoice) :
    (∑ vertex ∈ support.processedCore choice,
      ctx.G.object.degree vertex) ≤ 200 * support.centers.card := by
  have pointwise := Finset.sum_le_card_nsmul
    (support.processedCore choice) ctx.G.object.degree 8
      (fun vertex member =>
        support.processedVertex_degree_le_eight choice member)
  have cardinal := support.processedCore_card_le_twentyFive_mul_centers choice
  calc
    (∑ vertex ∈ support.processedCore choice,
        ctx.G.object.degree vertex) ≤
        (support.processedCore choice).card * 8 := by
      simpa [nsmul_eq_mul] using pointwise
    _ ≤ (25 * support.centers.card) * 8 :=
      Nat.mul_le_mul_right 8 cardinal
    _ = 200 * support.centers.card := by omega

theorem centers_card_le_assignedSurplus :
    support.centers.card ≤
      support.assignedChargeProfile.assignedSurplus := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  unfold assignedChargeProfile
    Graph.AssignedSupportCharge.Profile.assignedSurplus
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro center member
  have high : 4 ≤ ctx.G.object.degree center := by
    rw [support.centers_exact] at member
    exact (Finset.mem_filter.mp member).2
  unfold Graph.AssignedSupportCharge.Profile.surplusAt
  omega

end TypeBAssignedSupport

end Erdos64EG.Internal
