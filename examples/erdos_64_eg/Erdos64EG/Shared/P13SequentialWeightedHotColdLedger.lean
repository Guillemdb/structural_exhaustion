import Erdos64EG.Shared.P13WeightedLocalGraphInterpretation
import Erdos64EG.Shared.P13ExactWeightedRate
import Erdos64EG.Shared.CT15BaselineSpineDemand
import StructuralExhaustion.Core.DependentOwnerGlueCapacity
import StructuralExhaustion.Core.SequentialCompatibleExtensionLedger

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Core.SequentialCompatibleExtensionLedger

universe u

/-- One accepted window together with its graph interpretation. -/
structure P13SequentialRetainedHot
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) : Type (u + 3) where
  window : P13SelectedConnectorWindow ctx
  package : P13WeightedLiveWindowPackage ctx node21 window
  interpretation : P13WeightedLocalGraphInterpretation package

abbrev P13RetainedLocalChoice
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    (retained : List (P13SequentialRetainedHot ctx node21))
    (owner : Fin retained.length) :=
  P13WeightedScheduledState (retained.get owner).package

/-- The packing-order state: one global completion and all hot owners already
retained in it.  `commutes` is the joint invariant, not coordinatewise
activity. -/
structure P13SequentialHotAggregate
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) : Type (u + 3) where
  retained : List (P13SequentialRetainedHot ctx node21)
  JointState : Type (u + 1)
  jointStates : FinEnum JointState
  glue : (∀ owner, P13RetainedLocalChoice retained owner) → JointState
  recover : JointState → ∀ owner, P13RetainedLocalChoice retained owner
  recover_glue : ∀ choice owner, recover (glue choice) owner = choice owner
  /-- Reset every retained local choice while preserving the remainder state
  of an existing compatible completion.  Absence of such an operation is
  exactly failure of the existing compatible-extension predicate and hence
  enters the already declared cold ledger; it creates no new case. -/
  reglue : JointState →
    (∀ owner, P13RetainedLocalChoice retained owner) → JointState
  recover_reglue : ∀ joint choice owner,
    recover (reglue joint choice) owner = choice owner
  global : JointState → P13GlobalGraphCompletion ctx
  remainderGraph : JointState → SimpleGraph (P13RemainderVertex ctx) :=
    fun joint => (global joint).object.graph.comap (fun vertex => vertex.1)
  /-- The cached projection is definitionally the remainder of the same
  graph-owned completion.  Keeping this equation in the accumulated ledger
  prevents downstream nodes from silently changing the carrier projection. -/
  remainderGraph_exact : ∀ joint,
    remainderGraph joint =
      (global joint).object.graph.comap (fun vertex => vertex.1) := by
    intro joint
    rfl
  remainderGraph_reglue : ∀ joint choice,
    remainderGraph (reglue joint choice) = remainderGraph joint
  commutes : ∀ joint owner coordinate,
    let entry := retained.get owner
    p13GlobalResponse (global joint) entry.window
        (entry.interpretation.interpret (recover joint owner) coordinate)
        (entry.package.barrierIndex coordinate.1) =
      entry.package.accepts coordinate.1 (recover joint owner).1
  Code : Type (u + 1)
  codes : FinEnum Code
  codeCapacity : codes.card ≤ max 1 (baselineSpineStateCount ctx)
  skeletonCode : JointState → Code
  skeletonCodeInjective : Function.Injective skeletonCode
  skeletonCodeInjectiveOnGlue : ∀ left right,
    skeletonCode (glue left) = skeletonCode (glue right) →
      glue left = glue right

namespace P13SequentialHotAggregate

@[implicit_reducible] noncomputable def localChoices
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx node21)
    (owner : Fin aggregate.retained.length) :
    FinEnum (P13RetainedLocalChoice aggregate.retained owner) := by
  let package := (aggregate.retained.get owner).package
  letI : DecidableEq package.State := package.states.decEq
  exact FinEnum.ofList package.states.values.attach
    (by intro state; simpa using state.property)

/-- The joint aggregate instantiates the reusable dependent-owner capacity
theorem; recoverability, rather than coordinatewise activity, supplies the
injective product map. -/
noncomputable def capacityProfile
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx node21) :
    Core.DependentOwnerGlueCapacity.Profile where
  Owner := Fin aggregate.retained.length
  owners := inferInstance
  Local := P13RetainedLocalChoice aggregate.retained
  locals := aggregate.localChoices
  Global := aggregate.JointState
  Code := aggregate.Code
  codes := aggregate.codes
  glue := aggregate.glue
  restrict := aggregate.recover
  recover := aggregate.recover_glue
  code := aggregate.skeletonCode
  codeInjectiveOnGlue := aggregate.skeletonCodeInjectiveOnGlue

theorem localProduct_le_codeCard
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx node21) :
    Nat.card (∀ owner, P13RetainedLocalChoice aggregate.retained owner) ≤
      aggregate.codes.card :=
  aggregate.capacityProfile.localProduct_le_codeCard

theorem localProduct_le_fixedCapacity
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx node21) :
    Nat.card (∀ owner, P13RetainedLocalChoice aggregate.retained owner) ≤
      max 1 (baselineSpineStateCount ctx) :=
  aggregate.localProduct_le_codeCard.trans aggregate.codeCapacity

/-- Total retained separated-scale multiplicity, summed over the exact
dependent owner type of this aggregate. -/
noncomputable def retainedScaleMultiplicity
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx node21) : Nat :=
  aggregate.capacityProfile.weightSum fun owner =>
    (aggregate.retained.get owner).package.scaleMultiplicity

/-- Exact aggregate form of the paper's weighted hot payment.  Every local
rate is the certified `118108581006 / 10^9`; recoverable dependent gluing
multiplies those local cardinalities, and the skeleton code supplies the fixed
capacity.  The bounded power `2^34` is part of the repeated-square
certificate, not an enumeration. -/
theorem exactPoweredRate_le_fixedCapacity
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx node21) :
    2 ^ aggregate.capacityProfile.weightSum (fun owner =>
        118108581006 *
          (aggregate.retained.get owner).package.scaleMultiplicity *
            2 ^ p13ExactWeightedRateCertificate.steps) ≤
      (max 1 (baselineSpineStateCount ctx)) ^
        (1000000000 * 2 ^ p13ExactWeightedRateCertificate.steps) := by
  have codeBound := aggregate.capacityProfile.base_pow_sumWeight_le_codeCard_pow
    2 (1000000000 * 2 ^ p13ExactWeightedRateCertificate.steps)
    (fun owner => 118108581006 *
      (aggregate.retained.get owner).package.scaleMultiplicity *
        2 ^ p13ExactWeightedRateCertificate.steps) (by
      intro owner
      let package := (aggregate.retained.get owner).package
      have localRate := package.exactStatePowerLower
      have localCard :
          Nat.card (P13RetainedLocalChoice aggregate.retained owner) =
            package.states.values.length := by
        let enumeration := aggregate.localChoices owner
        calc
          Nat.card (P13RetainedLocalChoice aggregate.retained owner) =
              enumeration.card := Core.Enumeration.natCard_eq enumeration
          _ = package.states.values.length := by
            dsimp [enumeration, P13SequentialHotAggregate.localChoices]
            rw [FinEnum.card_ofList]
            · rw [List.dedup_eq_self.mpr package.states.nodup.attach]
              simp
            · intro state
              exact List.mem_attach _ state
      exact localRate.trans_eq (congrArg
        (fun cardinal => cardinal ^
          (1000000000 * 2 ^ p13ExactWeightedRateCertificate.steps))
        localCard.symm))
  have codeCapacityPower := Nat.pow_le_pow_left aggregate.codeCapacity
    (1000000000 * 2 ^ p13ExactWeightedRateCertificate.steps)
  exact codeBound.trans codeCapacityPower

end P13SequentialHotAggregate

/-- A distinguished joint state whose global completion is literally the
original counterexample.  This is the witness that makes every final
curvature-flat fibre nonempty; it is carried by Core's one sequential ledger,
not by a node-local checkpoint. -/
structure P13OriginalCompletionWitness
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx node21) : Type (u + 2) where
  joint : aggregate.JointState
  globalExact : aggregate.global joint = p13OriginalGlobalCompletion ctx

/-- An extension is precisely the paper's successful hot step.  It provides
the new graph-owned completion, preserves every response already retained,
and makes the new window commute.  Failure of this entire type is cold. -/
structure P13SequentialCompatibleExtension
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx node21)
    (window : P13SelectedConnectorWindow ctx) : Type (u + 3) where
  package : P13WeightedLiveWindowPackage ctx node21 window
  interpretation : P13WeightedLocalGraphInterpretation package
  next : P13SequentialHotAggregate ctx node21
  retainedExact : next.retained = {
    window := window
    package := package
    interpretation := interpretation
  } :: aggregate.retained
  restrictOldJoint : next.JointState → aggregate.JointState
  oldOwner : Fin aggregate.retained.length → Fin next.retained.length
  oldChoicesRecovered : ∀ joint (owner : Fin aggregate.retained.length),
    HEq (aggregate.recover (restrictOldJoint joint) owner)
      (next.recover joint (oldOwner owner))
  /-- Every accepted hot extension embeds the preceding joint carrier.  In
  particular the original target-avoiding completion is never lost. -/
  liftOldJoint : aggregate.JointState → next.JointState
  global_liftOldJoint : ∀ joint,
    next.global (liftOldJoint joint) = aggregate.global joint

noncomputable def p13SequentialExtend
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    {aggregate : P13SequentialHotAggregate ctx node21}
    {window : P13SelectedConnectorWindow ctx}
    (extension : P13SequentialCompatibleExtension aggregate window) :
    P13SequentialHotAggregate ctx node21 :=
  extension.next

/-- P13 specialization of Core's proof-relevant witness transport. -/
def p13SequentialTransportOriginalWitness
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    {aggregate : P13SequentialHotAggregate ctx node21}
    {window : P13SelectedConnectorWindow ctx}
    (extension : P13SequentialCompatibleExtension aggregate window) :
    P13OriginalCompletionWitness aggregate →
      P13OriginalCompletionWitness extension.next := by
  intro witness
  exact {
    joint := extension.liftOldJoint witness.joint
    globalExact := (extension.global_liftOldJoint witness.joint).trans
      witness.globalExact
  }

/-- Empty aggregate supplied unconditionally by the original counterexample. -/
noncomputable def p13SequentialInitialAggregate
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) :
    P13SequentialHotAggregate ctx node21 where
  retained := []
  JointState := ULift.{u + 1} Unit
  jointStates := inferInstance
  glue := fun _ => ⟨()⟩
  recover := fun _ owner => Fin.elim0 owner
  recover_glue := by intro _ owner; exact Fin.elim0 owner
  reglue := fun _ _ => ⟨()⟩
  recover_reglue := by intro _ _ owner; exact Fin.elim0 owner
  global := fun _ => p13OriginalGlobalCompletion ctx
  remainderGraph_reglue := by intros; rfl
  remainderGraph_exact := by intros; rfl
  commutes := by intro _ owner; exact Fin.elim0 owner
  Code := ULift.{u + 1} Unit
  codes := inferInstance
  codeCapacity := by simp
  skeletonCode := id
  skeletonCodeInjective := fun _ _ equal => equal
  skeletonCodeInjectiveOnGlue := by intros; rfl

/-- The initial aggregate owns the literal original completion. -/
noncomputable def p13SequentialInitialOriginalWitness
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) :
    P13OriginalCompletionWitness (p13SequentialInitialAggregate ctx node21) :=
  { joint := ⟨()⟩
    globalExact := rfl }

noncomputable abbrev p13SequentialWeightedProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) : Profile where
  Window := P13SelectedConnectorWindow ctx
  windows := {
    values := (p13Windows ctx).attach
    nodup := (inducedP13PackingProfile ctx).values_nodup.attach
    decEq := Classical.decEq _
  }
  Aggregate := P13SequentialHotAggregate ctx node21
  Valid := fun _ => True
  initial := p13SequentialInitialAggregate ctx node21
  initialValid := trivial
  Extension := P13SequentialCompatibleExtension
  extend := p13SequentialExtend
  extendValid := by simp

abbrev P13SequentialWeightedLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) :=
  Ledger (p13SequentialWeightedProfile ctx node21)
    (p13SequentialWeightedProfile ctx node21).initial
    (p13SequentialWeightedProfile ctx node21).windows.values

noncomputable def p13SequentialWeightedLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) :
    P13SequentialWeightedLedger ctx node21 :=
  run (p13SequentialWeightedProfile ctx node21)

/-- Sequential cold entries remember the aggregate at the exact rejection
point and absence of the full compatible extension. -/
structure P13SequentialWeightedColdWindow
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) : Type (u + 3) where
  currentAggregate : P13SequentialHotAggregate ctx node21
  window : P13SelectedConnectorWindow ctx
  extensionAbsent : ¬Nonempty
    (P13SequentialCompatibleExtension currentAggregate window)

private noncomputable def sequentialHotOfLedger
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    {aggregate windows} :
    Ledger (p13SequentialWeightedProfile ctx node21) aggregate windows →
      List (P13WeightedHotWindow ctx node21)
  | .nil _ => []
  | @Ledger.accept _ _ window _ _ extension rest =>
      ⟨window, extension.package⟩ :: sequentialHotOfLedger rest
  | .reject _ _ rest => sequentialHotOfLedger rest

private noncomputable def sequentialColdOfLedger
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    {aggregate windows} :
    Ledger (p13SequentialWeightedProfile ctx node21) aggregate windows →
      List (P13SequentialWeightedColdWindow ctx node21)
  | .nil _ => []
  | .accept _ _ rest => sequentialColdOfLedger rest
  | @Ledger.reject _ aggregate window _ _ absent rest =>
      ⟨aggregate, window, absent⟩ :: sequentialColdOfLedger rest

noncomputable def p13SequentialWeightedHotWindows
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) :=
  sequentialHotOfLedger (p13SequentialWeightedLedger ctx node21)

noncomputable def p13SequentialWeightedColdWindows
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) :=
  sequentialColdOfLedger (p13SequentialWeightedLedger ctx node21)

noncomputable def p13SequentialFinalHotAggregate
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) :
    P13SequentialHotAggregate ctx node21 :=
  (p13SequentialWeightedLedger ctx node21).finalAggregate

/-- Core transports the distinguished original completion through the exact
hot/cold ledger.  Rejected windows retain it definitionally; accepted windows
use the extension-owned lift. -/
noncomputable def p13SequentialFinalOriginalWitness
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) :
    P13OriginalCompletionWitness
      (p13SequentialFinalHotAggregate ctx node21) :=
  (p13SequentialWeightedLedger ctx node21).finalWitness
    P13OriginalCompletionWitness
    p13SequentialTransportOriginalWitness
    (p13SequentialInitialOriginalWitness ctx node21)

theorem p13SequentialFinal_localProduct_le_fixedCapacity
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) :
    Nat.card (∀ owner,
      P13RetainedLocalChoice
        (p13SequentialFinalHotAggregate ctx node21).retained owner) ≤
      max 1 (baselineSpineStateCount ctx) :=
  (p13SequentialFinalHotAggregate ctx node21).localProduct_le_fixedCapacity

private theorem sequential_length_partition
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    {aggregate windows}
    (ledger : Ledger (p13SequentialWeightedProfile ctx node21) aggregate windows) :
    (sequentialHotOfLedger ledger).length +
      (sequentialColdOfLedger ledger).length = windows.length := by
  induction ledger with
  | nil => rfl
  | accept _ _ _ ih => simp [sequentialHotOfLedger, sequentialColdOfLedger]; omega
  | reject _ _ _ ih => simp [sequentialHotOfLedger, sequentialColdOfLedger]; omega

private theorem sequential_cold_windows_sublist
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    {aggregate windows}
    (ledger : Ledger (p13SequentialWeightedProfile ctx node21) aggregate windows) :
    List.Sublist
      ((sequentialColdOfLedger ledger).map (fun cold => cold.window)) windows := by
  induction ledger with
  | nil => exact .slnil
  | accept _ _ _ ih => exact .cons _ ih
  | reject _ _ _ ih => exact .cons_cons _ ih

private theorem sequential_final_retained_length
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : P13BarrierRateCertificate}
    {aggregate windows}
    (ledger : Ledger (p13SequentialWeightedProfile ctx node21) aggregate windows) :
    ledger.finalAggregate.retained.length =
      aggregate.retained.length + (sequentialHotOfLedger ledger).length := by
  induction ledger with
  | nil => simp [Ledger.finalAggregate, sequentialHotOfLedger]
  | accept valid extension rest ih =>
      rw [Ledger.finalAggregate, ih]
      change extension.next.retained.length +
          (sequentialHotOfLedger rest).length = _
      rw [extension.retainedExact]
      simp [sequentialHotOfLedger]
      omega
  | reject valid absent rest ih =>
      simpa [Ledger.finalAggregate, sequentialHotOfLedger] using ih

theorem p13SequentialFinal_retainedCount
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) :
    (p13SequentialFinalHotAggregate ctx node21).retained.length =
      (p13SequentialWeightedHotWindows ctx node21).length := by
  simpa [p13SequentialFinalHotAggregate, p13SequentialWeightedHotWindows,
    p13SequentialWeightedLedger, p13SequentialInitialAggregate] using
      sequential_final_retained_length (p13SequentialWeightedLedger ctx node21)

theorem p13SequentialWeightedHotCount_add_coldCount
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) :
    (p13SequentialWeightedHotWindows ctx node21).length +
      (p13SequentialWeightedColdWindows ctx node21).length = p13 ctx := by
  rw [p13SequentialWeightedHotWindows, p13SequentialWeightedColdWindows]
  have partition :=
    sequential_length_partition (p13SequentialWeightedLedger ctx node21)
  change _ = (p13Windows ctx).attach.length at partition
  rw [List.length_attach] at partition
  exact partition.trans rfl

/-- The sequential rejection ledger never duplicates a selected packing
window.  This is inherited from the exact canonical packing order, while each
entry still retains its rejection-relative aggregate and absence proof. -/
theorem p13SequentialWeightedColdWindows_window_nodup
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate) :
    (p13SequentialWeightedColdWindows ctx node21).map
      (fun cold => cold.window) |>.Nodup := by
  exact (sequential_cold_windows_sublist
    (p13SequentialWeightedLedger ctx node21)).nodup
      (p13SequentialWeightedProfile ctx node21).windows.nodup

/-- Exact finite hot/cold payment for the accumulated compatible ledger.  The
only external premise is a bound on the retained hot count; the partition
then charges every rejected extension to the sequential cold list. -/
theorem p13SequentialHotBudget_total_le_budget_add_cold
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate)
    (rate budget : Nat)
    (hotBound : rate * (p13SequentialWeightedHotWindows ctx node21).length ≤
      budget) :
    rate * p13 ctx ≤ budget +
      rate * (p13SequentialWeightedColdWindows ctx node21).length := by
  calc
    rate * p13 ctx = rate *
        ((p13SequentialWeightedHotWindows ctx node21).length +
          (p13SequentialWeightedColdWindows ctx node21).length) := by
      rw [p13SequentialWeightedHotCount_add_coldCount]
    _ = rate * (p13SequentialWeightedHotWindows ctx node21).length +
        rate * (p13SequentialWeightedColdWindows ctx node21).length := by
      rw [Nat.mul_add]
    _ ≤ budget + rate *
        (p13SequentialWeightedColdWindows ctx node21).length :=
      Nat.add_le_add_right hotBound _

theorem p13SequentialHotBudget_shortfall_le_cold
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate)
    (rate budget : Nat)
    (hotBound : rate * (p13SequentialWeightedHotWindows ctx node21).length ≤
      budget) :
    rate * p13 ctx - budget ≤
      rate * (p13SequentialWeightedColdWindows ctx node21).length := by
  have payment := p13SequentialHotBudget_total_le_budget_add_cold
    ctx node21 rate budget hotBound
  omega

theorem p13SequentialHotOverflow_forces_cold_nonempty
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : P13BarrierRateCertificate)
    (rate budget : Nat)
    (hotBound : rate * (p13SequentialWeightedHotWindows ctx node21).length ≤
      budget)
    (overflow : budget < rate * p13 ctx) :
    0 < (p13SequentialWeightedColdWindows ctx node21).length := by
  have payment := p13SequentialHotBudget_total_le_budget_add_cold
    ctx node21 rate budget hotBound
  by_contra notPositive
  have coldZero : (p13SequentialWeightedColdWindows ctx node21).length = 0 :=
    Nat.eq_zero_of_not_pos notPositive
  simp [coldZero] at payment
  omega

end Erdos64EG.Internal
