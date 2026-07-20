import Erdos64EG.Node51
import StructuralExhaustion.Core.PoweredJointNormalization

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

noncomputable def node52CertificateScale : Nat :=
  2 ^ p13ExactWeightedRateCertificate.steps

noncomputable def node52CapacityExponent : Nat :=
  1000000000 * node52CertificateScale

noncomputable def node52HotScaleTotal {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : Nat :=
  let aggregate := node49CanonicalAggregate active.data.previous
    active.data.outerProof active.data.outerOutput
  aggregate.capacityProfile.weightSum fun owner =>
    (aggregate.retained.get owner).package.scaleMultiplicity

noncomputable def node52HotScaleLoss {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : Nat :=
  let aggregate := node49CanonicalAggregate active.data.previous
    active.data.outerProof active.data.outerOutput
  aggregate.capacityProfile.weightSum fun owner =>
    (aggregate.retained.get owner).package.scaleLoss

noncomputable def node52ColdWindowCount {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : Nat :=
  (p13SequentialWeightedColdWindows (Node21Context active.data.previous)
    active.data.outerOutput.barrierRateCertificate).length

noncomputable def node52PaidWindowExponent {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : Nat :=
  118108581006 * node52HotScaleTotal active * node52CertificateScale

noncomputable def node52DesiredWindowExponent {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : Nat :=
  118108581006 * p13 (Node21Context active.data.previous) *
    Nat.log 2 (Node21Context active.data.previous).G.object.input.vertices.card *
      node52CertificateScale

noncomputable def node52WindowErrorExponent {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : Nat :=
  118108581006 *
      (node52HotScaleLoss active + node52ColdWindowCount active *
        Nat.log 2
          (Node21Context active.data.previous).G.object.input.vertices.card) *
    node52CertificateScale

private theorem node52HotScaleTotal_add_loss {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) :
    node52HotScaleTotal active + node52HotScaleLoss active =
      (p13SequentialWeightedHotWindows (Node21Context active.data.previous)
        active.data.outerOutput.barrierRateCertificate).length *
        Nat.log 2
          (Node21Context active.data.previous).G.object.input.vertices.card := by
  let aggregate := node49CanonicalAggregate active.data.previous
    active.data.outerProof active.data.outerOutput
  change aggregate.capacityProfile.weightSum (fun owner =>
      (aggregate.retained.get owner).package.scaleMultiplicity) +
    aggregate.capacityProfile.weightSum (fun owner =>
      (aggregate.retained.get owner).package.scaleLoss) = _
  rw [← aggregate.capacityProfile.weightSum_add]
  calc
    aggregate.capacityProfile.weightSum (fun owner =>
        (aggregate.retained.get owner).package.scaleMultiplicity +
          (aggregate.retained.get owner).package.scaleLoss) =
        aggregate.capacityProfile.weightSum (fun _ =>
          Nat.log 2
            (Node21Context active.data.previous).G.object.input.vertices.card) := by
      apply congrArg
      funext owner
      exact (aggregate.retained.get owner).package.scaleCountExact
    _ = aggregate.capacityProfile.owners.card *
        Nat.log 2
          (Node21Context active.data.previous).G.object.input.vertices.card :=
      aggregate.capacityProfile.weightSum_const _
    _ = aggregate.retained.length *
        Nat.log 2
          (Node21Context active.data.previous).G.object.input.vertices.card := by
      simp [P13SequentialHotAggregate.capacityProfile]
    _ = _ := by
      have retainedExact : aggregate.retained.length =
          (p13SequentialWeightedHotWindows
            (Node21Context active.data.previous)
            active.data.outerOutput.barrierRateCertificate).length := by
        calc
          aggregate.retained.length =
              (p13SequentialFinalHotAggregate
                (Node21Context active.data.previous)
                active.data.outerOutput.barrierRateCertificate).retained.length :=
            congrArg (fun result => result.retained.length)
              (node49CanonicalAggregate_eq active.data.previous
                active.data.outerProof active.data.outerOutput)
          _ = _ := p13SequentialFinal_retainedCount _ _
      exact congrArg (fun count => count *
        Nat.log 2
          (Node21Context active.data.previous).G.object.input.vertices.card)
        retainedExact

private theorem node52DesiredExponent_exact {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) :
    node52DesiredWindowExponent active =
      node52PaidWindowExponent active + node52WindowErrorExponent active := by
  have scales := node52HotScaleTotal_add_loss active
  have partition := p13SequentialWeightedHotCount_add_coldCount
    (Node21Context active.data.previous)
    active.data.outerOutput.barrierRateCertificate
  have combined :
      node52HotScaleTotal active + node52HotScaleLoss active +
          node52ColdWindowCount active *
            Nat.log 2
              (Node21Context active.data.previous).G.object.input.vertices.card =
        p13 (Node21Context active.data.previous) *
          Nat.log 2
            (Node21Context active.data.previous).G.object.input.vertices.card := by
    calc
      _ =
          ((p13SequentialWeightedHotWindows
              (Node21Context active.data.previous)
              active.data.outerOutput.barrierRateCertificate).length +
            node52ColdWindowCount active) *
              Nat.log 2
                (Node21Context active.data.previous).G.object.input.vertices.card := by
        rw [scales]
        ring
      _ = _ := by
        unfold node52ColdWindowCount
        rw [partition]
  unfold node52DesiredWindowExponent node52PaidWindowExponent
    node52WindowErrorExponent
  calc
    _ = 118108581006 *
          (p13 (Node21Context active.data.previous) *
            Nat.log 2
              (Node21Context active.data.previous).G.object.input.vertices.card) *
        node52CertificateScale := by ring
    _ = 118108581006 *
          (node52HotScaleTotal active + node52HotScaleLoss active +
            node52ColdWindowCount active *
              Nat.log 2
                (Node21Context active.data.previous).G.object.input.vertices.card) *
        node52CertificateScale := by rw [← combined]
    _ = _ := by ring

/-!
# Diagram node [52]: joint window--remainder accounting

Node [52] consumes only node [51]'s literal high-entropy leaf.  Its one new
mathematical certificate is the exact same-skeleton capacity of the realized
remainder family together with every dependent hot-window choice.  Core owns
the continuation and transports the node-[50] low leaf and every bypass
unchanged.
-/

/-- Exact finite joint accounting before logarithmic normalization. -/
def Node52JointCapacity {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual) : Prop :=
  let aggregate := node49CanonicalAggregate active.data.previous
    active.data.outerProof active.data.outerOutput
  active.output.stateCount *
      Nat.card (∀ owner,
        P13RetainedLocalChoice aggregate.retained owner) ≤
    aggregate.codes.card

/-- The same joint family fits in the labelled skeleton capacity. -/
def Node52SkeletonCapacity {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual) : Prop :=
  let aggregate := node49CanonicalAggregate active.data.previous
    active.data.outerProof active.data.outerOutput
  active.output.stateCount *
      Nat.card (∀ owner,
        P13RetainedLocalChoice aggregate.retained owner) ≤
    max 1 (baselineSpineStateCount (Node21Context active.data.previous))

/-- Node [52]'s finite error-bearing window--remainder feasibility theorem. -/
def Node52NormalizedJointCapacity {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : Prop :=
  active.output.stateCount ^ node52CapacityExponent *
      2 ^ node52DesiredWindowExponent active ≤
    (max 1 (baselineSpineStateCount
      (Node21Context active.data.previous))) ^ node52CapacityExponent *
      2 ^ node52WindowErrorExponent active

/-- The exact real-logarithmic feasibility inequality consumed by node [54].
It is merely the logarithm of `Node52NormalizedJointCapacity`; every finite
normalization error remains explicit. -/
def Node52LogarithmicJointCapacity {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : Prop :=
  (node52CapacityExponent : ℝ) * Real.logb 2 active.output.stateCount +
      (node52DesiredWindowExponent active : ℝ) ≤
    (node52CapacityExponent : ℝ) * Real.logb 2
        (max 1 (baselineSpineStateCount
          (Node21Context active.data.previous))) +
      (node52WindowErrorExponent active : ℝ)

/-- Node [52]'s exact paper-facing feasibility budget.  The remainder term is
node [51]'s inherited high-entropy contribution; node [54] consumes precisely
the strict reverse of this proposition. -/
def Node52JointBudget {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : Prop :=
  (node52CapacityExponent : ℝ) *
        ((((p13RemainderVertices
          (Node21Context active.data.previous)).card : ℝ) / 10) *
          Real.logb 2
            (Node21Context active.data.previous).G.object.input.vertices.card) +
      (node52DesiredWindowExponent active : ℝ) ≤
    (node52CapacityExponent : ℝ) * Real.logb 2
        (max 1 (baselineSpineStateCount
          (Node21Context active.data.previous))) +
      (node52WindowErrorExponent active : ℝ)

/-- Node [52]'s sole new, error-preserving mathematical output. -/
structure Node52Output {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual)
    (_high : Node50High residual active) : Type (u + 2) where
  jointCapacity : Node52JointCapacity active
  skeletonCapacity : Node52SkeletonCapacity active
  normalizedJointCapacity : Node52NormalizedJointCapacity active
  logarithmicJointCapacity : Node52LogarithmicJointCapacity active
  jointBudget : Node52JointBudget active

private theorem node52JointCapacity {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) :
    Node52JointCapacity active := by
  let aggregate := node49CanonicalAggregate active.data.previous
    active.data.outerProof active.data.outerOutput
  change active.output.stateCount *
      Nat.card (∀ owner,
        P13RetainedLocalChoice aggregate.retained owner) ≤
    aggregate.codes.card
  calc
    active.output.stateCount *
          Nat.card (∀ owner,
            P13RetainedLocalChoice aggregate.retained owner) =
        Nat.card (Core.DependentOwnerGlueCapacity.RealizedProjection
          aggregate.JointState
          (SimpleGraph (P13RemainderVertex
            (Node21Context active.data.previous)))
          aggregate.remainderGraph) *
          Nat.card (∀ owner,
            P13RetainedLocalChoice aggregate.retained owner) := by
      rw [active.output.stateCountExact]
    _ ≤ aggregate.codes.card :=
      node49_realizedRemainder_mul_hotChoices_le_skeletonCode aggregate

private theorem node52SkeletonCapacity {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) :
    Node52SkeletonCapacity active := by
  let aggregate := node49CanonicalAggregate active.data.previous
    active.data.outerProof active.data.outerOutput
  exact (node52JointCapacity active).trans aggregate.codeCapacity

private theorem node52PaidPoweredCapacity {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) :
    active.output.stateCount ^ node52CapacityExponent *
        2 ^ node52PaidWindowExponent active ≤
      (max 1 (baselineSpineStateCount
        (Node21Context active.data.previous))) ^ node52CapacityExponent := by
  let aggregate := node49CanonicalAggregate active.data.previous
    active.data.outerProof active.data.outerOutput
  let profile := node49RealizedRemainderHotCapacityProfile aggregate
  have localLower : ∀ owner,
      2 ^ (118108581006 *
          (aggregate.retained.get owner).package.scaleMultiplicity *
            node52CertificateScale) ≤
        Nat.card (P13RetainedLocalChoice aggregate.retained owner) ^
          node52CapacityExponent := by
    intro owner
    let package := (aggregate.retained.get owner).package
    have rate := package.exactStatePowerLower
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
    change 2 ^ (118108581006 * package.scaleMultiplicity *
        node52CertificateScale) ≤
      Nat.card (P13RetainedLocalChoice aggregate.retained owner) ^
        node52CapacityExponent
    simpa [node52CertificateScale, node52CapacityExponent] using
      rate.trans_eq (congrArg
        (fun cardinal => cardinal ^ node52CapacityExponent) localCard.symm)
  have powered := profile.base_pow_mul_base_pow_sumWeight_le_codeCard_pow
    2 node52CapacityExponent
    (fun owner => 118108581006 *
      (aggregate.retained.get owner).package.scaleMultiplicity *
        node52CertificateScale)
    localLower
  have baseExact : Nat.card profile.Base = active.output.stateCount := by
    exact active.output.stateCountExact.symm
  have paidExact : profile.weightSum (fun owner => 118108581006 *
      (aggregate.retained.get owner).package.scaleMultiplicity *
        node52CertificateScale) = node52PaidWindowExponent active := by
    dsimp [profile, node49RealizedRemainderHotCapacityProfile,
      node52PaidWindowExponent, node52HotScaleTotal]
    unfold Core.DependentOwnerGlueCapacity.BaseProfile.weightSum
      Core.DependentOwnerGlueCapacity.Profile.weightSum
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro owner _membership
    rfl
  rw [baseExact, paidExact] at powered
  exact powered.trans (Nat.pow_le_pow_left aggregate.codeCapacity _)

/-- The exact powered inequality with every discarded hot scale and every
cold window retained on the error side. -/
noncomputable def node52NormalizationProfile {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) :
    Core.PoweredJointNormalization.Profile where
  stateCount := active.output.stateCount
  base := 2
  exponent := node52CapacityExponent
  paidExponent := node52PaidWindowExponent active
  desiredExponent := node52DesiredWindowExponent active
  errorExponent := node52WindowErrorExponent active
  capacity := max 1 (baselineSpineStateCount
    (Node21Context active.data.previous))
  paidCapacity := node52PaidPoweredCapacity active
  desiredExact := node52DesiredExponent_exact active

private theorem node52NormalizedJointCapacity {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) :
    Node52NormalizedJointCapacity active :=
  (node52NormalizationProfile active).withError

private theorem node52StateCountPos {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) :
    0 < active.output.stateCount := by
  let aggregate := node49CanonicalAggregate active.data.previous
    active.data.outerProof active.data.outerOutput
  have choices : ∀ owner,
      P13RetainedLocalChoice aggregate.retained owner := by
    intro owner
    let package := (aggregate.retained.get owner).package
    have rate := package.exactStatePowerLower
    have lengthPos : 0 < package.states.values.length := by
      by_contra notPositive
      have lengthZero : package.states.values.length = 0 :=
        Nat.eq_zero_of_not_pos notPositive
      rw [lengthZero] at rate
      norm_num [node52CertificateScale, node52CapacityExponent] at rate
    exact ⟨package.states.values.get ⟨0, lengthPos⟩,
      package.states.values.get_mem ⟨0, lengthPos⟩⟩
  let joint := aggregate.glue choices
  let Realized := Core.DependentOwnerGlueCapacity.RealizedProjection
    aggregate.JointState
    (SimpleGraph (P13RemainderVertex
      (Node21Context active.data.previous))) aggregate.remainderGraph
  have realizedNonempty : Nonempty Realized :=
    ⟨Core.DependentOwnerGlueCapacity.realizedProjectionValue
      aggregate.remainderGraph joint⟩
  have cardPos : 0 < Nat.card Realized := by
    letI := realizedNonempty
    exact Nat.card_pos
  calc
    0 < Nat.card Realized := cardPos
    _ = active.output.stateCount := active.output.stateCountExact.symm

private theorem node52LogarithmicJointCapacity {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) :
    Node52LogarithmicJointCapacity active := by
  have logged := (node52NormalizationProfile active).logb_withError
    (node52StateCountPos active)
    (by change 0 < 2; norm_num)
    (by change 0 < max 1 (baselineSpineStateCount
      (Node21Context active.data.previous)); omega)
  dsimp [node52NormalizationProfile] at logged
  norm_num at logged
  exact logged

private theorem node52JointBudget {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual)
    {high : Node50High residual active} (node51 : Node51Output active high) :
    Node52JointBudget active := by
  have scaled := mul_le_mul_of_nonneg_left node51.remainderBits
    (show (0 : ℝ) ≤ node52CapacityExponent by positivity)
  change (node52CapacityExponent : ℝ) *
      ((((p13RemainderVertices
        (Node21Context active.data.previous)).card : ℝ) / 10) *
        Real.logb 2
          (Node21Context active.data.previous).G.object.input.vertices.card) ≤
    (node52CapacityExponent : ℝ) *
      Real.logb 2 active.output.stateCount at scaled
  have logged := node52LogarithmicJointCapacity active
  unfold Node52LogarithmicJointCapacity at logged
  unfold Node52JointBudget
  linarith

/-- Exact `[51] -> [52]` successor family. -/
abbrev Node52Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (Node50Bypass V) (Node50Active V)
    (@Node50High V) (@Node50Low V)
    (fun residual active high =>
      Node52Output (residual := residual) active high)
    residual

/-- Core maps only the literal node-[51] leaf; Erdős supplies the one local
joint-capacity certificate. -/
noncomputable def node52P13WindowRemainderAccounting {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node51Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node52Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuation
    (Bypass := Node50Bypass V)
    (Active := Node50Active V)
    (yes := @Node50High V)
    (no := @Node50Low V)
    (Output := fun residual active high =>
      Node51Output (residual := residual) active high)
    (Next := fun residual active high =>
      Node52Output (residual := residual) active high)
    fun _residual active _high node51 => {
      jointCapacity := node52JointCapacity active
      skeletonCapacity := node52SkeletonCapacity active
      normalizedJointCapacity := node52NormalizedJointCapacity active
      logarithmicJointCapacity := node52LogarithmicJointCapacity active
      jointBudget := node52JointBudget active node51
    }

noncomputable def runInitialThroughNode52 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode51 residual).mapYesStage
    node52P13WindowRemainderAccounting

/-- Symbolic cardinality transport performs no semantic scan. -/
def node52LocalChecks : Nat := 0

theorem node52LocalChecks_eq_zero : node52LocalChecks = 0 := rfl

#print axioms node52P13WindowRemainderAccounting
#print axioms runInitialThroughNode52

end Erdos64EG.Internal
