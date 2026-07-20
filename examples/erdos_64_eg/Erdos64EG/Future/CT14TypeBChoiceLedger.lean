import Erdos64EG.Future.CT12TypeBResolution

namespace Erdos64EG.Internal

open StructuralExhaustion
open scoped BigOperators

universe u

/-!
# Exact nonnegative ledger for a full Type B choice

Each local candidate has one fixed quarter-unit term and one selected-item
term. In the certificate branch the fixed term is the center charge. In the
positive branch it is window credit minus the exact fan deficit. Candidate
validity proves the resulting balance nonnegative. A B2 choice therefore has
nonnegative total local balance by literal finite summation.
-/

namespace TypeBLocalEntry

noncomputable def fixedQuarterBalance
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}} :
    TypeBLocalEntry ctx → Int
  | .certificate marked =>
      Graph.CertificateClosedFanCandidate.Profile.centerQuarterCharge
        marked.chargeProfile
  | .positive entry =>
      (Graph.HybridFanIncidence.windowQuarterCredit
        (base := fixedPackedInput ctx) (object := ctx.G.object)
        (baseline := (packedStaticInput.fixedContext ctx).baseline)
        (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned
          entry.assignedDecidable) : Int) -
      Graph.FanClosedPortMass.deficitNumerator
        (ctx.G.object.degree entry.fan.center)
        (Graph.HybridFanIncidence.closedMembers
          (object := ctx.G.object) (center := entry.fan.center)
          (p13FanWindowProfile ctx entry.Assigned
            entry.assignedDecidable)).card

noncomputable def selectedQuarterCredit
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : TypeBLocalEntry ctx)
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex)
    (candidate : (entry.selectionProfile reserve).Candidate) : Int :=
  ∑ item ∈ candidate.1, (entry.selectionProfile reserve).weight item

noncomputable def localQuarterBalance
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : TypeBLocalEntry ctx)
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex)
    (candidate : (entry.selectionProfile reserve).Candidate) : Int :=
  entry.fixedQuarterBalance + entry.selectedQuarterCredit reserve candidate

/-- Candidate validity is exactly nonnegativity of the corresponding local
Type B quarter-unit balance. -/
theorem localQuarterBalance_nonnegative
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : TypeBLocalEntry ctx)
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex)
    (candidate : (entry.selectionProfile reserve).Candidate) :
    0 ≤ entry.localQuarterBalance reserve candidate := by
  have payment := (entry.selectionProfile reserve).payment candidate
  cases entry with
  | certificate marked =>
      change -Graph.CertificateClosedFanCandidate.Profile.centerQuarterCharge
          marked.chargeProfile ≤ _ at payment
      change 0 ≤
        Graph.CertificateClosedFanCandidate.Profile.centerQuarterCharge
          marked.chargeProfile +
        ∑ item ∈ candidate.1,
          ((TypeBLocalEntry.certificate marked).selectionProfile reserve).weight item
      omega
  | positive positiveEntry =>
      change Graph.HybridFanIncidence.remainingNonWindowDemand
          (base := fixedPackedInput ctx) (object := ctx.G.object)
          (baseline := (packedStaticInput.fixedContext ctx).baseline)
          (center := positiveEntry.fan.center)
          (p13FanWindowProfile ctx positiveEntry.Assigned
            positiveEntry.assignedDecidable) ≤ _ at payment
      change 0 ≤
        (Graph.HybridFanIncidence.windowQuarterCredit
          (base := fixedPackedInput ctx) (object := ctx.G.object)
          (baseline := (packedStaticInput.fixedContext ctx).baseline)
          (center := positiveEntry.fan.center)
          (p13FanWindowProfile ctx positiveEntry.Assigned
            positiveEntry.assignedDecidable) : Int) -
        Graph.FanClosedPortMass.deficitNumerator
          (ctx.G.object.degree positiveEntry.fan.center)
          (Graph.HybridFanIncidence.closedMembers
            (object := ctx.G.object) (center := positiveEntry.fan.center)
            (p13FanWindowProfile ctx positiveEntry.Assigned
              positiveEntry.assignedDecidable)).card +
        ∑ item ∈ candidate.1,
          ((TypeBLocalEntry.positive positiveEntry).selectionProfile reserve).weight item
      unfold Graph.HybridFanIncidence.remainingNonWindowDemand at payment
      omega

end TypeBLocalEntry

namespace TypeBAssignedSupport

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (support : TypeBAssignedSupport ctx)

noncomputable def chosenCandidate
    {selected : List support.Demand}
    (choice : support.completionProfile.Choice selected)
    (demand : {demand // demand ∈ selected}) :
    (support.selectionProfile demand.1).Candidate := by
  change support.Candidate demand.1
  exact choice.entry demand

noncomputable def chosenLocalCandidate
    {selected : List support.Demand}
    (choice : support.completionProfile.Choice selected)
    (demand : {demand // demand ∈ selected}) :
    ((support.entry demand.1).selectionProfile support.reserve).Candidate := by
  change (support.selectionProfile demand.1).Candidate
  exact support.chosenCandidate choice demand

noncomputable def totalLocalQuarterBalance
    {selected : List support.Demand}
  (choice : support.completionProfile.Choice selected) : Int :=
  (selected.attach.map fun demand =>
    TypeBLocalEntry.localQuarterBalance (support.entry demand.1)
      support.reserve (support.chosenLocalCandidate choice demand)).sum

/-- Pairwise carrier disjointness is retained by the choice, while local
validity alone proves the exact sum of its B1 balances nonnegative. -/
theorem totalLocalQuarterBalance_nonnegative
    {selected : List support.Demand}
    (choice : support.completionProfile.Choice selected) :
    0 ≤ support.totalLocalQuarterBalance choice := by
  unfold totalLocalQuarterBalance
  let balances : List Int := selected.attach.map fun demand =>
    TypeBLocalEntry.localQuarterBalance (support.entry demand.1)
      support.reserve (support.chosenLocalCandidate choice demand)
  have pointwise : ∀ balance, balance ∈ balances → 0 ≤ balance := by
    intro balance member
    rcases List.mem_map.mp member with ⟨demand, _demandMem, rfl⟩
    exact TypeBLocalEntry.localQuarterBalance_nonnegative
      (support.entry demand.1) support.reserve
      (support.chosenLocalCandidate choice demand)
  change 0 ≤ balances.sum
  have sum_nonnegative : ∀ values : List Int,
      (∀ value, value ∈ values → 0 ≤ value) → 0 ≤ values.sum := by
    intro values nonnegative
    induction values with
    | nil => simp
    | cons head tail ih =>
        simp only [List.sum_cons]
        exact Int.add_nonneg
          (nonnegative head (by simp))
          (ih (fun value member => nonnegative value (by simp [member])))
  exact sum_nonnegative balances pointwise

end TypeBAssignedSupport

/-- Same-ledger theorem extension attaching the exact local-balance sum to
the completed CT12 residual. -/
abbrev VerifiedTypeBChoiceLedgerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedTypeBResolutionPrefix ctx)
    (fun _previous => ∀ (support : TypeBAssignedSupport ctx)
      (choice : support.completionProfile.FullChoice),
      0 ≤ support.totalLocalQuarterBalance choice)

noncomputable def verifiedTypeBChoiceLedgerPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTypeBResolutionPrefix ctx) :
    VerifiedTypeBChoiceLedgerPrefix ctx :=
  ⟨previous, fun support choice =>
    support.totalLocalQuarterBalance_nonnegative choice⟩

theorem exists_verifiedTypeBChoiceLedgerPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedTypeBChoiceLedgerPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedTypeBResolutionPrefix object baseline avoids
  exact ⟨ctx, verifiedTypeBChoiceLedgerPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
