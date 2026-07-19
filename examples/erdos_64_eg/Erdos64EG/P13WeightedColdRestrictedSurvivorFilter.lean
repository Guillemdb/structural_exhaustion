import Erdos64EG.P13WeightedColdRestrictedD4D5
import Erdos64EG.P13WeightedColdRestrictedD6Projection
import StructuralExhaustion.Graph.SurplusResidualBudget

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Exact local survivor filter on `[152] -> [153]`

The node-[152] source has already been filtered to a weighted-cold,
ambient-cubic window by `P13WeightedColdCubicWindow`; this module does not
repeat that graph scan.  It specifies the single proof-carrying payload that
may cross the existing `[152] -> [153]` edge after the earlier surplus and
handoff incidences have been removed.  No alternative constructor is exposed
on that edge.

This is deliberately only the local part of the manuscript's surviving-cold
filter.  Every actual high result below now maps to a literal surplus slot at
the identical center, but the repository does not yet contain (1) an
occurrence-level multiplicity bound or distinct payment for all selected
corridors meeting that center, or (2) a branch-total producer proving that the combined ordinary
Type-B, decorated Type-B, and route-8 ledger contains every earlier handoff.
Consequently a negative D6 scan below means negative for the exact supplied
producer ledger; it is not promoted to global branch absence.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

/-- The restricted prefix package retains the literal node-[152]
branch-excess occurrence from which its component corridor was constructed. -/
theorem source_mem_node152_branchExcessSchedule :
    package.entry.source ∈ p13WeightedColdBranchExcessSchedule
      (ctx := ctx) (node21 := node21) :=
  package.entry.sourceMember

/-- The exact center-level surplus coverage for an actual high occurrence on
one stored corridor prefix.  The witness is a literal slot of the inherited
degree-surplus universe and retains membership in this prefix's support.  No
ambient vertex family is scanned. -/
def highOccurrenceSurplusSlot (stage : package.Stage)
    (high : WalkTypeAD5Projection.High (package.ambientPrefix stage)) :
    SurplusResidualBudget.RestrictedSlot ctx.G.object
      (fun center => center ∈
        WalkTypeAD5Projection.support (package.ambientPrefix stage)) :=
  SurplusResidualBudget.restrictedSlotOfHigh ctx.G.object
    (fun center => center ∈
      WalkTypeAD5Projection.support (package.ambientPrefix stage))
    high.center high.centerHigh high.centerMem

/-- The prefix slot has exactly the center returned by the graph-owned
high scan. -/
@[simp]
theorem highOccurrenceSurplusSlot_center (stage : package.Stage)
    (high : WalkTypeAD5Projection.High (package.ambientPrefix stage)) :
    (package.highOccurrenceSurplusSlot stage high).1.1 = high.center := rfl

/-- Every graph-owned high result on this literal prefix is covered by an
actual slot of the already inherited surplus ledger. -/
theorem highOccurrence_covered_by_surplusLedger (stage : package.Stage)
    (high : WalkTypeAD5Projection.High (package.ambientPrefix stage)) :
    ∃ slot : SurplusPortActivity.ExcessPortSlot ctx.G.object,
      slot.1 = high.center ∧
        high.center ∈ WalkTypeAD5Projection.support
          (package.ambientPrefix stage) :=
  ⟨(package.highOccurrenceSurplusSlot stage high).1, rfl,
    (package.highOccurrenceSurplusSlot stage high).2⟩

/-- No-high data and a high result on the same literal prefix are disjoint. -/
theorem noHigh_excludes_high (stage : package.Stage)
    (noHigh : WalkTypeAD5Projection.NoHigh (package.ambientPrefix stage)
      (minimumDegreeThree (ctx := ctx))) :
    WalkTypeAD5Projection.High (package.ambientPrefix stage) → False := by
  intro high
  have cubic := noHigh.ambientCubic high.center high.centerMem
  have highDegree := high.centerHigh
  omega

/-- Exact D5-negative reconstruction from the manuscript's semantic
subcubic condition at this stage. -/
theorem exists_d5Available_of_noHigh (stage : package.Stage)
    (noHigh : WalkTypeAD5Projection.NoHigh (package.ambientPrefix stage)
      (minimumDegreeThree (ctx := ctx))) :
    ∃ available : package.D5Available stage,
      package.runD5 stage = .d5 available := by
  rcases package.runD5_exhaustive stage with ⟨high, exactHigh⟩ | available
  · exact False.elim (package.noHigh_excludes_high stage noHigh high)
  · exact available

/-- Exact D6-negative reconstruction from absence in every support of the
single supplied produced-prior ledger. -/
theorem exists_d6Complete_of_outsideProducedSupports
    (ledger : package.PriorD6Ledger) (stage : package.Stage)
    (outside : ∀ occurrence : package.D6Key ledger,
      package.currentAmbientEndpoint stage ∉
        P13ProducedPriorSupportLedger.eventSupport
          (package.d6Entry ledger occurrence)) :
    ∃ complete : package.D6Complete ledger stage,
      package.runD6 ledger stage = .complete complete := by
  rcases package.runD6_total ledger stage with ⟨hit, exactHit⟩ | complete
  · exact False.elim (outside hit.hit.occurrence (by
      simpa [hit.eventExact] using hit.endpointMem))
  · exact complete

/-- Exact local survivor at one literal prefix. -/
structure LocallyClearStage (ledger : package.PriorD6Ledger)
    (stage : package.Stage) where
  available : package.D5Available stage
  d5Exact : package.runD5 stage = .d5 available
  priorComplete : package.D6Complete ledger stage
  d6Exact : package.runD6 ledger stage = .complete priorComplete

/-- Proof-carrying local survivor over every literal stage of the exact
restricted component path. -/
structure LocalCorridorSurvivor (ledger : package.PriorD6Ledger) where
  clear : ∀ stage : package.Stage, package.LocallyClearStage ledger stage

/-- The strongest theorem-only connector currently available on the original
`[152] -> [153]` edge.  It consumes the two semantic exclusions that the
original surviving branch must obtain from its already named sparse-surplus
and produced-handoff ledgers, then reconstructs the exact D5/D6 negative
runner payload at every literal stage.  No new result constructor is added. -/
theorem exists_localCorridorSurvivor_of_branchExclusions
    (prior : ProducedPriorD6State (ctx := ctx))
    (subcubic : ∀ stage : package.Stage,
      WalkTypeAD5Projection.NoHigh (package.ambientPrefix stage)
        (minimumDegreeThree (ctx := ctx)))
    (outsideProduced : ∀ stage : package.Stage,
      ∀ occurrence : package.D6Key prior,
        package.currentAmbientEndpoint stage ∉
          P13ProducedPriorSupportLedger.eventSupport
            (package.d6Entry prior occurrence)) :
    Nonempty (package.LocalCorridorSurvivor prior) := by
  classical
  refine ⟨⟨fun stage => ?_⟩⟩
  let d5Exists := package.exists_d5Available_of_noHigh stage (subcubic stage)
  let available := d5Exists.choose
  have d5Exact := d5Exists.choose_spec
  let d6Exists := package.exists_d6Complete_of_outsideProducedSupports
    prior stage (outsideProduced stage)
  let priorComplete := d6Exists.choose
  have d6Exact := d6Exists.choose_spec
  exact ⟨available, d5Exact, priorComplete, d6Exact⟩

/-- Exact no-high fact exposed by a locally surviving corridor. -/
theorem LocalCorridorSurvivor.noHigh
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (stage : package.Stage) :
    WalkTypeAD5Projection.NoHigh (package.ambientPrefix stage)
      (minimumDegreeThree (ctx := ctx)) :=
  (survivor.clear stage).available.noHigh

/-- Exact absence of every event in the supplied proof-carrying prior ledger.
This theorem intentionally makes no completeness claim about omitted producer
events. -/
theorem LocalCorridorSurvivor.outsideRecordedPriorSupports
    {ledger : package.PriorD6Ledger}
    (survivor : package.LocalCorridorSurvivor ledger)
    (stage : package.Stage) (key : package.D6Key ledger) :
    package.currentAmbientEndpoint stage ∉
      P13ProducedPriorSupportLedger.eventSupport
        (package.d6Entry ledger key) :=
  (survivor.clear stage).priorComplete.endpointOutside key

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
