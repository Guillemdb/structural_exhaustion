import Erdos64EG.Future.P13WeightedColdRestrictedF1Completion
import StructuralExhaustion.Core.FinitePrioritizedContinuation

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

@[implicit_reducible] noncomputable def p13F1Offsets : FinEnum (Fin 13) :=
  inferInstance

/-- Paper-faithful F1 predicate at one prefix stage: at least one of the
thirteen literal offsets closes there. -/
def F1Stage (stage : package.Stage) : Prop :=
  ∃ offset : Fin 13, package.F1At (stage, offset)

noncomputable def f1StageDecidable (stage : package.Stage) :
    Decidable (package.F1Stage stage) := by
  unfold F1Stage
  letI : ∀ offset : Fin 13, Decidable (package.F1At (stage, offset)) :=
    fun offset => package.f1AtDecidable (stage, offset)
  infer_instance

/-- Canonical first offset within one fixed stage.  This is the inner local
scan used before F2 is inspected at that same stage. -/
noncomputable def f1OffsetScan (stage : package.Stage) :=
  Core.FiniteSearch.first p13F1Offsets
    (fun offset => package.F1At (stage, offset))
    (fun offset => package.f1AtDecidable (stage, offset))

noncomputable def firstOffsetHit (stage : package.Stage)
    (existsHit : package.F1Stage stage) :
    Core.FiniteSearch.FirstHit p13F1Offsets.orderedValues
      (fun offset => package.F1At (stage, offset)) := by
  have hasHit := Core.FiniteSearch.first_complete p13F1Offsets
    (fun offset => package.F1At (stage, offset))
    (fun offset => package.f1AtDecidable (stage, offset)) existsHit
  cases equation : package.f1OffsetScan stage with
  | found hit => exact hit
  | absent none =>
      change (package.f1OffsetScan stage).HasHit at hasHit
      rw [equation] at hasHit
      exact False.elim hasHit

/-- Fixed F1 payload type used by the generic stage-major runner.  It retains
the exact stage, canonical first offset (including its clean offset prefix),
and literal dyadic cycle. -/
def F1StageData : Type u :=
  Sigma fun stage : package.Stage =>
    Sigma fun _hit : Core.FiniteSearch.FirstHit
      p13F1Offsets.orderedValues
      (fun offset => package.F1At (stage, offset)) =>
        CycleWithLength ctx.G.object.graph PowerOfTwoLength

noncomputable def f1StageData (stage : package.Stage)
    (proof : package.F1Stage stage) : package.F1StageData := by
  let hit := package.firstOffsetHit stage proof
  exact ⟨stage, hit,
    InducedPathRestrictedPrefixCompletion.cycleOfCompletion package.input
      PowerOfTwoLength stage hit.value hit.holds⟩

theorem f1StageData_stage (stage : package.Stage)
    (proof : package.F1Stage stage) :
    (package.f1StageData stage proof).1 = stage := rfl

theorem f1StageData_no_earlier_offset (stage : package.Stage)
    (proof : package.F1Stage stage) :
    ∀ offset ∈ (package.f1StageData stage proof).2.1.before,
      ¬package.F1At (stage, offset) :=
  (package.f1StageData stage proof).2.1.beforeAbsent

/-- The missing graph/route-owned part of C153.  An eventual constructor must
instantiate these predicates and payloads with literal two-boundary pieces,
proof-selected compatible contexts, CT3 replacement data, existing F4 ledger
keys, and the terminal/repeated-state F5 germ.  This alias is deliberately not
an Erdős semantic theorem. -/
abbrev RequiredF2F5Semantics :=
  Core.FinitePrioritizedContinuation.LaterSemantics package.Stage package.F1Stage

/-- Exact stage-major profile prescribed by the paper.  At each prefix it
checks the local thirteen-offset F1 predicate, then F2, F3, and F4.  F5 is
constructed by the generic runner only after every stage is clear. -/
noncomputable def continuationProfile
    (later : package.RequiredF2F5Semantics) :
    Core.FiniteFirstFailure.Profile Unit package.Stage :=
  Core.FinitePrioritizedContinuation.profile package.stages
    package.F1Stage package.f1StageDecidable package.F1StageData
    package.f1StageData later

noncomputable def runContinuation
    (later : package.RequiredF2F5Semantics) :=
  (package.continuationProfile later).run ()

theorem runContinuation_total
    (later : package.RequiredF2F5Semantics) :
    (∃ hit data, package.runContinuation later = .first hit data) ∨
    (∃ noEvent data, package.runContinuation later = .germ noEvent data) :=
  (package.continuationProfile later).run_total ()

/-- Any F1 constructor selected by the continuation contains a literal cycle;
the runner cannot manufacture it from an arithmetic bit. -/
theorem f1_payload_has_literal_cycle
    (data : package.F1StageData) :
    Nonempty (CycleWithLength ctx.G.object.graph PowerOfTwoLength) :=
  ⟨data.2.2⟩

theorem continuation_first_prefix_clear
    (later : package.RequiredF2F5Semantics)
    (hit : Core.FiniteSearch.FirstHit package.stages.values
      ((package.continuationProfile later).Event ())) :
    ∀ stage, stage ∈ hit.before →
      ¬(package.continuationProfile later).Event () stage :=
  (package.continuationProfile later).first_prefix_clear () hit

theorem continuation_checks
    (later : package.RequiredF2F5Semantics) :
    (package.continuationProfile later).checks () =
      package.stages.values.length := rfl

/-- Exact nested scheduling reflection: outer order is the stored prefix order
and the inner F1 order is the canonical `Fin 13` order at that one stage. -/
theorem stage_major_offset_order
    (later : package.RequiredF2F5Semantics)
    (stage : package.Stage) :
    ((package.continuationProfile later).stages ()).values =
        package.stages.values ∧
      package.f1OffsetScan stage =
        Core.FiniteSearch.first p13F1Offsets
          (fun offset => package.F1At (stage, offset))
          (fun offset => package.f1AtDecidable (stage, offset)) :=
  ⟨rfl, rfl⟩

theorem f1_offset_order_length : p13F1Offsets.orderedValues.length = 13 := by
  rw [FinEnum.orderedValues_length, FinEnum.card_eq_fintypeCard]
  exact Fintype.card_fin 13

theorem f1_offset_order_exact :
    p13F1Offsets.orderedValues = List.finRange 13 := rfl

/-- Top-level local predicate-call bound: at most thirteen F1 offset tests,
then one call to each of the F2, F3 and F4 semantic predicates, per stored
prefix stage.  The missing semantic producer must separately bound the cost
of those three predicate calls. -/
noncomputable def continuationLocalPredicateCallsUpper : Nat :=
  package.stages.values.length * 16

theorem continuationLocalPredicateCallsUpper_eq :
    package.continuationLocalPredicateCallsUpper =
      package.stages.values.length * (13 + 3) := by
  simp [continuationLocalPredicateCallsUpper]

/-- The older product scan remains available only as an auxiliary global F1
audit.  It is not used by `continuationProfile`, because doing so would let a
later F1 outrank an earlier F2. -/
theorem auxiliary_product_scan_checks :
    package.f1Checks = package.checks * 13 :=
  package.f1Checks_eq

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
