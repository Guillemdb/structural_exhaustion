import StructuralExhaustion.CT10.Automation
import StructuralExhaustion.Graph.InducedPathComponentD4D7OrCoarseRepeat

namespace StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u uAmbient uBranch

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {V : Type u} {object : FiniteObject V}
variable
  {input : InducedPathComponentD1D3Ledger.Input object}
  {anchorState : InducedPathComponentD1D3Ledger.State}
  {LengthOK : Nat → Prop}
  {lengthOKDecidable : DecidablePred LengthOK}

abbrev CoarseResidual
    (input : InducedPathComponentD1D3Ledger.Input object)
    (anchorState : InducedPathComponentD1D3Ledger.State)
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK) :=
  InducedPathComponentD4D7OrCoarseRepeat.CoarseRepeatResidual input
    anchorState LengthOK lengthOKDecidable

/-! ## Exact coarse-pair CT10 consumer -/

abbrev PairClass
    (source : CoarseResidual input anchorState LengthOK lengthOKDecidable) :=
  {stub : InducedPathComponentD1D3Ledger.Stub input //
    stub = source.repetition.collision.first.1 ∨
      stub = source.repetition.collision.second.1}

noncomputable def firstClass
    (source : CoarseResidual input anchorState LengthOK lengthOKDecidable) :
    PairClass source :=
  ⟨source.repetition.collision.first.1, Or.inl rfl⟩

noncomputable def secondClass
    (source : CoarseResidual input anchorState LengthOK lengthOKDecidable) :
    PairClass source :=
  ⟨source.repetition.collision.second.1, Or.inr rfl⟩

@[implicit_reducible]
noncomputable def pairClasses
    (source : CoarseResidual input anchorState LengthOK lengthOKDecidable) :
    FinEnum (PairClass source) := by
  classical
  apply FinEnum.ofNodupList [firstClass source, secondClass source]
  · intro cls
    rcases cls.property with first | second
    · have equal : cls = firstClass source := Subtype.ext first
      simp [equal]
    · have equal : cls = secondClass source := Subtype.ext second
      simp [equal]
  · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, and_true]
    intro equal
    apply source.distinct
    exact congrArg Subtype.val equal

structure CoarsePromotion
    (source : CoarseResidual input anchorState LengthOK lengthOKDecidable) where
  sourceExact : CoarseResidual input anchorState LengthOK lengthOKDecidable
  sourceExact_eq : sourceExact = source
  missingClass : PairClass source

noncomputable def coarseCapability (P : Core.Problem)
    (source : CoarseResidual input anchorState LengthOK lengthOKDecidable) :
    CT10.Capability P where
  Datum := PairClass source
  Class := PairClass source
  Promotion := CoarsePromotion source
  classes := pairClasses source
  classOf := id
  Direct := fun _ => False
  directDecidable := fun _ => isFalse id
  promote := fun cls => ⟨source, rfl, cls⟩

noncomputable def coarseData
    (source : CoarseResidual input anchorState LengthOK lengthOKDecidable) :
    Core.OrderedCollection (PairClass source) where
  values := []
  nodup := by simp
  decEq := (pairClasses source).decEq

noncomputable def coarseInput (P : Core.Problem) (ctx : Core.BranchContext P)
    (source : CoarseResidual input anchorState LengthOK lengthOKDecidable) :
    CT10.Input (coarseCapability P source) where
  context := ctx
  data := coarseData source

noncomputable def coarseExecution (P : Core.Problem)
    (ctx : Core.BranchContext P)
    (source : CoarseResidual input anchorState LengthOK lengthOKDecidable) :=
  CT10.run (coarseCapability P source) (coarseInput P ctx source)

theorem coarse_context_preserved (ctx : Core.BranchContext P)
    (source : CoarseResidual input anchorState LengthOK lengthOKDecidable) :
    (coarseInput P ctx source).context = ctx := rfl

theorem coarse_valid (ctx : Core.BranchContext P)
    (source : CoarseResidual input anchorState LengthOK lengthOKDecidable) :
    (coarseExecution P ctx source).outcome.Valid :=
  CT10.run_verified (coarseCapability P source) (coarseInput P ctx source)

/-- With no graph-derived D4--D7 datum, CT10 promotes the first class of the
actual retained pair as the exact next refinement obligation. -/
theorem coarse_terminal_promoted (ctx : Core.BranchContext P)
    (source : CoarseResidual input anchorState LengthOK lengthOKDecidable) :
    (coarseExecution P ctx source).terminal = .promoted := by
  rfl

theorem coarse_trace_promoted (ctx : Core.BranchContext P)
    (source : CoarseResidual input anchorState LengthOK lengthOKDecidable) :
    (coarseExecution P ctx source).trace =
      [.entry, .table, .direct, .missing, .promotion, .promotedTerminal] := by
  rfl

theorem coarse_trace_valid (ctx : Core.BranchContext P)
    (source : CoarseResidual input anchorState LengthOK lengthOKDecidable) :
    CT10.Graph.ValidTrace (coarseCapability P source) (coarseInput P ctx source)
      (coarseExecution P ctx source).trace :=
  CT10.run_trace_valid (coarseCapability P source) (coarseInput P ctx source)

theorem coarse_total (ctx : Core.BranchContext P)
    (source : CoarseResidual input anchorState LengthOK lengthOKDecidable) :
    ∃ result : CT10.ExecutionResult (coarseCapability P source)
        (coarseInput P ctx source),
      result.outcome.Valid ∧
        CT10.Graph.ValidTrace (coarseCapability P source)
          (coarseInput P ctx source) result.trace :=
  CT10.run_total (coarseCapability P source) (coarseInput P ctx source)

def coarseHandoffId := "Graph.residual.d4d7.coarseRepeat->CT10"
theorem coarse_handoff_provenance : coarseHandoffId =
    "Graph.residual.d4d7.coarseRepeat->CT10" := rfl

def coarseHandoffContract : Core.SemanticHandoffContract where
  handoffId := coarseHandoffId
  sourceResidualKind := "Graph.residual.d4d7.coarseRepeat"
  targetConsumerId := "CT10.executableInterface"
  discovery := "exact retained collision pair"
  consumerInputConstructor :=
    "StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.coarseInput"
  soundnessTheorem :=
    "StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.coarse_valid"
  contextPreservationTheorem :=
    "StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.coarse_context_preserved"
  provenanceTheorem :=
    "StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.coarse_handoff_provenance"

/-! ## Exact first-missing-row CT10 consumer -/

abbrev MissingResidual
    (input : InducedPathComponentD1D3Ledger.Input object) :=
  InducedPathComponentD4D7OrCoarseRepeat.FirstMissingReconstruction input

@[implicit_reducible]
noncomputable def actualStubClasses
    (input : InducedPathComponentD1D3Ledger.Input object) :
    FinEnum (InducedPathComponentD1D3Ledger.Stub input) := by
  classical
  apply FinEnum.ofNodupList (InducedPathComponentD1D3Ledger.stubs input)
  · intro stub
    simpa [InducedPathComponentD1D3Ledger.stubs]
  · exact InducedPathComponentD1D3Ledger.stubs_nodup input

structure MissingPromotion (source : MissingResidual input) where
  sourceExact : MissingResidual input
  sourceExact_eq : sourceExact = source
  missingClass : InducedPathComponentD1D3Ledger.Stub input

noncomputable def missingCapability (P : Core.Problem)
    (source : MissingResidual input) : CT10.Capability P where
  Datum := InducedPathComponentD1D3Ledger.Stub input
  Class := InducedPathComponentD1D3Ledger.Stub input
  Promotion := MissingPromotion source
  classes := actualStubClasses input
  classOf := id
  Direct := fun cls => cls = source.scan.row
  directDecidable := fun _ => Classical.propDecidable _
  promote := fun cls => ⟨source, rfl, cls⟩

noncomputable def missingInput (P : Core.Problem) (ctx : Core.BranchContext P)
    (source : MissingResidual input) :
    CT10.Input (missingCapability P source) where
  context := ctx
  data := (actualStubClasses input).toOrderedCollection

noncomputable def missingExecution (P : Core.Problem)
    (ctx : Core.BranchContext P) (source : MissingResidual input) :=
  CT10.run (missingCapability P source) (missingInput P ctx source)

theorem missing_context_preserved (ctx : Core.BranchContext P)
    (source : MissingResidual input) :
    (missingInput P ctx source).context = ctx := rfl

set_option maxHeartbeats 800000 in
theorem missing_valid (ctx : Core.BranchContext P)
    (source : MissingResidual input) :
    (missingExecution P ctx source).outcome.Valid :=
  CT10.run_verified (missingCapability P source) (missingInput P ctx source)

set_option maxHeartbeats 800000 in
theorem missing_trace_valid (ctx : Core.BranchContext P)
    (source : MissingResidual input) :
    CT10.Graph.ValidTrace (missingCapability P source) (missingInput P ctx source)
      (missingExecution P ctx source).trace :=
  CT10.run_trace_valid (missingCapability P source) (missingInput P ctx source)

set_option maxHeartbeats 800000 in
theorem missing_total (ctx : Core.BranchContext P)
    (source : MissingResidual input) :
    ∃ result : CT10.ExecutionResult (missingCapability P source)
        (missingInput P ctx source),
      result.outcome.Valid ∧
        CT10.Graph.ValidTrace (missingCapability P source)
          (missingInput P ctx source) result.trace :=
  CT10.run_total (missingCapability P source) (missingInput P ctx source)

def missingHandoffId := "Graph.residual.d4d7.firstMissing->CT10"
theorem missing_handoff_provenance : missingHandoffId =
    "Graph.residual.d4d7.firstMissing->CT10" := rfl

def missingHandoffContract : Core.SemanticHandoffContract where
  handoffId := missingHandoffId
  sourceResidualKind := "Graph.residual.d4d7.firstMissing"
  targetConsumerId := "CT10.executableInterface"
  discovery := "exact first missing row in the retained schedule"
  consumerInputConstructor :=
    "StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.missingInput"
  soundnessTheorem :=
    "StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.missing_valid"
  contextPreservationTheorem :=
    "StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.missing_context_preserved"
  provenanceTheorem :=
    "StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.missing_handoff_provenance"

def handoffContracts : List Core.SemanticHandoffContract :=
  [coarseHandoffContract, missingHandoffContract]

/-- Conservative work for either mutually exclusive route: three checks
cover the two-class coarse promotion, while the first-missing consumer scans
at most the actual retained stub schedule. -/
noncomputable def visibleChecks
    (input : InducedPathComponentD1D3Ledger.Input object) : Nat :=
  3 + (InducedPathComponentD1D3Ledger.stubs input).length

theorem visibleChecks_polynomial
    (input : InducedPathComponentD1D3Ledger.Input object) :
    visibleChecks input ≤
      InducedPathComponentD1D3Ledger.localScale input + 3 := by
  unfold visibleChecks InducedPathComponentD1D3Ledger.localScale
  omega

end StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10
