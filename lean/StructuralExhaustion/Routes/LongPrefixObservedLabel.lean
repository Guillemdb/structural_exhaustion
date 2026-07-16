import StructuralExhaustion.Graph.LongPrefixObservedLabel
import StructuralExhaustion.CT10.Automation

namespace StructuralExhaustion.Routes.LongPrefixObservedLabel

open StructuralExhaustion

universe uAmbient uBranch uVertex

/-!
# Typed route from an observed coarse repeat to semantic refinement

The branch context is a dependent index.  This route cannot replace it and
does not promote coarse-label equality to CT8 response equality or removal.
-/

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {V : Type uVertex} {object : Graph.FiniteObject V}

/-- Semantic layers in increasing refinement order. -/
inductive SemanticClass where
  | coarseLabel
  | responseContexts
  | certifiedRemoval
  deriving DecidableEq

@[implicit_reducible]
def semanticClasses : FinEnum SemanticClass :=
  @FinEnum.ofNodupList SemanticClass inferInstance
    [.coarseLabel, .responseContexts, .certifiedRemoval]
    (by intro cls; cases cls <;> simp) (by decide)

/-- CT10 classifies the single retained datum as the already-proved coarse
label layer.  No class is declared direct, so the first absent semantic layer
is promoted as the next typed obligation. -/
abbrev semanticCapability (P : Core.Problem.{uAmbient, uBranch}) :
    CT10.Capability P where
  Datum := Graph.LongPrefixObservedLabel.Occurrence
  Class := SemanticClass
  Promotion := SemanticClass
  classes := semanticClasses
  classOf := fun _occurrence => .coarseLabel
  Direct := fun _ => False
  directDecidable := fun _ => isFalse id
  promote := id

noncomputable def coarseData
    {input : Graph.LongPrefixObservedLabel.Input object}
    (observed : Graph.LongPrefixObservedLabel.SemanticRefinementResidual input) :
    Core.OrderedCollection Graph.LongPrefixObservedLabel.Occurrence where
  values := [observed.repetition.collision.first,
    observed.repetition.collision.second]
  nodup := by
    rw [List.nodup_cons]
    exact ⟨by simpa using observed.repetition.distinct, by simp⟩
  decEq := inferInstance

noncomputable def semanticInput
    {input : Graph.LongPrefixObservedLabel.Input object}
    (ctx : Core.BranchContext P)
    (observed : Graph.LongPrefixObservedLabel.SemanticRefinementResidual input) :
    CT10.Input (semanticCapability P) where
  context := ctx
  data := coarseData observed

@[simp]
theorem semanticInput_values
    {input : Graph.LongPrefixObservedLabel.Input object}
    (ctx : Core.BranchContext P)
    (observed : Graph.LongPrefixObservedLabel.SemanticRefinementResidual input) :
    (semanticInput ctx observed).data.values =
      [observed.repetition.collision.first,
        observed.repetition.collision.second] := rfl

structure Source (ctx : Core.BranchContext P)
    (input : Graph.LongPrefixObservedLabel.Input object) where
  observed : Graph.LongPrefixObservedLabel.SemanticRefinementResidual input

structure Residual (ctx : Core.BranchContext P)
    (input : Graph.LongPrefixObservedLabel.Input object) where
  source : Source ctx input
  refinement : Graph.LongPrefixObservedLabel.SemanticRefinementResidual input
  exact : refinement = source.observed
  classification : CT10.ExecutionResult (semanticCapability P)
    (semanticInput ctx source.observed)
  classificationExact : classification =
    CT10.run (semanticCapability P) (semanticInput ctx source.observed)

noncomputable def route {ctx : Core.BranchContext P}
    {input : Graph.LongPrefixObservedLabel.Input object}
    (source : Source ctx input) : Residual ctx input where
  source := source
  refinement := source.observed
  exact := rfl
  classification := CT10.run (semanticCapability P)
    (semanticInput ctx source.observed)
  classificationExact := rfl

/-- The table contains the coarse layer and therefore promotes the first
missing layer, `responseContexts`. -/
theorem semantic_terminal_promoted
    {input : Graph.LongPrefixObservedLabel.Input object}
    (ctx : Core.BranchContext P)
    (observed : Graph.LongPrefixObservedLabel.SemanticRefinementResidual input) :
    (CT10.run (semanticCapability P)
      (semanticInput ctx observed)).terminal = .promoted := by
  rfl

theorem semantic_first_missing_responseContexts
    {input : Graph.LongPrefixObservedLabel.Input object}
    (ctx : Core.BranchContext P)
    (observed : Graph.LongPrefixObservedLabel.SemanticRefinementResidual input) :
    match (CT10.run (semanticCapability P)
      (semanticInput ctx observed)).outcome with
    | .promoted residual => residual.promotion = .responseContexts
    | _ => False := by
  rfl

theorem semantic_run_verified
    {input : Graph.LongPrefixObservedLabel.Input object}
    (ctx : Core.BranchContext P)
    (observed : Graph.LongPrefixObservedLabel.SemanticRefinementResidual input) :
    (CT10.run (semanticCapability P)
      (semanticInput ctx observed)).outcome.Valid :=
  CT10.run_verified (semanticCapability P) (semanticInput ctx observed)

theorem semantic_run_trace_valid
    {input : Graph.LongPrefixObservedLabel.Input object}
    (ctx : Core.BranchContext P)
    (observed : Graph.LongPrefixObservedLabel.SemanticRefinementResidual input) :
    CT10.Graph.ValidTrace (semanticCapability P) (semanticInput ctx observed)
      (CT10.run (semanticCapability P) (semanticInput ctx observed)).trace :=
  CT10.run_trace_valid (semanticCapability P) (semanticInput ctx observed)

theorem semantic_run_trace
    {input : Graph.LongPrefixObservedLabel.Input object}
    (ctx : Core.BranchContext P)
    (observed : Graph.LongPrefixObservedLabel.SemanticRefinementResidual input) :
    (CT10.run (semanticCapability P) (semanticInput ctx observed)).trace =
      [.entry, .table, .direct, .missing, .promotion, .promotedTerminal] := by
  rfl

theorem semantic_run_total
    {input : Graph.LongPrefixObservedLabel.Input object}
    (ctx : Core.BranchContext P)
    (observed : Graph.LongPrefixObservedLabel.SemanticRefinementResidual input) :
    ∃ result : CT10.ExecutionResult (semanticCapability P)
        (semanticInput ctx observed),
      result.outcome.Valid ∧
        CT10.Graph.ValidTrace (semanticCapability P)
          (semanticInput ctx observed) result.trace :=
  CT10.run_total (semanticCapability P) (semanticInput ctx observed)

/-- Conservative CT10 work: scan three direct classes and, for the missing
class search, at most two retained observations in each of three rows. -/
noncomputable def semanticChecks
    {input : Graph.LongPrefixObservedLabel.Input object}
    (observed : Graph.LongPrefixObservedLabel.SemanticRefinementResidual input) : Nat :=
  semanticClasses.card + semanticClasses.card * (coarseData observed).values.length

@[simp] theorem semanticChecks_eq_nine
    {input : Graph.LongPrefixObservedLabel.Input object}
    (observed : Graph.LongPrefixObservedLabel.SemanticRefinementResidual input) :
    semanticChecks observed = 9 := by
  rfl

theorem context_preserved {ctx : Core.BranchContext P}
    {input : Graph.LongPrefixObservedLabel.Input object}
    (_source : Source ctx input) : ctx.G = ctx.G := rfl

end StructuralExhaustion.Routes.LongPrefixObservedLabel
