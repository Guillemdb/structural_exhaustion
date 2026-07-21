import Hypostructure.Graph.CT7
import Hypostructure.PDE.CT7
import Hypostructure.Fixtures.GraphResponse
import Hypostructure.Fixtures.PDEBasics

/-!
# CT7 vertical-slice fixtures

The neutral fixture reaches all three terminals from one residual-owned
two-context schedule.  Graph and PDE fixtures instantiate the same executor
with glued graph targets and additive local/tail targets, respectively.
-/

namespace Hypostructure.Fixtures.CT7

namespace Neutral

inductive Mode where
  | realization
  | distinguishing
  | neutral
  deriving DecidableEq, Repr

def boolContexts : Core.Finite.Enumeration Bool :=
  Core.Finite.Enumeration.ofNodupList [false, true] (by decide)

theorem boolContexts_complete (context : Bool) :
    Exists fun index : Fin boolContexts.card =>
      context = boolContexts.get index := by
  cases context
  · exact ⟨⟨0, by decide⟩, rfl⟩
  · exact ⟨⟨1, by decide⟩, rfl⟩

def response (representative context : Bool) : Bool :=
  representative && context

abbrev responseSystem : Core.Response.System Bool :=
  Core.Response.System.ofDecodedContexts Bool Bool Bool response id

def realizes (mode : Mode) (representative context : Bool) : Prop :=
  mode = .realization ∧ representative = true ∧ context = true

def realizesDecidable (mode : Mode) (representative context : Bool) :
    Decidable (realizes mode representative context) := by
  unfold realizes
  infer_instance

structure Residual where
  mode : Mode
  representatives : Core.Response.Representatives Bool
  contexts : Core.Finite.Enumeration Bool
  contextsComplete : forall context, Exists fun index : Fin contexts.card =>
    context = contexts.get index

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def representativesQuery : Core.Residual.Query Previous fun _previous =>
    Core.Response.Representatives Bool :=
  residualQuery.map fun _previous residual => residual.representatives

def contextsQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous residual => residual.contexts

def spec : _root_.Hypostructure.CT7.Spec Previous where
  Representative := Bool
  system := responseSystem
  Realizes := fun previous representative context =>
    realizes (Core.Residual.residualOf previous).mode representative context

def capability : _root_.Hypostructure.CT7.Capability spec :=
  _root_.Hypostructure.CT7.Capability.ofExactContexts
    representativesQuery contextsQuery
    (by
      change DecidableEq Bool
      infer_instance)
    (fun previous coordinate =>
      realizesDecidable (Core.Residual.residualOf previous).mode
        (representativesQuery.read previous).source coordinate)
    (by
      intro previous context
      exact (Core.Residual.residualOf previous).contextsComplete context)

def residual : Mode -> Residual
  | .realization => {
      mode := .realization
      representatives := ⟨true, false⟩
      contexts := boolContexts
      contextsComplete := boolContexts_complete
    }
  | .distinguishing => {
      mode := .distinguishing
      representatives := ⟨false, true⟩
      contexts := boolContexts
      contextsComplete := boolContexts_complete
    }
  | .neutral => {
      mode := .neutral
      representatives := ⟨false, false⟩
      contexts := boolContexts
      contextsComplete := boolContexts_complete
    }

def previous (mode : Mode) : Previous :=
  Core.Residual.Ledger.initial (residual mode)

def realizationResult : _root_.Hypostructure.CT7.ExecutionResult spec capability :=
  _root_.Hypostructure.CT7.execute spec capability (previous .realization)

def distinguishingResult :
    _root_.Hypostructure.CT7.ExecutionResult spec capability :=
  _root_.Hypostructure.CT7.execute spec capability (previous .distinguishing)

def neutralResult : _root_.Hypostructure.CT7.ExecutionResult spec capability :=
  _root_.Hypostructure.CT7.execute spec capability (previous .neutral)

theorem realization_previous :
    realizationResult.stage.previous = previous .realization := rfl

theorem distinguishing_previous :
    distinguishingResult.stage.previous = previous .distinguishing := rfl

theorem neutral_previous :
    neutralResult.stage.previous = previous .neutral := rfl

theorem realization_terminal : realizationResult.terminal = .realization := rfl

theorem distinguishing_terminal :
    distinguishingResult.terminal = .distinguishing := rfl

theorem neutral_terminal : neutralResult.terminal = .neutral := rfl

theorem realization_checks : realizationResult.checks = 2 := rfl

theorem distinguishing_checks : distinguishingResult.checks = 4 := rfl

theorem neutral_checks : neutralResult.checks = 4 := rfl

theorem realization_trace : realizationResult.traceNodes =
    [.entry, .contextSchedule, .realizationSearch, .realizationTerminal] := rfl

theorem distinguishing_trace : distinguishingResult.traceNodes =
    [.entry, .contextSchedule, .realizationSearch, .distinctionSearch,
      .distinguishingTerminal] := rfl

theorem neutral_trace : neutralResult.traceNodes =
    [.entry, .contextSchedule, .realizationSearch, .distinctionSearch,
      .neutralTerminal] := rfl

theorem realization_verified :
    _root_.Hypostructure.CT7.OutcomeClaim realizationResult.outcome :=
  realizationResult.verified

theorem distinguishing_verified :
    _root_.Hypostructure.CT7.OutcomeClaim distinguishingResult.outcome :=
  distinguishingResult.verified

theorem neutral_verified :
    _root_.Hypostructure.CT7.OutcomeClaim neutralResult.outcome :=
  neutralResult.verified

theorem neutral_total : Exists fun result :
    _root_.Hypostructure.CT7.ExecutionResult spec capability =>
    result.stage.previous = previous .neutral ∧
    _root_.Hypostructure.CT7.OutcomeClaim result.outcome ∧
    result.traceNodes =
      _root_.Hypostructure.CT7.Trace.expectedNodes result.terminal ∧
    result.checks ≤ (capability.linearWorkBudget).coefficient *
      ((capability.linearWorkBudget).size (previous .neutral) + 1) ^
        (capability.linearWorkBudget).degree := by
  ct7_total (previous .neutral) using capability

end Neutral

namespace Graph

open Hypostructure.Fixtures.GraphResponse

structure Residual where
  representatives : Core.Response.Representatives
    (Hypostructure.Graph.BoundaryPiece boundary)
  contexts : Core.Finite.Enumeration Bool
  contextsComplete : forall context, Exists fun index : Fin contexts.card =>
    context = contexts.get index

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

noncomputable def representativesQuery :
    Core.Residual.Query Previous fun _previous =>
      Core.Response.Representatives
        (Hypostructure.Graph.BoundaryPiece boundary) :=
  residualQuery.map fun _previous residual => residual.representatives

def contextsQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous residual => residual.contexts

noncomputable abbrev spec :=
  _root_.Hypostructure.Graph.CT7.targetSpec Previous HasEdge hasEdgeDecidable
    Bool outsideByCode Bool id

noncomputable def capability : _root_.Hypostructure.CT7.Capability spec :=
  _root_.Hypostructure.Graph.CT7.targetCapabilityOfExactContexts
    hasEdgeDecidable representativesQuery contextsQuery (by
      intro previous context
      exact (Core.Residual.residualOf previous).contextsComplete context)

noncomputable def residual : Residual where
  representatives := ⟨edgePiece, emptyPiece⟩
  contexts := Neutral.boolContexts
  contextsComplete := Neutral.boolContexts_complete

noncomputable def previous : Previous :=
  Core.Residual.Ledger.initial residual

noncomputable def result :
    _root_.Hypostructure.CT7.ExecutionResult spec capability :=
  _root_.Hypostructure.CT7.execute spec capability previous

theorem result_previous : result.stage.previous = previous := rfl

theorem result_terminal : result.terminal = .realization := by
  apply result.terminal_realization_of_exists
  refine ⟨false, ?_⟩
  change HasEdge (Hypostructure.Graph.glue edgePiece
    (outsideByCode false))
  exact edgePiece_hasEdge false

theorem result_verified :
    _root_.Hypostructure.CT7.OutcomeClaim result.outcome :=
  result.verified

end Graph

namespace PDE

open Hypostructure.Fixtures.PDEBasics

abbrev M := FiniteCoordinates.model
abbrev Field := FiniteCoordinates.Field

local instance ambientAdd : Add M.problem.Ambient :=
  show Add FiniteCoordinates.Field from inferInstance

def Target (field : Field) : Prop := field 0 = 1

def decideTarget (field : Field) : Decidable (Target field) := by
  unfold Target
  infer_instance

def zeroField : Field := fun _index => 0

def oneField : Field := fun _index => 1

def tail (_context : Bool) : Field := zeroField

structure Residual where
  representatives : Core.Response.Representatives Field
  contexts : Core.Finite.Enumeration Bool
  contextsComplete : forall context, Exists fun index : Fin contexts.card =>
    context = contexts.get index

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def representativesQuery : Core.Residual.Query Previous fun _previous =>
    Core.Response.Representatives Field :=
  residualQuery.map fun _previous residual => residual.representatives

def contextsQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous residual => residual.contexts

noncomputable abbrev spec :=
  _root_.Hypostructure.PDE.CT7.targetSpec Previous M Target decideTarget Bool
    tail Bool id

noncomputable def capability : _root_.Hypostructure.CT7.Capability spec :=
  _root_.Hypostructure.PDE.CT7.targetCapabilityOfExactContexts M decideTarget
    representativesQuery contextsQuery (by
      intro previous context
      exact (Core.Residual.residualOf previous).contextsComplete context)

def residual : Residual where
  representatives := ⟨zeroField, oneField⟩
  contexts := Neutral.boolContexts
  contextsComplete := Neutral.boolContexts_complete

def previous : Previous :=
  Core.Residual.Ledger.initial residual

noncomputable def result :
    _root_.Hypostructure.CT7.ExecutionResult spec capability :=
  _root_.Hypostructure.CT7.execute spec capability previous

theorem result_previous : result.stage.previous = previous := rfl

theorem result_terminal : result.terminal = .distinguishing := rfl

theorem result_checks : result.checks = 3 := rfl

theorem result_verified :
    _root_.Hypostructure.CT7.OutcomeClaim result.outcome :=
  result.verified

end PDE

#print axioms Neutral.realization_terminal
#print axioms Neutral.realization_verified
#print axioms Neutral.distinguishing_terminal
#print axioms Neutral.distinguishing_verified
#print axioms Neutral.neutral_terminal
#print axioms Neutral.neutral_verified
#print axioms Neutral.neutral_total
#print axioms Graph.result_terminal
#print axioms Graph.result_verified
#print axioms PDE.result_terminal
#print axioms PDE.result_verified

end Hypostructure.Fixtures.CT7
