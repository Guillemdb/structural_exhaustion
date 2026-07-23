import Hypostructure.PDE.Strategy

/-!# Generic PDE fast-track window schedules

This adapter turns an explicitly ordered finite window family into the
strategy-facing scale/window profile.  The active predicate and its decision
procedure remain analytic inputs supplied by the PDE application.
-/

namespace Hypostructure.PDE.FastTrack.WindowSchedule

universe uPrevious uWindow uModel uResult uValue uClass
universe uTargetCertificate uTerminal uPayload uLeft uRight

open Hypostructure

structure Profile (Previous : Type uPrevious) where
  Window : Previous -> Type uWindow
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Window previous))
  active : (previous : Previous) -> Window previous -> Prop
  activeDecidable : (previous : Previous) ->
    (window : Window previous) -> Decidable (active previous window)

def toStrategyProfile (profile : Profile Previous) :
    PDE.Strategy.ScaleWindowProfile Previous where
  Scale := profile.Window
  schedule := profile.schedule
  active := profile.active
  activeDecidable := profile.activeDecidable

def toObservableScan {M : PDE.LocalModel.{uModel}}
    (profile : Profile Previous)
    (state : Core.Residual.Query Previous
      (fun _previous => M.problem.Ambient))
    (observe : (previous : Previous) -> M.problem.Ambient ->
      profile.Window previous -> Bool) :
    PDE.Strategy.ObservableScan Previous M where
  state := state
  Item := profile.Window
  schedule := profile.schedule
  observe := observe

def toOrderedWitnessScan
    {Result : Previous -> Type uResult}
    (profile : Profile Previous)
    (witness : (previous : Previous) ->
      profile.Window previous -> Prop)
    (witnessDecidable : (previous : Previous) ->
      (window : profile.Window previous) ->
        Decidable (witness previous window))
    (run : (previous : Previous) -> Result previous)
    (exhaustive : (previous : Previous) ->
      (window : profile.Window previous) ->
      window ∈ (profile.schedule.read previous).values ->
      witness previous window ∨ ¬ witness previous window) :
    PDE.Strategy.OrderedWitnessScan Previous where
  Item := profile.Window
  schedule := profile.schedule
  witness := witness
  witnessDecidable := witnessDecidable
  Result := Result
  run := run
  exhaustive := exhaustive

def toResponseClassifier
    {Value : Previous -> Type uValue}
    {Class : Previous -> Type uClass}
    (profile : Profile Previous)
    (observe : (previous : Previous) ->
      profile.Window previous -> Value previous)
    (classify : (previous : Previous) -> Value previous -> Class previous)
    (exhaustive : (previous : Previous) ->
      (window : profile.Window previous) ->
      ∃ classValue : Class previous,
        classify previous (observe previous window) = classValue) :
    PDE.Strategy.ResponseClassifier Previous where
  Item := profile.Window
  Response := Value
  schedule := profile.schedule
  observe := observe
  Class := Class
  classify := classify
  exhaustive := exhaustive

def toCapacityLedger
    {Class : Previous -> Type uClass}
    (profile : Profile Previous)
    (classify : (previous : Previous) ->
      profile.Window previous -> Class previous)
    (contribution : (previous : Previous) ->
      profile.Window previous -> Nat)
    (capacity : (previous : Previous) -> Class previous -> Nat)
    (totalWithin : (previous : Previous) ->
      (window : profile.Window previous) ->
      contribution previous window ≤
        capacity previous (classify previous window)) :
    PDE.Strategy.CapacityLedger Previous where
  Item := profile.Window
  Class := Class
  schedule := profile.schedule
  classify := classify
  contribution := contribution
  capacity := capacity
  totalWithin := totalWithin

def toSupportLocalization
    (profile : Profile Previous)
    (localBudget : (previous : Previous) ->
      profile.Window previous -> Int)
    (selected : (previous : Previous) -> profile.Window previous)
    (selected_negative : (previous : Previous) ->
      localBudget previous (selected previous) < 0) :
    PDE.Strategy.SupportLocalization Previous where
  Cell := profile.Window
  schedule := profile.schedule
  localBudget := localBudget
  selected := selected
  selected_negative := selected_negative

def toTargetAvoidingContinuation
    {TargetCertificate : Previous -> Type uTargetCertificate}
    {AvoidingResidual : Previous -> Type uTargetCertificate}
    (target : (previous : Previous) ->
      TargetCertificate previous -> Prop)
    (avoiding : (previous : Previous) -> AvoidingResidual previous)
    (target_or_avoiding : (previous : Previous) ->
      (∃ certificate, target previous certificate) ∨
        Nonempty (AvoidingResidual previous)) :
    PDE.Strategy.TargetAvoidingContinuation Previous where
  TargetCertificate := TargetCertificate
  AvoidingResidual := AvoidingResidual
  target := target
  avoiding := avoiding
  target_or_avoiding := target_or_avoiding

def toRankBudgetSplit
    (rank budget threshold : Previous -> Nat)
    (high low : Previous -> Prop)
    (exhaustive : (previous : Previous) ->
      high previous ∨ low previous) :
    PDE.Strategy.RankBudgetSplit Previous where
  Rank := rank
  Budget := budget
  threshold := threshold
  high := high
  low := low
  exhaustive := exhaustive

def toClosedCodeExhaustion
    (profile : Profile Previous)
    (targetCode observedCode : (previous : Previous) ->
      profile.Window previous)
    (closed : (previous : Previous) ->
      observedCode previous =
        targetCode previous) :
    PDE.Strategy.ClosedCodeExhaustion Previous where
  Code := profile.Window
  schedule := profile.schedule
  targetCode := targetCode
  observedCode := fun previous _ => observedCode previous
  closed := fun previous => by
    simpa using closed previous

def toWorkProfile
    (checks work : Previous -> Nat) :
    PDE.Strategy.WorkProfile Previous where
  checks := checks
  work := work

def toWorkEvidence
    (checks work : Previous -> Nat)
    (checks_nonnegative : ∀ previous, 0 ≤ checks previous)
    (work_nonnegative : ∀ previous, 0 ≤ work previous) :
    PDE.Strategy.WorkEvidence Previous where
  checks := checks
  work := work
  checks_nonnegative := checks_nonnegative
  work_nonnegative := work_nonnegative

def toTerminalCertificate
    (kind : Core.Strategy.TerminalKind)
    (target avoiding : Previous -> Prop)
    (target_or_avoiding : ∀ previous,
      kind = .target ∧ target previous ∨
        kind = .avoiding ∧ avoiding previous) :
    PDE.Strategy.TerminalCertificate Previous where
  kind := kind
  target := target
  avoiding := avoiding
  target_or_avoiding := target_or_avoiding

def toClosedPipeline
    (pipeline : PDE.Strategy.Pipeline Previous)
    (terminal : (previous : Previous) ->
      PDE.Strategy.TerminalCertificate Previous)
    (terminal_closed : ∀ previous,
      (terminal previous).kind = .target ∨
        (terminal previous).kind = .avoiding) :
    PDE.Strategy.ClosedPipeline Previous where
  pipeline := pipeline
  terminal := terminal
  terminal_closed := terminal_closed

def toContract
    {Terminal : Type uTerminal}
    {Payload : Previous -> Terminal -> Type uPayload}
    (produce : (previous : Previous) ->
      Sigma (Payload previous))
    (exhaustive : (previous : Previous) ->
      Nonempty (Sigma (Payload previous))) :
    PDE.Strategy.StrategyContract Previous where
  Terminal := Terminal
  Payload := Payload
  produce := produce
  exhaustive := exhaustive

def toDichotomy
    {LeftPayload : Previous -> Type uLeft}
    {RightPayload : Previous -> Type uRight}
    (classify : (previous : Previous) ->
      Sum (LeftPayload previous) (RightPayload previous)) :
    PDE.Strategy.Dichotomy Previous where
  LeftPayload := LeftPayload
  RightPayload := RightPayload
  classify := classify

def toClosedDichotomy
    {LeftPayload : Previous -> Type uLeft}
    {RightPayload : Previous -> Type uRight}
    (classify : (previous : Previous) ->
      Sum (LeftPayload previous) (RightPayload previous))
    (leftClosed : (previous : Previous) ->
      LeftPayload previous -> Prop)
    (rightClosed : (previous : Previous) ->
      RightPayload previous -> Prop)
    (leftProof : (previous : Previous) ->
      match classify previous with
      | Sum.inl payload => leftClosed previous payload
      | Sum.inr _ => True)
    (rightProof : (previous : Previous) ->
      match classify previous with
      | Sum.inl _ => True
      | Sum.inr payload => rightClosed previous payload) :
    PDE.Strategy.ClosedDichotomy Previous where
  LeftPayload := LeftPayload
  RightPayload := RightPayload
  classify := classify
  leftClosed := leftClosed
  rightClosed := rightClosed
  leftProof := leftProof
  rightProof := rightProof

def activeValues (profile : Profile Previous) (previous : Previous) :
    List (profile.Window previous) := by
  letI : ∀ window, Decidable (profile.active previous window) :=
    profile.activeDecidable previous
  exact (profile.schedule.read previous).values.filter
    (fun window => decide (profile.active previous window))

theorem activeValues_mem
    (profile : Profile Previous) (previous : Previous)
    {window : profile.Window previous}
    (membership : window ∈ activeValues profile previous) :
    window ∈ (profile.schedule.read previous).values := by
  classical
  simp [activeValues] at membership ⊢
  exact membership.1

theorem activeValues_nodup
    (profile : Profile Previous) (previous : Previous) :
    (activeValues profile previous).Nodup := by
  classical
  exact (profile.schedule.read previous).nodup.filter _

noncomputable def activeSchedule (profile : Profile Previous) :
    Core.Residual.Query Previous
      (fun previous => Core.Finite.Enumeration (profile.Window previous)) :=
  profile.schedule.dependentMap fun previous _schedule => by
    letI : DecidableEq (profile.Window previous) := Classical.decEq _
    exact Core.Finite.Enumeration.ofNodupList
      (activeValues profile previous)
      (activeValues_nodup profile previous)

theorem activeSchedule_mem
    (profile : Profile Previous) (previous : Previous)
    {window : profile.Window previous}
    (index : Fin ((activeSchedule profile).read previous).card) :
    (((activeSchedule profile).read previous).get index) ∈
      (profile.schedule.read previous).values := by
  have membership :
      (((activeSchedule profile).read previous).get index) ∈
        activeValues profile previous := by
    change (((activeSchedule profile).read previous).get index) ∈
      ((activeSchedule profile).read previous).values
    exact ((activeSchedule profile).read previous).get_mem index
  exact activeValues_mem profile previous
    membership

theorem activeSchedule_active
    (profile : Profile Previous) (previous : Previous)
    (index : Fin ((activeSchedule profile).read previous).card) :
    profile.active previous
      (((activeSchedule profile).read previous).get index) := by
  classical
  have membership :
      (((activeSchedule profile).read previous).get index) ∈
        activeValues profile previous :=
    by
      change (((activeSchedule profile).read previous).get index) ∈
        ((activeSchedule profile).read previous).values
      exact ((activeSchedule profile).read previous).get_mem index
  simpa [activeValues] using (List.mem_filter.mp membership).2

theorem mem_activeSchedule_iff
    (profile : Profile Previous) (previous : Previous)
    (window : profile.Window previous) :
    window ∈ (activeSchedule profile |>.read previous).values ↔
      window ∈ (profile.schedule.read previous).values ∧
        profile.active previous window := by
  classical
  change window ∈ activeValues profile previous ↔ _
  simp [activeValues]

end Hypostructure.PDE.FastTrack.WindowSchedule
