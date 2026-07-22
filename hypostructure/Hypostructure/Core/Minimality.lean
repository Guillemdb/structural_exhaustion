import Hypostructure.Core.Context
import Hypostructure.Core.Closure
import Hypostructure.Core.Residual.Focus

/-!
# Generic subobject strict-progress minimality

The core owns the exact strict-progress contradiction pattern for a
minimality argument. A client supplies a family of certified subobjects,
how each subobject maps to the ambient object, a target transfer
principle, and a branch-state reconstruction. Core handles routing, work
accounting, and exact closure registration.
-/

namespace Hypostructure.Core.Minimality

universe uAmbient uBranch uMeasure uSubobject

/-- A target transfer map for certified subobjects. -/
structure TargetMonotone
    {P : Problem.{uAmbient, uBranch}}
    (Target : P.Ambient → Prop)
    (Subobject : P.Ambient → Type uSubobject)
    (toAmbient : {source : P.Ambient} → Subobject source → P.Ambient) where
  map : ∀ {source : P.Ambient} (subobject : Subobject source),
    Target (toAmbient subobject) → Target source

/-- Exact profile data for the strict-progress subobject minimality executor. -/
structure SubobjectMinimalityProfile
    {P : Problem.{uAmbient, uBranch}}
    (Target : P.Ambient → Prop)
    (progress : Progress.{uAmbient, uBranch, uMeasure} P)
    (Subobject : P.Ambient → Type uSubobject) where
  toAmbient : {source : P.Ambient} → Subobject source → P.Ambient
  smaller : ∀ {source : P.Ambient},
    (subobject : Subobject source) →
      progress.Smaller (toAmbient subobject) source
  targetMonotone :
    ∀ {source : P.Ambient} (subobject : Subobject source),
      Target (toAmbient subobject) → Target source
  stateOf : (ambient : P.Ambient) → P.BranchState ambient

/-- Result of proving no certified baseline-preserving subobject remains at the
top-level context. -/
structure NoSubobjectBaselineCertificate
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (ctx : Core.MinimalCounterexampleContext P Target progress) where
  private mk ::
  closure : ∀ (subobject : Subobject ctx.G),
    P.Baseline (profile.toAmbient subobject) →
      Core.Closure.Result False
  mechanism : ∀ (subobject : Subobject ctx.G)
    (baseline : P.Baseline (profile.toAmbient subobject)),
    (closure subobject baseline).mechanism =
      Core.Closure.Mechanism.strictProgress

namespace NoSubobjectBaselineCertificate

/-- A baseline subobject would contradict minimality. -/
theorem excludes
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {profile : SubobjectMinimalityProfile (P := P) Target progress Subobject}
    {ctx : Core.MinimalCounterexampleContext P Target progress}
    (certificate : NoSubobjectBaselineCertificate profile ctx)
    (subobject : Subobject ctx.G) :
    Not (P.Baseline (profile.toAmbient subobject)) := by
  intro baseline
  exact (certificate.closure subobject baseline).proof

end NoSubobjectBaselineCertificate

/-- Register strict-progress contradictions for all certified subobjects. -/
def deriveNoSubobjectBaseline
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (ctx : Core.MinimalCounterexampleContext P Target progress) :
  NoSubobjectBaselineCertificate profile ctx where
  closure := by
    intro subobject baseline
    let candidate : Core.AvoidingContext P Target :=
      Core.AvoidingContext.ofBranch
        ({
          G := profile.toAmbient subobject,
          baseline := baseline,
          state := profile.stateOf (profile.toAmbient subobject)
        } : Core.BranchContext P)
        (fun target => ctx.avoids (profile.targetMonotone subobject target))
    exact
      Core.Closure.Result.strictProgress
        { candidate := candidate
          smaller := profile.smaller subobject }
  mechanism := by
    intro subobject baseline
    rfl

/-- Focused output carrying the certificate on active predecessors. -/
abbrev FocusedNoSubobjectBaselineOutput
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (stage : Previous) (active : focus.Active stage) :=
  NoSubobjectBaselineCertificate profile (context.read stage active)

/-- Exact accumulated stage after focused minimality registration. -/
abbrev FocusedNoSubobjectBaselineStage
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress) :=
  Core.Residual.Focus.Stage focus
    (FocusedNoSubobjectBaselineOutput (P := P) (Target := Target)
      (progress := progress) (Subobject := Subobject) focus profile context)

/-- Counted focused execution of the generic subobject minimality pattern. -/
def executeFocusedNoSubobjectBaselineCounted
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (previous : Previous) :
    Core.Counted (FocusedNoSubobjectBaselineStage (P := P) (Target := Target)
      (progress := progress) (Subobject := Subobject) focus profile context) :=
  Core.Residual.Focus.runCounted focus
    (Output :=
      FocusedNoSubobjectBaselineOutput (P := P) (Target := Target)
        (progress := progress) (Subobject := Subobject) focus profile context)
    previous
    (fun active _checks _exact =>
      deriveNoSubobjectBaseline profile (context.read previous active))

@[simp] theorem executeFocusedNoSubobjectBaselineCounted_checks
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (previous : Previous) :
    (executeFocusedNoSubobjectBaselineCounted (P := P) (Target := Target)
      (progress := progress) (Subobject := Subobject) focus profile context
      previous).checks =
      focus.selectionBudget.checks previous := by
  simpa [executeFocusedNoSubobjectBaselineCounted] using
    (Core.Residual.Focus.runCounted_checks
      (profile := focus)
      (Output :=
        FocusedNoSubobjectBaselineOutput (P := P) (Target := Target)
          (progress := progress) (Subobject := Subobject) focus profile context)
      previous
      (onActive := fun active checks exact =>
        deriveNoSubobjectBaseline profile (context.read previous active)))

theorem executeFocusedNoSubobjectBaselineCounted_work_within
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress)
    (previous : Previous) :
    focus.selectionBudget.Within previous
      (executeFocusedNoSubobjectBaselineCounted (P := P) (Target := Target)
        (progress := progress) (Subobject := Subobject) focus profile context
        previous).checks :=
  by
    rw [executeFocusedNoSubobjectBaselineCounted_checks (P := P)
      (Target := Target) (progress := progress) (Subobject := Subobject)
      focus profile context previous]
    exact focus.selectionBudget.bounded previous

/-- Focused profile used by successor stages. -/
abbrev FocusedNoSubobjectBaselineProfile
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress) :=
  Core.Residual.Focus.successor focus
    (FocusedNoSubobjectBaselineOutput (P := P) (Target := Target)
      (progress := progress) (Subobject := Subobject) focus profile context)

/-- Read the exact certificate from the newest focused stage. -/
def focusedNoSubobjectBaselineQuery
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {Previous : Type uAmbient}
    (focus : Core.Residual.Focus.Profile Previous)
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (context : Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Core.MinimalCounterexampleContext P Target progress) :
    Core.Residual.Focus.ActiveQuery
      (FocusedNoSubobjectBaselineProfile (P := P) (Target := Target)
        (progress := progress) (Subobject := Subobject) focus profile context)
      (fun stage active =>
        FocusedNoSubobjectBaselineOutput (P := P) (Target := Target)
          (progress := progress) (Subobject := Subobject) focus profile
          context stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

end Hypostructure.Core.Minimality
