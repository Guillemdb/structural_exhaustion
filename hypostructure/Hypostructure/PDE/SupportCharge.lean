import Hypostructure.Core.SupportSplit
import Hypostructure.PDE.Model

/-!
# PDE support-charge specialization

PDE concentration, defect, and flux supports use the same finite signed
support contract as Graph.  The PDE adapter gives the carrier an analytic
meaning and leaves the high/low scan and outcome construction to Core.
-/

namespace Hypostructure.PDE.SupportCharge

universe uPrevious uModel uCarrier

open Hypostructure

abbrev Parameters := Core.SupportSplit.Parameters

abbrev Support (Carrier : Type uCarrier) :=
  Core.SupportSplit.Source Carrier

def chargeTotal {Carrier : Type uCarrier}
    (source : Support (Carrier := Carrier)) : Int :=
  (source.cells.values.map source.charge).sum

theorem chargeTotal_negative {Carrier : Type uCarrier}
    (source : Support (Carrier := Carrier)) :
    chargeTotal source < 0 :=
  source.negative

structure Profile {Previous : Type uPrevious}
    (M : PDE.LocalModel.{uModel}) where
  Carrier : Previous -> Type uCarrier
  source : Core.Residual.Query Previous
    (fun previous => Support (Carrier := Carrier previous))
  state : Core.Residual.Query Previous (fun _ => M.problem.Ambient)
  high : (previous : Previous) -> M.problem.Ambient ->
    Carrier previous -> Prop
  highDecidable : (previous : Previous) ->
    (object : M.problem.Ambient) ->
    (carrier : Carrier previous) -> Decidable (high previous object carrier)

def highSplit {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous))
    (previous : Previous) :
    Core.SupportSplit.HighSplit (profile.Carrier previous)
      (profile.source.read previous) where
  high := profile.high previous (profile.state.read previous)
  high_decidable := fun carrier =>
    profile.highDecidable previous (profile.state.read previous) carrier

def highValues {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous))
    (previous : Previous) : List (profile.Carrier previous) :=
  Core.SupportSplit.highValues (highSplit profile previous)

def hasHigh {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous))
    (previous : Previous) : Prop :=
  ∃ carrier, carrier ∈ highValues profile previous

def hasNoHigh {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous))
    (previous : Previous) : Prop :=
  highValues profile previous = []

theorem hasHigh_or_hasNoHigh {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous))
    (previous : Previous) :
    hasHigh profile previous ∨ hasNoHigh profile previous := by
  cases h : highValues profile previous with
  | nil => exact Or.inr h
  | cons carrier rest =>
      exact Or.inl ⟨carrier, by simp [h]⟩

noncomputable def hasHighDecidable {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous))
    (previous : Previous) : Decidable (hasHigh profile previous) := by
  classical
  unfold hasHigh
  infer_instance

noncomputable def hasNoHighDecidable {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous))
    (previous : Previous) : Decidable (hasNoHigh profile previous) := by
  classical
  unfold hasNoHigh
  infer_instance

abbrev Outcome {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous))
    (previous : Previous) :=
  Core.SupportSplit.Outcome (profile.Carrier previous)
    (profile.source.read previous) (highSplit profile previous)

def execute {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous))
    (previous : Previous) : Outcome profile previous :=
  Core.SupportSplit.execute (highSplit profile previous)

def outcomeQuery {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous)) :
    Core.Residual.Query Previous
      (fun previous => Outcome profile previous) :=
  profile.source.dependentMap fun previous _source =>
    execute profile previous

def highValuesQuery {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous)) :
    Core.Residual.Query Previous
      (fun previous => List (profile.Carrier previous)) :=
  profile.source.map fun previous _source =>
    highValues profile previous

noncomputable def hasHighDecisionQuery {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous)) :
    Core.Residual.Query Previous
      (fun previous => Decidable (hasHigh profile previous)) :=
  profile.source.dependentMap fun previous _source =>
    hasHighDecidable profile previous

noncomputable def hasNoHighDecisionQuery {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous)) :
    Core.Residual.Query Previous
      (fun previous => Decidable (hasNoHigh profile previous)) :=
  profile.source.dependentMap fun previous _source =>
    hasNoHighDecidable profile previous

end Hypostructure.PDE.SupportCharge
