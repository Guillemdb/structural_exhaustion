import Hypostructure.PDE.NavierStokes.Basic
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query
import Hypostructure.PDE.Strategy

/-!# Analytic registration surface for a 2D Navier--Stokes regularity proof

This module does not claim regularity.  It records the finite represented
observables and the analytic certificates a proof must provide before the
generic PDE strategies and CTs can execute.
-/

namespace Hypostructure.PDE.NavierStokes.Regularity

open Hypostructure
open Hypostructure.PDE.NavierStokes

structure Profile where
  field : Field
  windows : Core.Finite.Enumeration Window
  localRegular : Window -> Prop
  localRegularDecidable : (window : Window) ->
    Decidable (localRegular window)
  localEquation : ∀ window,
    RepresentedClassicalOn field (Window.region window)
  energy : Window -> Real
  enstrophy : Window -> Real
  flux : Window -> Real
  windowCover : ∀ z, z ∈ field.domain ->
    ∃ window ∈ windows.values, z ∈ Window.region window
  energyNonnegative : ∀ window, 0 ≤ energy window
  enstrophyNonnegative : ∀ window, 0 ≤ enstrophy window
  localEnergyBound : ∀ window, localRegular window -> energy window < 1
  localEnstrophyBound : ∀ window, localRegular window -> enstrophy window < 1
  fluxBound : ∀ window, localRegular window -> flux window ≤ energy window

def Target (profile : Profile) : Prop :=
  ∀ z, z ∈ profile.field.domain ->
    ContDiffAt Real ⊤ profile.field.velocity z

def LocalTarget (profile : Profile) (window : Window) : Prop :=
  ∀ z, z ∈ Window.region window ->
    ContDiffAt Real ⊤ profile.field.velocity z

structure CompactnessCertificate (profile : Profile) where
  extracted : Profile
  sameField : extracted.field = profile.field
  convergent : Prop
  preservesEnergy : ∀ window,
    extracted.energy window ≤ profile.energy window
  preservesEnstrophy : ∀ window,
    extracted.enstrophy window ≤ profile.enstrophy window

structure InvarianceCertificate (profile : Profile) where
  gaugePreservesBaseline : ∀ (gauge : Real -> Real),
    RepresentedSolution (applyTimeGauge gauge profile.field)
  recenterPreservesBaseline : ∀ shift,
    RepresentedSolution (recenterField shift profile.field)
  rescalePreservesBaseline : ∀ scale,
    RepresentedSolution (rescaleField scale profile.field)

structure WorkCertificate (profile : Profile) where
  checks : Window -> Nat
  checkBound : Nat
  checks_bounded : ∀ window,
    checks window ≤ checkBound
  total_bounded :
    (profile.windows.values.map checks).sum ≤
      profile.windows.values.length * checkBound

structure EnergyCertificate (profile : Profile) where
  initialEnergy : Real
  dissipation : Window -> Real
  dissipationNonnegative : ∀ window, 0 ≤ dissipation window
  energyBound : ∀ window, profile.energy window ≤ initialEnergy
  energyDissipationBound : ∀ window,
    profile.energy window + dissipation window ≤ initialEnergy
  enstrophyBound : ∀ window,
    profile.enstrophy window ≤ initialEnergy

/-! The initial trace is kept separate from local window estimates.  This is
the data needed to connect the local energy ledger to the Cauchy problem. -/
structure InitialDataCertificate (profile : Profile) where
  initialTime : Real
  initialVelocity : Space -> Space
  initialTrace : ∀ x, (initialTime, x) ∈ profile.field.domain ->
    profile.field.velocity (initialTime, x) = initialVelocity x
  initialDivergenceFree : ∀ x, (initialTime, x) ∈ profile.field.domain ->
    divergence profile.field.velocity (initialTime, x) = 0
  initialEnergy : Real
  initialEnergyNonnegative : 0 ≤ initialEnergy

structure VorticityCertificate (profile : Profile) where
  vorticity : Window -> Real
  enstrophyEqualsVorticity : ∀ window,
    profile.enstrophy window = vorticity window ^ 2
  vorticityBound : ∀ window,
    |vorticity window| ≤ Real.sqrt (profile.energy window + 1)

structure PressureCertificate (profile : Profile) where
  oscillation : Window -> Real
  oscillationNonnegative : ∀ window, 0 ≤ oscillation window
  pressureBound : ∀ window,
    oscillation window ≤
      Real.sqrt (profile.energy window + profile.enstrophy window + 1)

structure ContinuationCertificate (profile : Profile) where
  smaller : Window -> Window -> Prop
  wellFounded : WellFounded smaller
  localToSmaller : ∀ small large,
    smaller small large -> profile.localRegular large ->
      profile.localRegular small
  localRegularToTarget : ∀ window,
    profile.localRegular window -> LocalTarget profile window
  targetFromAllLocal : (∀ window ∈ profile.windows.values,
      profile.localRegular window) -> Target profile

structure Registration (profile : Profile) where
  baseline : RepresentedSolution profile.field
  initialData : InitialDataCertificate profile
  gauge : GaugeInterface model representationSemantics
  compactness : CompactnessCertificate profile
  invariance : InvarianceCertificate profile
  energy : EnergyCertificate profile
  vorticity : VorticityCertificate profile
  pressure : PressureCertificate profile
  work : WorkCertificate profile
  continuation : ContinuationCertificate profile

abbrev ProblemInput :=
  Core.Strategy.ProblemInput problem

abbrev InitialStage :=
  Core.Strategy.InitStage problem

def problemInput (profile : Profile) (registration : Registration profile) :
    ProblemInput where
  object := profile.field
  baseline := registration.baseline
  branchState := ()

def initialStage (profile : Profile) (registration : Registration profile) :
    InitialStage :=
  (Core.Strategy.InitStrategy.forProblem problem).run
    (problemInput profile registration)

/-! ## Strategy-facing residual projections

The proof node carries only the current Navier--Stokes registration.  The
generic strategy layer receives the same data as predecessor-owned queries,
so later CT stages can refine the schedule without introducing detached
external output.
-/

def windowQuery (profile : Profile) :
    Core.Residual.Query Unit (fun _ => Core.Finite.Enumeration Window) :=
  Core.Residual.Query.ofFunction (fun _ => profile.windows)

def localRegularQuery (profile : Profile) :
    Core.Residual.Query Unit (fun _ => Window -> Prop) :=
  Core.Residual.Query.ofFunction (fun _ => profile.localRegular)

def localRegularityDecision (profile : Profile) (window : Window) :
    Decidable (profile.localRegular window) :=
  profile.localRegularDecidable window

theorem target_of_local_targets
    (profile : Profile)
    (localTargets : ∀ window, window ∈ profile.windows.values ->
      LocalTarget profile window) :
    Target profile := by
  intro z hz
  obtain ⟨window, member, inWindow⟩ := profile.windowCover z hz
  exact localTargets window member z inWindow

/-! ## Generic strategy projections

These projections expose only the finite, residual-owned part of the
Navier--Stokes registration.  The generic strategy layer still owns all
branching, ledger extension, and terminal routing.
-/

def scaleWindowProfile (profile : Profile) :
    PDE.Strategy.ScaleWindowProfile Unit where
  Scale := fun _ => Window
  schedule := windowQuery profile
  active := fun _ window => profile.localRegular window
  activeDecidable := fun _ window => localRegularityDecision profile window

noncomputable def energyObservableProfile (profile : Profile) :
    PDE.Strategy.ResponseProfile Unit where
  Coordinate := fun _ => Window
  schedule := windowQuery profile
  observe := fun _ window => decide (profile.energy window < 1)

theorem target_of_registration
    (profile : Profile) (registration : Registration profile)
    (localTargets : ∀ window ∈ profile.windows.values,
      profile.localRegular window) :
    Target profile :=
  registration.continuation.targetFromAllLocal localTargets

end Hypostructure.PDE.NavierStokes.Regularity
