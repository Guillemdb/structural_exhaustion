import Erdos64EG.Future.P13SelectedWindowCorridor
import StructuralExhaustion.CT17.Automation
import StructuralExhaustion.Graph.InducedPathColdGermScale

namespace Erdos64EG.Internal.P13SelectedWindowGermScale

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor
open StructuralExhaustion.Graph.InducedPathColdGermScale

universe u

variable (ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u})

noncomputable abbrev supportLength
    (stub : CubicStub ctx.G.object) : Nat :=
  (p13SelectedWindowCorridorProducer ctx).ambientReturn stub |>.support.length

noncomputable abbrev rootLength
    (stub : CubicStub ctx.G.object) : Nat :=
  (p13SelectedWindowCorridorProducer ctx).rootCycle stub |>.length

/-- The literal bounded exponent universe occurring in
`PowerOfTwoLength (rootLength ctx stub)`. -/
abbrev PowerTarget (stub : CubicStub ctx.G.object) :=
  {exponent : Fin (rootLength ctx stub + 1) // 2 ≤ exponent.1}

@[implicit_reducible]
noncomputable def powerTargets (stub : CubicStub ctx.G.object) :
    FinEnum (PowerTarget ctx stub) :=
  Core.Enumeration.subtype
    (inferInstance : FinEnum (Fin (rootLength ctx stub + 1)))
    (fun exponent => 2 ≤ exponent.1) (fun _ => inferInstance)

/-- Actual root-cycle arithmetic viewed through CT17.  Both finite block and
large orbit values are the literal restored-cycle length; the target values
are precisely the allowed powers of two. -/
noncomputable abbrev powerOrbitSpec (stub : CubicStub ctx.G.object) :
    CT17.Spec PackedProblem.{u} where
  Target := PowerTarget ctx stub
  Offset := Unit
  Position := fun _scale => Fin (supportLength ctx stub)
  Value := Nat
  targetValue := fun target => 2 ^ target.1.1
  blockValue := fun _branch {_scale} _position _offset => rootLength ctx stub
  orbitValue := fun _branch _scale _offset => rootLength ctx stub
  Compatible := fun _branch _target _offset => True

/-- The checked short/long threshold is CT17's finite-scale limit.  Its
position enumeration is the literal corridor support. -/
noncomputable def powerOrbitCapability (stub : CubicStub ctx.G.object)
    (threshold : Nat) : CT17.Capability (powerOrbitSpec ctx stub) where
  targets := powerTargets ctx stub
  offsets := Core.Enumeration.unit
  positions := fun _scale => inferInstance
  compatibleDecidable := fun _branch _target _offset => .isTrue trivial
  valueDecidableEq := inferInstance
  finiteScaleLimit := threshold

/-- Route-facing CT17 trigger.  The incoming scale is the actual support
length, so a graph-proved long inequality forces CT17's arithmetic branch. -/
noncomputable def powerOrbitInput (stub : CubicStub ctx.G.object)
    (threshold : Nat) :
    CT17.Input (powerOrbitSpec ctx stub)
      (powerOrbitCapability ctx stub threshold) ctx.toBranchContext :=
  ⟨supportLength ctx stub⟩

noncomputable def powerOrbitRun (stub : CubicStub ctx.G.object)
    (threshold : Nat) :=
  CT17.run (powerOrbitSpec ctx stub)
    (powerOrbitCapability ctx stub threshold) ctx.toBranchContext
    (powerOrbitInput ctx stub threshold)

theorem long_forces_arithmetic
    (stub : CubicStub ctx.G.object)
    (germ : Producer.ColdStructuralGerm
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength stub)
    (threshold : Nat)
    (residual : LongSupportResidual
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength stub germ threshold) :
    (powerOrbitCapability ctx stub threshold).finiteScaleLimit <
      (powerOrbitInput ctx stub threshold).scale :=
  residual.exceeds

/-- A CT17 target hit is exactly the forbidden root-cycle power of two, so
the quiet germ rules it out without any response assumption. -/
theorem targetHit_impossible
    (stub : CubicStub ctx.G.object)
    (germ : Producer.ColdStructuralGerm
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength stub)
    (threshold : Nat)
    {compatible : CT17.CompatibleState (powerOrbitSpec ctx stub)
      (powerOrbitCapability ctx stub threshold) ctx.toBranchContext
      (powerOrbitInput ctx stub threshold)}
    {orbit : CT17.OrbitScaleState (powerOrbitSpec ctx stub)
      (powerOrbitCapability ctx stub threshold) ctx.toBranchContext
      (powerOrbitInput ctx stub threshold) compatible}
    (certificate : CT17.TargetHitCertificate (powerOrbitSpec ctx stub)
      (powerOrbitCapability ctx stub threshold) ctx.toBranchContext
      (powerOrbitInput ctx stub threshold) orbit) : False := by
  apply germ.rootLengthRejected
  exact ⟨certificate.target.1, certificate.target.2, certificate.equal⟩

/-- The long trigger really reaches CT17's arithmetic orbit residual.  The
compatibility and finite-scale terminals contradict definitional graph data,
and the target-hit terminal contradicts the quiet germ. -/
theorem powerOrbitRun_terminal_orbit
    (stub : CubicStub ctx.G.object)
    (germ : Producer.ColdStructuralGerm
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength stub)
    (threshold : Nat)
    (residual : LongSupportResidual
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength stub germ threshold) :
    (powerOrbitRun ctx stub threshold).terminal = .orbit := by
  generalize runEq : powerOrbitRun ctx stub threshold = result
  rcases result with ⟨terminal, path, outcome⟩
  cases outcome with
  | incompatibility incompatible =>
      exact False.elim (incompatible.incompatible trivial)
  | @exhausted compatible finite certificate =>
      exact False.elim (Nat.not_le_of_lt residual.exceeds finite.finite)
  | @survivors compatible finite survivor =>
      exact False.elim (Nat.not_le_of_lt residual.exceeds finite.finite)
  | targetHit certificate =>
      exact False.elim (targetHit_impossible ctx stub germ threshold certificate)
  | orbit orbit => rfl

/-- End-to-end graph-owned result for one selected window and one explicit
scale threshold.  No stub, germ, branch choice, target universe, or CT17
trigger is supplied by the caller. -/
inductive RoutedWindowScale
    (window : P13SelectedConnectorWindow ctx) (threshold : Nat) where
  | surplus (position : Fin 13)
      (high : 3 < ctx.G.object.degree (window.1 position))
  | firstEvent (stub : CubicStub ctx.G.object)
      (sameWindow : stub.window = selectedConnectorWindowIndex window)
      (hit : Core.FiniteSearch.FirstHit
        ((InducedPathColdCorridor.firstFailureProfile
          (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
          powerOfTwoLengthDecidable).stages stub).values
        ((InducedPathColdCorridor.firstFailureProfile
          (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
          powerOfTwoLengthDecidable).Event stub))
      (event : (InducedPathColdCorridor.firstFailureProfile
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
        powerOfTwoLengthDecidable).EventData stub hit.value)
  | short (stub : CubicStub ctx.G.object)
      (sameWindow : stub.window = selectedConnectorWindowIndex window)
      (noEvent : ∀ stage,
        stage ∈ ((InducedPathColdCorridor.firstFailureProfile
          (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
          powerOfTwoLengthDecidable).stages stub).values →
        ¬(InducedPathColdCorridor.firstFailureProfile
          (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
          powerOfTwoLengthDecidable).Event stub stage)
      (germ : Producer.ColdStructuralGerm
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength stub)
      (residual : BoundedSameInterfaceResidual
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength stub germ threshold)
  | long (stub : CubicStub ctx.G.object)
      (sameWindow : stub.window = selectedConnectorWindowIndex window)
      (noEvent : ∀ stage,
        stage ∈ ((InducedPathColdCorridor.firstFailureProfile
          (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
          powerOfTwoLengthDecidable).stages stub).values →
        ¬(InducedPathColdCorridor.firstFailureProfile
          (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
          powerOfTwoLengthDecidable).Event stub stage)
      (germ : Producer.ColdStructuralGerm
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength stub)
      (residual : LongSupportResidual
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength stub germ threshold)
      (result : CT17.ExecutionResult (powerOrbitSpec ctx stub)
        (powerOrbitCapability ctx stub threshold) ctx.toBranchContext
        (powerOrbitInput ctx stub threshold))
      (arithmeticOrbit : result.terminal = .orbit)

/-- Execute the complete selected-window route through the scale split and,
on the long side, through CT17 itself. -/
noncomputable def routeWindowScale
    (window : P13SelectedConnectorWindow ctx) (threshold : Nat) :
    RoutedWindowScale ctx window threshold :=
  match routeSelectedWindowCorridor ctx window with
  | .surplus position high => .surplus position high
  | .corridor stub sameWindow result =>
      match result with
      | .first hit event => .firstEvent stub sameWindow hit event
      | .germ noEvent germ =>
          match InducedPathColdGermScale.route
              (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
              stub germ threshold with
          | .short residual => .short stub sameWindow noEvent germ residual
          | .long residual => .long stub sameWindow noEvent germ residual
              (powerOrbitRun ctx stub threshold)
              (powerOrbitRun_terminal_orbit ctx stub germ threshold residual)

end Erdos64EG.Internal.P13SelectedWindowGermScale
