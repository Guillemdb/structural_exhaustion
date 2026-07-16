import StructuralExhaustion.Graph.HighSeparatorPortClassification
import StructuralExhaustion.Graph.TriangularPortReturn
import StructuralExhaustion.Graph.TriangularCrossShoulder

namespace StructuralExhaustion.Graph.HighSeparatorPortClassificationRoutes

open StructuralExhaustion

universe u
universe v

variable {V : Type u}
variable {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
variable {object : FiniteObject V} {baseline : base.problem.Baseline object}
variable {center : V}

abbrev Setup (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (center : V) :=
  TriangularShoulderCompletion.Setup base object baseline center

/-- Preserve the exact classifier branch while converting its equality
evidence into the subtype expected by the existing triangular profiles. -/
inductive PortRoute (setup : Setup base object baseline center)
    (port : HighCenterPort.Port object center) where
  | openPort (exact : HighCenterPort.portType object center setup.centerHigh
      setup.deletionCritical port = .open)
  | triangularPort (exact : HighCenterPort.portType object center setup.centerHigh
      setup.deletionCritical port = .triangular)

def routePort (setup : Setup base object baseline center)
    (port : HighCenterPort.Port object center)
    (classified : HighSeparatorPortClassification.PortClass object center
      setup.centerHigh setup.deletionCritical port) :
    PortRoute setup port :=
  match classified with
  | .open exact => .openPort exact
  | .triangular exact => .triangularPort exact

/-- The complete ordered pair split.  In particular, `openOpen` remains a
typed live branch; this adapter supplies no assignment or selected-slot
semantics. -/
inductive PairRoute (setup : Setup base object baseline center)
    (first second : HighCenterPort.Port object center) where
  | openOpen
      (firstExact : HighCenterPort.portType object center setup.centerHigh
        setup.deletionCritical first = .open)
      (secondExact : HighCenterPort.portType object center setup.centerHigh
        setup.deletionCritical second = .open)
  | openTriangular
      (firstExact : HighCenterPort.portType object center setup.centerHigh
        setup.deletionCritical first = .open)
      (secondExact : HighCenterPort.portType object center setup.centerHigh
        setup.deletionCritical second = .triangular)
  | triangularOpen
      (firstExact : HighCenterPort.portType object center setup.centerHigh
        setup.deletionCritical first = .triangular)
      (secondExact : HighCenterPort.portType object center setup.centerHigh
        setup.deletionCritical second = .open)
  | triangularTriangular
      (firstExact : HighCenterPort.portType object center setup.centerHigh
        setup.deletionCritical first = .triangular)
      (secondExact : HighCenterPort.portType object center setup.centerHigh
        setup.deletionCritical second = .triangular)

def routePair (setup : Setup base object baseline center)
    (first second : HighCenterPort.Port object center)
    (classified : HighSeparatorPortClassification.PairCase object center
      setup.centerHigh setup.deletionCritical first second) :
    PairRoute setup first second := by
  cases classified with
  | openOpen firstExact secondExact =>
      exact .openOpen firstExact secondExact
  | openTriangular firstExact secondExact =>
      exact .openTriangular firstExact secondExact
  | triangularOpen firstExact secondExact =>
      exact .triangularOpen firstExact secondExact
  | triangularTriangular firstExact secondExact =>
      exact .triangularTriangular firstExact secondExact

namespace PairRoute

def firstRoute (setup : Setup base object baseline center)
    {first second : HighCenterPort.Port object center}
    (route : PairRoute setup first second) : PortRoute setup first :=
  match route with
  | .openOpen firstExact _ | .openTriangular firstExact _ =>
      .openPort firstExact
  | .triangularOpen firstExact _ | .triangularTriangular firstExact _ =>
      .triangularPort firstExact

def secondRoute (setup : Setup base object baseline center)
    {first second : HighCenterPort.Port object center}
    (route : PairRoute setup first second) : PortRoute setup second :=
  match route with
  | .openOpen _ secondExact | .triangularOpen _ secondExact =>
      .openPort secondExact
  | .openTriangular _ secondExact | .triangularTriangular _ secondExact =>
      .triangularPort secondExact

end PairRoute

/-- Root classification and all caller provenance are retained together with
the converted port routes. -/
structure RootRoutes (setup : Setup base object baseline center)
    {divergence : RootIncidence.Divergence object center}
    {third : RootIncidence.Third object center divergence}
    {Provenance : Type v}
    (output : HighSeparatorPort.RootHigh object divergence third Provenance) where
  classified : HighSeparatorPortClassification.RootResult object center output
    setup.deletionCritical
  divergent : PairRoute setup output.leftPort output.rightPort
  thirdPort : PortRoute setup output.thirdPort
  provenance_eq : classified.provenance = output.provenance

noncomputable def routeRoot (setup : Setup base object baseline center)
    {divergence : RootIncidence.Divergence object center}
    {third : RootIncidence.Third object center divergence}
    {Provenance : Type v}
    (output : HighSeparatorPort.RootHigh object divergence third Provenance) :
    RootRoutes setup output := by
  let classified := HighSeparatorPortClassification.classifyRoot object center
    output setup.deletionCritical
  exact {
    classified := classified
    divergent := routePair setup output.leftPort output.rightPort
      classified.divergent.typeCase
    thirdPort := routePort setup output.thirdPort classified.thirdClass
    provenance_eq := rfl
  }

/-- After-edge analogue retaining the complete classified incidence payload. -/
structure AfterEdgeRoutes (setup : Setup base object baseline center)
    {incidence : RootIncidence.AfterEdge object center}
    {Provenance : Type v}
    (output : HighSeparatorPort.AfterEdgeHigh object incidence Provenance) where
  classified : HighSeparatorPortClassification.AfterEdgeResult object center
    output setup.deletionCritical
  predecessor : PortRoute setup output.predecessorPort
  divergent : PairRoute setup output.leftPort output.rightPort
  provenance_eq : classified.provenance = output.provenance

noncomputable def routeAfterEdge (setup : Setup base object baseline center)
    {incidence : RootIncidence.AfterEdge object center}
    {Provenance : Type v}
    (output : HighSeparatorPort.AfterEdgeHigh object incidence Provenance) :
    AfterEdgeRoutes setup output := by
  let classified := HighSeparatorPortClassification.classifyAfterEdge object
    center output setup.deletionCritical
  exact {
    classified := classified
    predecessor := routePort setup output.predecessorPort
      classified.predecessorClass
    divergent := routePair setup output.leftPort output.rightPort
      classified.divergent.typeCase
    provenance_eq := rfl
  }

/-- One classifier-selected triangular port together with the already
verified global shoulder-completion stage on the identical setup. -/
structure ShoulderOutput (setup : Setup base object baseline center) where
  port : TriangularShoulderCompletion.TriPort setup
  stage : TriangularShoulderCompletion.VerifiedStage setup

def shoulderStage? (setup : Setup base object baseline center)
    {port : HighCenterPort.Port object center}
    (route : PortRoute setup port) : Option (ShoulderOutput setup) :=
  match route with
  | .openPort _ => none
  | .triangularPort exact => some {
      port := ⟨port, exact⟩
      stage := TriangularShoulderCompletion.verifiedStage setup
    }

/-- Required return inputs are explicit functions of the extracted triangular
port, so the adapter cannot substitute a look-alike root. -/
structure ReturnOutput (setup : Setup base object baseline center)
    (root : (port : TriangularShoulderCompletion.TriPort setup) →
      DartReturn object.graph (TriangularPortReturn.rootDart setup port))
    (avoids : ¬HasCycleWithLength object.graph base.LengthOK) where
  port : TriangularShoulderCompletion.TriPort setup
  stage : TriangularPortReturn.VerifiedStage setup port (root port) avoids

noncomputable def returnStage? (setup : Setup base object baseline center)
    (root : (port : TriangularShoulderCompletion.TriPort setup) →
      DartReturn object.graph (TriangularPortReturn.rootDart setup port))
    (avoids : ¬HasCycleWithLength object.graph base.LengthOK)
    {port : HighCenterPort.Port object center} (route : PortRoute setup port) :
    Option (ReturnOutput setup root avoids) :=
  match route with
  | .openPort _ => none
  | .triangularPort exact =>
      let triangularPort : TriangularShoulderCompletion.TriPort setup :=
        ⟨port, exact⟩
      some {
        port := triangularPort
        stage := TriangularPortReturn.verifiedStage setup triangularPort
          (root triangularPort) avoids
      }

/-- Exact TT-only CT9 consumer.  Mixed and open pairs intentionally return
`none`; their unresolved open side is not silently discarded. -/
structure CrossOutput (setup : Setup base object baseline center) where
  first : TriangularCrossShoulder.TriPort setup
  second : TriangularCrossShoulder.TriPort setup
  distinct : first ≠ second
  stage : TriangularCrossShoulder.VerifiedStage first second distinct

def crossStage? (setup : Setup base object baseline center)
    {first second : HighCenterPort.Port object center}
    (portsNe : first ≠ second) (route : PairRoute setup first second) :
    Option (CrossOutput setup) :=
  match route with
  | .triangularTriangular firstExact secondExact =>
      let firstPort : TriangularCrossShoulder.TriPort setup :=
        ⟨first, firstExact⟩
      let secondPort : TriangularCrossShoulder.TriPort setup :=
        ⟨second, secondExact⟩
      let distinct : firstPort ≠ secondPort := fun equal =>
        portsNe (congrArg Subtype.val equal)
      some {
        first := firstPort
        second := secondPort
        distinct := distinct
        stage := TriangularCrossShoulder.verifiedStage firstPort secondPort
          distinct
      }
  | .openOpen _ _ | .openTriangular _ _ | .triangularOpen _ _ => none

end StructuralExhaustion.Graph.HighSeparatorPortClassificationRoutes
