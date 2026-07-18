import StructuralExhaustion.Graph.FanClosedPort
import StructuralExhaustion.Graph.HighSeparatorPortClassification

namespace StructuralExhaustion.Graph.HighCompatiblePortOrigin

open StructuralExhaustion

universe u

variable {V : Type u} (object : FiniteObject V) (center : V)
variable (centerHigh : 4 ≤ object.degree center)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)

abbrev Port := HighCenterPort.Port object center

/-- Exact origin of the open-compatible leaf.  The raw ports are retained;
the open subtypes below are definitionally built from these same ports. -/
structure OpenCompatibleOrigin (first second : Port object center) : Prop where
  firstOpen : HighCenterPort.portType object center centerHigh
    deletionCritical first = .open
  secondOpen : HighCenterPort.portType object center centerHigh
    deletionCritical second = .open
  distinct : first ≠ second
  compatible : HighCenterPort.FanCompatible object center first second

namespace OpenCompatibleOrigin

variable {centerHigh deletionCritical}
variable {first second : Port object center}

def firstPort
    (origin : OpenCompatibleOrigin object center centerHigh deletionCritical
      first second) :
    FanClosedPort.OpenPort centerHigh deletionCritical :=
  ⟨first, origin.firstOpen⟩

def secondPort
    (origin : OpenCompatibleOrigin object center centerHigh deletionCritical
      first second) :
    FanClosedPort.OpenPort centerHigh deletionCritical :=
  ⟨second, origin.secondOpen⟩

@[simp] theorem firstPort_raw
    (origin : OpenCompatibleOrigin object center centerHigh deletionCritical
      first second) : origin.firstPort.1 = first := rfl

@[simp] theorem secondPort_raw
    (origin : OpenCompatibleOrigin object center centerHigh deletionCritical
      first second) : origin.secondPort.1 = second := rfl

def pair
    (origin : OpenCompatibleOrigin object center centerHigh deletionCritical
      first second) :
    FanClosedPort.CompatiblePair centerHigh deletionCritical origin.firstPort
      origin.secondPort where
  distinct := by
    intro equal
    exact origin.distinct (congrArg Subtype.val equal)
  compatible := origin.compatible

theorem carriers_nodup
    (origin : OpenCompatibleOrigin object center centerHigh deletionCritical
      first second) :
    (FanClosedPort.carriers centerHigh deletionCritical origin.firstPort
      origin.secondPort).Nodup :=
  FanClosedPort.carriers_nodup centerHigh deletionCritical origin.firstPort
    origin.secondPort origin.pair

end OpenCompatibleOrigin

/-- Compatible pairs containing a triangular port are retained for the
manuscript's separate triangular route. -/
inductive TriangularCompatibleResidual (first second : Port object center) : Prop where
  | openTriangular
      (firstOpen : HighCenterPort.portType object center centerHigh
        deletionCritical first = .open)
      (secondTriangular : HighCenterPort.portType object center centerHigh
        deletionCritical second = .triangular)
      (compatible : HighCenterPort.FanCompatible object center first second)
  | triangularOpen
      (firstTriangular : HighCenterPort.portType object center centerHigh
        deletionCritical first = .triangular)
      (secondOpen : HighCenterPort.portType object center centerHigh
        deletionCritical second = .open)
      (compatible : HighCenterPort.FanCompatible object center first second)
  | triangularTriangular
      (firstTriangular : HighCenterPort.portType object center centerHigh
        deletionCritical first = .triangular)
      (secondTriangular : HighCenterPort.portType object center centerHigh
        deletionCritical second = .triangular)
      (compatible : HighCenterPort.FanCompatible object center first second)

/-- Exact type refinement of an already proved compatible pair. -/
inductive Outcome (first second : Port object center) : Type u where
  | openPair
      (origin : OpenCompatibleOrigin object center centerHigh deletionCritical
        first second)
  | triangular
      (residual : TriangularCompatibleResidual object center centerHigh
        deletionCritical first second)

/-- Refine compatibility using only the fixed two-port type table. -/
def classify (first second : Port object center) (distinct : first ≠ second)
    (compatible : HighCenterPort.FanCompatible object center first second) :
    Outcome object center centerHigh deletionCritical first second := by
  cases HighSeparatorPortClassification.classifyPairCase object center
      centerHigh deletionCritical first second with
  | openOpen firstOpen secondOpen =>
      exact .openPair ⟨firstOpen, secondOpen, distinct, compatible⟩
  | openTriangular firstOpen secondTriangular =>
      exact .triangular (.openTriangular firstOpen secondTriangular compatible)
  | triangularOpen firstTriangular secondOpen =>
      exact .triangular (.triangularOpen firstTriangular secondOpen compatible)
  | triangularTriangular firstTriangular secondTriangular =>
      exact .triangular
        (.triangularTriangular firstTriangular secondTriangular compatible)

/-- Fully proved local data waiting for the manuscript's assigned Type-B
profile.  No remainder or assignment fact is a field of this frontier. -/
structure AssignmentFrontier (first second : Port object center) : Prop where
  origin : OpenCompatibleOrigin object center centerHigh deletionCritical
    first second

def assignmentFrontier {first second : Port object center}
    (origin : OpenCompatibleOrigin object center centerHigh deletionCritical
      first second) :
    AssignmentFrontier object center centerHigh deletionCritical first second :=
  ⟨origin⟩

/-- The exact conditional premise of the paper's compatible-pair fan-closure
lemma: a semantic profile plus the two endpoint and four carrier assignments. -/
structure AssignedEntry {first second : Port object center}
    (frontier : AssignmentFrontier object center centerHigh deletionCritical
      first second) : Type u where
  profile : FanClosedPort.FanWindowProfile V
  assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
    frontier.origin.firstPort frontier.origin.secondPort

namespace AssignedEntry

variable {centerHigh deletionCritical}
variable {first second : Port object center}
variable {frontier : AssignmentFrontier object center centerHigh
  deletionCritical first second}

theorem first_fanClosed (entry : AssignedEntry object center centerHigh
    deletionCritical frontier) :
    FanClosedPort.FanClosed centerHigh deletionCritical entry.profile
      frontier.origin.firstPort :=
  FanClosedPort.first_fanClosed centerHigh deletionCritical entry.profile
    frontier.origin.firstPort frontier.origin.secondPort entry.assigned

theorem second_fanClosed (entry : AssignedEntry object center centerHigh
    deletionCritical frontier) :
    FanClosedPort.FanClosed centerHigh deletionCritical entry.profile
      frontier.origin.secondPort :=
  FanClosedPort.second_fanClosed centerHigh deletionCritical entry.profile
    frontier.origin.firstPort frontier.origin.secondPort entry.assigned

end AssignedEntry

end StructuralExhaustion.Graph.HighCompatiblePortOrigin
