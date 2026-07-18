import StructuralExhaustion.Graph.HighSeparatorPortClassification
import StructuralExhaustion.Graph.OpenPortSuppression

namespace StructuralExhaustion.Graph.HighOpenEndpointFailure

open StructuralExhaustion

universe u

variable {V : Type u} (object : FiniteObject V) (center : V)
variable (centerHigh : 4 ≤ object.degree center)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)

abbrev Port := HighCenterPort.Port object center

/-- Four-case normalization of an endpoint-in-shoulders failure.  `side=false`
means the foreign endpoint is the first shoulder of the suppressed port. -/
structure NormalizedFailure (first second : Port object center) : Type u where
  foreign : Port object center
  suppressed : Port object center
  foreignOpen : HighCenterPort.portType object center centerHigh
    deletionCritical foreign = .open
  suppressedOpen : HighCenterPort.portType object center centerHigh
    deletionCritical suppressed = .open
  distinct : foreign ≠ suppressed
  origin : (foreign = first ∧ suppressed = second) ∨
    (foreign = second ∧ suppressed = first)
  side : Bool
  foreign_eq_shoulder : HighCenterPort.endpoint object center foreign =
    if side then
      HighCenterPort.secondShoulder object center centerHigh deletionCritical
        suppressed
    else
      HighCenterPort.firstShoulder object center centerHigh deletionCritical
        suppressed

/-- Inspect only the proved two-element shoulder list. -/
noncomputable def classify {first second : Port object center}
    (failure : HighSeparatorPortClassification.OpenEndpointFailure object
      center centerHigh deletionCritical first second) :
    NormalizedFailure object center centerHigh deletionCritical first second := by
  cases failure with
  | firstEndpointInSecondShoulders firstOpen secondOpen member =>
      classical
      by_cases equal : HighCenterPort.endpoint object center first =
          HighCenterPort.firstShoulder object center centerHigh deletionCritical second
      · exact {
          foreign := first
          suppressed := second
          foreignOpen := firstOpen
          suppressedOpen := secondOpen
          distinct := by
            intro same
            subst second
            exact (HighCenterPort.adjacent_of_mem_shoulders object center first
              member).ne rfl
          origin := Or.inl ⟨rfl, rfl⟩
          side := false
          foreign_eq_shoulder := by simpa using equal
        }
      · have equalSecond : HighCenterPort.endpoint object center first =
            HighCenterPort.secondShoulder object center centerHigh
              deletionCritical second :=
          (HighCenterPort.eq_firstShoulder_or_eq_secondShoulder_of_mem object
            center centerHigh deletionCritical second member).resolve_left equal
        exact {
          foreign := first
          suppressed := second
          foreignOpen := firstOpen
          suppressedOpen := secondOpen
          distinct := by
            intro same
            subst second
            exact (HighCenterPort.adjacent_of_mem_shoulders object center first
              member).ne rfl
          origin := Or.inl ⟨rfl, rfl⟩
          side := true
          foreign_eq_shoulder := by simpa using equalSecond
        }
  | secondEndpointInFirstShoulders firstOpen secondOpen member =>
      classical
      by_cases equal : HighCenterPort.endpoint object center second =
          HighCenterPort.firstShoulder object center centerHigh deletionCritical first
      · exact {
          foreign := second
          suppressed := first
          foreignOpen := secondOpen
          suppressedOpen := firstOpen
          distinct := by
            intro same
            subst second
            exact (HighCenterPort.adjacent_of_mem_shoulders object center first
              member).ne rfl
          origin := Or.inr ⟨rfl, rfl⟩
          side := false
          foreign_eq_shoulder := by simpa using equal
        }
      · have equalSecond : HighCenterPort.endpoint object center second =
            HighCenterPort.secondShoulder object center centerHigh
              deletionCritical first :=
          (HighCenterPort.eq_firstShoulder_or_eq_secondShoulder_of_mem object
            center centerHigh deletionCritical first member).resolve_left equal
        exact {
          foreign := second
          suppressed := first
          foreignOpen := secondOpen
          suppressedOpen := firstOpen
          distinct := by
            intro same
            subst second
            exact (HighCenterPort.adjacent_of_mem_shoulders object center first
              member).ne rfl
          origin := Or.inr ⟨rfl, rfl⟩
          side := true
          foreign_eq_shoulder := by simpa using equalSecond
        }

namespace NormalizedFailure

variable {centerHigh deletionCritical}
variable {first second : Port object center}

theorem foreign_mem_shoulders
    (failure : NormalizedFailure object center centerHigh deletionCritical
      first second) :
    HighCenterPort.endpoint object center failure.foreign ∈
      HighCenterPort.shoulderVertices object center failure.suppressed := by
  rw [failure.foreign_eq_shoulder]
  cases failure.side
  · exact HighCenterPort.firstShoulder_mem object center centerHigh
      deletionCritical failure.suppressed
  · exact HighCenterPort.secondShoulder_mem object center centerHigh
      deletionCritical failure.suppressed

theorem endpoints_adjacent
    (failure : NormalizedFailure object center centerHigh deletionCritical
      first second) :
    object.graph.Adj
      (HighCenterPort.endpoint object center failure.foreign)
      (HighCenterPort.endpoint object center failure.suppressed) :=
  (HighCenterPort.adjacent_of_mem_shoulders object center failure.suppressed
    failure.foreign_mem_shoulders).symm

/-- The literal type-(c) blocker carrier: the same vertex has buffer role for
one port and shoulder role for the other. -/
structure SharedCarrier
    (failure : NormalizedFailure object center centerHigh deletionCritical
      first second) : Type u where
  vertex : V
  isForeignBuffer : vertex = HighCenterPort.endpoint object center failure.foreign
  isSuppressedShoulder : vertex ∈
    HighCenterPort.shoulderVertices object center failure.suppressed

def sharedCarrier
    (failure : NormalizedFailure object center centerHigh deletionCritical
      first second) : SharedCarrier object center failure where
  vertex := HighCenterPort.endpoint object center failure.foreign
  isForeignBuffer := rfl
  isSuppressedShoulder := failure.foreign_mem_shoulders

end NormalizedFailure

/-- Suppression input for one exact raw high-center open port. -/
def suppressionSetup (port : Port object center)
    (isOpen : HighCenterPort.portType object center centerHigh
      deletionCritical port = .open) : OpenPortSuppression.Setup object where
  center := center
  endpoint := HighCenterPort.endpoint object center port
  first := HighCenterPort.firstShoulder object center centerHigh
    deletionCritical port
  second := HighCenterPort.secondShoulder object center centerHigh
    deletionCritical port
  endpoint_ne_center := (HighCenterPort.endpoint_adjacent object center port).ne.symm
  endpoint_ne_first :=
    (HighCenterPort.firstShoulder_adjacent_endpoint object center centerHigh
      deletionCritical port).ne.symm
  endpoint_ne_second :=
    (HighCenterPort.secondShoulder_adjacent_endpoint object center centerHigh
      deletionCritical port).ne.symm
  first_ne_second := HighCenterPort.firstShoulder_ne_secondShoulder object center
    centerHigh deletionCritical port
  center_ne_first :=
    (HighCenterPort.ne_center_of_mem_shoulders object center port
      (HighCenterPort.firstShoulder_mem object center centerHigh
        deletionCritical port)).symm
  center_ne_second :=
    (HighCenterPort.ne_center_of_mem_shoulders object center port
      (HighCenterPort.secondShoulder_mem object center centerHigh
        deletionCritical port)).symm
  endpoint_neighbors := by
    intro vertex
    constructor
    · intro adjacent
      by_cases central : vertex = center
      · exact Or.inl central
      · exact Or.inr
          (HighCenterPort.eq_firstShoulder_or_eq_secondShoulder_of_mem object
            center centerHigh deletionCritical port
            (HighCenterPort.mem_shoulders_of_adjacent_endpoint_of_ne_center
              object center port adjacent central))
    · rintro (equal | equal | equal)
      · simpa [equal] using
          (HighCenterPort.endpoint_adjacent object center port).symm
      · simpa [equal] using
          (HighCenterPort.firstShoulder_adjacent_endpoint object center
            centerHigh deletionCritical port).symm
      · simpa [equal] using
          (HighCenterPort.secondShoulder_adjacent_endpoint object center
            centerHigh deletionCritical port).symm
  open_shoulders := by
    intro adjacent
    letI : DecidableRel object.graph.Adj := object.input.decideAdj
    change (if object.graph.Adj
      (HighCenterPort.firstShoulder object center centerHigh deletionCritical port)
      (HighCenterPort.secondShoulder object center centerHigh deletionCritical port)
      then HighCenterPort.PortType.triangular else HighCenterPort.PortType.open) =
        HighCenterPort.PortType.open at isOpen
    simp [adjacent] at isOpen
  center_high := centerHigh

/-- The complete dependency-ready local activation.  The critical cycle is
proof-selected by minimality and already proves use of the added chord. -/
structure ActivatedFailure
    (input : PackedMinimumDegreeCycle.StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (center : ctx.G.Vertex)
    (centerHigh : 4 ≤ ctx.G.object.degree center)
    (deletionCritical : ∀ dart : ctx.G.object.graph.Dart,
      ctx.G.object.degree dart.fst = 3 ∨ ctx.G.object.degree dart.snd = 3)
    (first second : Port ctx.G.object center) : Type u where
  normalized : NormalizedFailure ctx.G.object center centerHigh
    deletionCritical first second
  critical : OpenPortSuppression.Setup.CriticalCycle
    (suppressionSetup ctx.G.object center centerHigh deletionCritical
      normalized.suppressed normalized.suppressedOpen) input.LengthOK
  response : OpenPortSuppression.Setup.SuppressionPath
    (suppressionSetup ctx.G.object center centerHigh deletionCritical
      normalized.suppressed normalized.suppressedOpen) input.LengthOK
  response_exact : response = critical.predecessor

noncomputable def activate
    (input : PackedMinimumDegreeCycle.StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (minimumDegree_eq_three : input.minimumDegree = 3)
    (center : ctx.G.Vertex)
    (centerHigh : 4 ≤ ctx.G.object.degree center)
    (deletionCritical : ∀ dart : ctx.G.object.graph.Dart,
      ctx.G.object.degree dart.fst = 3 ∨ ctx.G.object.degree dart.snd = 3)
    {first second : Port ctx.G.object center}
    (failure : HighSeparatorPortClassification.OpenEndpointFailure ctx.G.object
      center centerHigh deletionCritical first second) :
    ActivatedFailure input ctx center centerHigh deletionCritical first second := by
  let normalized := classify ctx.G.object center centerHigh deletionCritical failure
  let localSetup := suppressionSetup ctx.G.object center centerHigh
    deletionCritical normalized.suppressed normalized.suppressedOpen
  let critical := Classical.choice
    (localSetup.criticalCycleFromMinimality input ctx minimumDegree_eq_three)
  exact {
    normalized := normalized
    critical := critical
    response := critical.predecessor
    response_exact := rfl
  }

end StructuralExhaustion.Graph.HighOpenEndpointFailure
