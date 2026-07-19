import StructuralExhaustion.Graph.HighCenterStructure
import StructuralExhaustion.Graph.OpenPortResponse

namespace StructuralExhaustion.Graph.OpenPortCompatibility

open StructuralExhaustion

universe u

/-!
# Fan compatibility for an exact CT9 overload pair

The profile interprets the pair already extracted by the registered
CT9-to-CT7 route.  It never enumerates pairs.  Four-cycle avoidance turns the
nonadjacent endpoint branch into the exact shoulder-disjointness conditions
used by fan routing; the complementary branch retains the literal endpoint
edge as a separate residual state.
-/

abbrev Slot (object : FiniteObject V) :=
  SurplusPortActivity.ExcessPortSlot object

/-- Exact graph-theoretic compatibility predicate for two ports. -/
def FanCompatible (object : FiniteObject V) (first second : Slot object) : Prop :=
  SurplusPortActivity.portEndpoint object first ∉
      SurplusPortActivity.shoulderVertices object second ∧
    SurplusPortActivity.portEndpoint object second ∉
      SurplusPortActivity.shoulderVertices object first ∧
    List.Disjoint
      (SurplusPortActivity.shoulderVertices object first)
      (SurplusPortActivity.shoulderVertices object second)

/-- Selected-slot specialization of the generic all-incident-port theorem. -/
theorem fanCompatible_of_nonadjacent
    (object : FiniteObject V)
    (fourFree : ¬HasCycleWithLength object.graph HighCenterStructure.FourLength)
    {first second : Slot object}
    (sameCenter : first.1 = second.1)
    (distinct : first ≠ second)
    (nonadjacent : ¬object.graph.Adj
      (SurplusPortActivity.portEndpoint object first)
      (SurplusPortActivity.portEndpoint object second)) :
    FanCompatible object first second := by
  rcases first with ⟨center, firstIndex⟩
  rcases second with ⟨secondCenter, secondIndex⟩
  dsimp only at sameCenter
  subst secondCenter
  have portDistinct :
      SurplusPortActivity.portOfSlot object ⟨center, firstIndex⟩ ≠
        SurplusPortActivity.portOfSlot object ⟨center, secondIndex⟩ := by
    intro equal
    apply distinct
    have valueEq : firstIndex.1 = secondIndex.1 :=
      congrArg (fun port : HighCenterPort.Port object center => port.1) equal
    have indexEq : firstIndex = secondIndex := Fin.ext valueEq
    subst secondIndex
    rfl
  simpa [FanCompatible, SurplusPortActivity.portEndpoint,
    SurplusPortActivity.shoulderVertices, HighCenterPort.FanCompatible] using
    (HighCenterPort.fanCompatible_of_nonadjacent object center fourFree
      portDistinct nonadjacent)

abbrev SourceResidual
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :=
  OpenPortResponse.SourceResidual base object baseline deletionCritical

def sourcePair
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (source : SourceResidual base object baseline deletionCritical) :=
  Routes.CT9ToCT7.sourcePair source
    (OpenPortResponse.capacityOne base object deletionCritical source.label)

def firstSlot
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (source : SourceResidual base object baseline deletionCritical) : Slot object :=
  (sourcePair base object baseline deletionCritical source).first.1

def secondSlot
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (source : SourceResidual base object baseline deletionCritical) : Slot object :=
  (sourcePair base object baseline deletionCritical source).second.1

theorem sourceSlots_distinct
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (source : SourceResidual base object baseline deletionCritical) :
    firstSlot base object baseline deletionCritical source ≠
      secondSlot base object baseline deletionCritical source := by
  intro equal
  exact (sourcePair base object baseline deletionCritical source).distinct
    (Subtype.ext equal)

theorem sourceSlots_sameCenter
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (source : SourceResidual base object baseline deletionCritical) :
    (firstSlot base object baseline deletionCritical source).1 =
      (secondSlot base object baseline deletionCritical source).1 :=
  (sourcePair base object baseline deletionCritical source).labels_eq

/-- Exact semantic state retained after the preceding CT9-to-CT7 execution. -/
def StateSpace
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (source : SourceResidual base object baseline deletionCritical) : Prop :=
  object.graph.Adj
      (SurplusPortActivity.portEndpoint object
        (firstSlot base object baseline deletionCritical source))
      (SurplusPortActivity.portEndpoint object
        (secondSlot base object baseline deletionCritical source)) ∨
    FanCompatible object
      (firstSlot base object baseline deletionCritical source)
      (secondSlot base object baseline deletionCritical source)

/-- Exact state-space refinement of the preceding CT9-to-CT7 execution. -/
theorem stateSpace
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (source : SourceResidual base object baseline deletionCritical)
    (fourFree : ¬HasCycleWithLength object.graph HighCenterStructure.FourLength) :
    StateSpace base object baseline deletionCritical source := by
  by_cases adjacent : object.graph.Adj
      (SurplusPortActivity.portEndpoint object
        (firstSlot base object baseline deletionCritical source))
      (SurplusPortActivity.portEndpoint object
        (secondSlot base object baseline deletionCritical source))
  · exact Or.inl adjacent
  · exact Or.inr (fanCompatible_of_nonadjacent object fourFree
      (sourceSlots_sameCenter base object baseline deletionCritical source)
      (sourceSlots_distinct base object baseline deletionCritical source)
      adjacent)

end StructuralExhaustion.Graph.OpenPortCompatibility
