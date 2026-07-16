import StructuralExhaustion.Graph.HighSeparatorPort
import StructuralExhaustion.Graph.HighCenterStructure

namespace StructuralExhaustion.Graph.HighSeparatorPortClassification

open StructuralExhaustion

universe u v

variable {V : Type u} (object : FiniteObject V) (center : V)

abbrev Port := HighCenterPort.Port object center

/-- Proof-carrying result of the exact two-class port test. -/
inductive PortClass
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (port : Port object center) : Type where
  | open (exact : HighCenterPort.portType object center centerHigh
      deletionCritical port = .open)
  | triangular (exact : HighCenterPort.portType object center centerHigh
      deletionCritical port = .triangular)

def classifyPort
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (port : Port object center) :
    PortClass object center centerHigh deletionCritical port := by
  by_cases openExact : HighCenterPort.portType object center centerHigh
      deletionCritical port = .open
  · exact .open openExact
  · have triangularExact : HighCenterPort.portType object center centerHigh
        deletionCritical port = .triangular := by
      cases typeEq : HighCenterPort.portType object center centerHigh
        deletionCritical port
      · exact (openExact typeEq).elim
      · rfl
    exact .triangular triangularExact

/-- The four exhaustive ordered type pairs. -/
inductive PairCase
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (first second : Port object center) : Type where
  | openOpen
      (firstExact : HighCenterPort.portType object center centerHigh
        deletionCritical first = .open)
      (secondExact : HighCenterPort.portType object center centerHigh
        deletionCritical second = .open)
  | openTriangular
      (firstExact : HighCenterPort.portType object center centerHigh
        deletionCritical first = .open)
      (secondExact : HighCenterPort.portType object center centerHigh
        deletionCritical second = .triangular)
  | triangularOpen
      (firstExact : HighCenterPort.portType object center centerHigh
        deletionCritical first = .triangular)
      (secondExact : HighCenterPort.portType object center centerHigh
        deletionCritical second = .open)
  | triangularTriangular
      (firstExact : HighCenterPort.portType object center centerHigh
        deletionCritical first = .triangular)
      (secondExact : HighCenterPort.portType object center centerHigh
        deletionCritical second = .triangular)

def classifyPairCase
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (first second : Port object center) :
    PairCase object center centerHigh deletionCritical first second := by
  cases firstEq : HighCenterPort.portType object center centerHigh
      deletionCritical first <;>
    cases secondEq : HighCenterPort.portType object center centerHigh
      deletionCritical second
  · exact .openOpen firstEq secondEq
  · exact .openTriangular firstEq secondEq
  · exact .triangularOpen firstEq secondEq
  · exact .triangularTriangular firstEq secondEq

/-- A typed first failed field of the literal fan-compatibility predicate. -/
inductive FanFailure (first second : Port object center) : Type u where
  | firstEndpointInSecondShoulders
      (member : HighCenterPort.endpoint object center first ∈
        HighCenterPort.shoulderVertices object center second)
  | secondEndpointInFirstShoulders
      (firstOutside : HighCenterPort.endpoint object center first ∉
        HighCenterPort.shoulderVertices object center second)
      (member : HighCenterPort.endpoint object center second ∈
        HighCenterPort.shoulderVertices object center first)
  | shouldersNotDisjoint
      (firstOutside : HighCenterPort.endpoint object center first ∉
        HighCenterPort.shoulderVertices object center second)
      (secondOutside : HighCenterPort.endpoint object center second ∉
        HighCenterPort.shoulderVertices object center first)
      (failure : ¬List.Disjoint
        (HighCenterPort.shoulderVertices object center first)
        (HighCenterPort.shoulderVertices object center second))

/-- Exact success, or a proof-carrying failed compatibility field. -/
inductive FanDecision (first second : Port object center) : Type u where
  | compatible (exact : HighCenterPort.FanCompatible object center first second)
  | failed (residual : FanFailure object center first second)

noncomputable def classifyFan (first second : Port object center) :
    FanDecision object center first second := by
  letI : DecidableEq V := object.input.vertices.decEq
  by_cases firstOutside : HighCenterPort.endpoint object center first ∉
      HighCenterPort.shoulderVertices object center second
  · by_cases secondOutside : HighCenterPort.endpoint object center second ∉
        HighCenterPort.shoulderVertices object center first
    · by_cases disjoint : List.Disjoint
        (HighCenterPort.shoulderVertices object center first)
        (HighCenterPort.shoulderVertices object center second)
      · exact .compatible ⟨firstOutside, secondOutside, disjoint⟩
      · exact .failed (.shouldersNotDisjoint firstOutside secondOutside disjoint)
    · exact .failed (.secondEndpointInFirstShoulders firstOutside
        (by simpa using secondOutside))
  · exact .failed (.firstEndpointInSecondShoulders (by simpa using firstOutside))

theorem failure_not_compatible {first second : Port object center}
    (failure : FanFailure object center first second) :
    ¬HighCenterPort.FanCompatible object center first second := by
  intro compatible
  rcases compatible with ⟨firstOutside, secondOutside, disjoint⟩
  cases failure with
  | firstEndpointInSecondShoulders member => exact firstOutside member
  | secondEndpointInFirstShoulders _ member => exact secondOutside member
  | shouldersNotDisjoint _ _ failed => exact failed disjoint

/-- A shared shoulder of two distinct ports is a literal four-cycle with the
common centre. -/
theorem hasFourCycle_of_shouldersNotDisjoint
    {first second : Port object center} (distinct : first ≠ second)
    (failure : ¬List.Disjoint
      (HighCenterPort.shoulderVertices object center first)
      (HighCenterPort.shoulderVertices object center second)) :
    HasCycleWithLength object.graph HighCenterStructure.FourLength := by
  classical
  by_contra fourFree
  apply failure
  rw [List.disjoint_left]
  intro common commonFirst commonSecond
  have endpointsNe : HighCenterPort.endpoint object center first ≠
      HighCenterPort.endpoint object center second := fun equal =>
    distinct (HighCenterPort.endpoint_injective object center equal)
  have commonNeCenter :=
    HighCenterPort.ne_center_of_mem_shoulders object center first commonFirst
  apply fourFree
  exact ⟨HighCenterStructure.squareCycle
    (HighCenterPort.endpoint_adjacent object center first)
    (HighCenterPort.adjacent_of_mem_shoulders object center first commonFirst)
    (HighCenterPort.adjacent_of_mem_shoulders object center second
      commonSecond).symm
    (HighCenterPort.endpoint_adjacent object center second).symm
    commonNeCenter.symm endpointsNe⟩

/-- If one port endpoint is a shoulder of a distinct triangular port, its
triangle edge and the common centre form a literal four-cycle. -/
theorem hasFourCycle_of_endpoint_mem_shoulders_of_triangular
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {first second : Port object center} (distinct : first ≠ second)
    (member : HighCenterPort.endpoint object center first ∈
      HighCenterPort.shoulderVertices object center second)
    (triangular : HighCenterPort.portType object center centerHigh
      deletionCritical second = .triangular) :
    HasCycleWithLength object.graph HighCenterStructure.FourLength := by
  have endpointsNe : HighCenterPort.endpoint object center first ≠
      HighCenterPort.endpoint object center second := fun equal =>
    distinct (HighCenterPort.endpoint_injective object center equal)
  rcases HighCenterPort.eq_firstShoulder_or_eq_secondShoulder_of_mem
      object center centerHigh deletionCritical second member with
    firstEq | secondEq
  · exact ⟨HighCenterStructure.squareCycle
      (HighCenterPort.endpoint_adjacent object center first)
      (by
        rw [firstEq]
        exact HighCenterPort.shoulders_adjacent_of_triangular object center
          centerHigh deletionCritical second triangular)
      (HighCenterPort.secondShoulder_adjacent_endpoint object center centerHigh
        deletionCritical second)
      (HighCenterPort.endpoint_adjacent object center second).symm
      (HighCenterPort.ne_center_of_mem_shoulders object center second
        (HighCenterPort.secondShoulder_mem object center centerHigh
          deletionCritical second)).symm endpointsNe⟩
  · exact ⟨HighCenterStructure.squareCycle
      (HighCenterPort.endpoint_adjacent object center first)
      (by
        rw [secondEq]
        exact (HighCenterPort.shoulders_adjacent_of_triangular object center
          centerHigh deletionCritical second triangular).symm)
      (HighCenterPort.firstShoulder_adjacent_endpoint object center centerHigh
        deletionCritical second)
      (HighCenterPort.endpoint_adjacent object center second).symm
      (HighCenterPort.ne_center_of_mem_shoulders object center second
        (HighCenterPort.firstShoulder_mem object center centerHigh
          deletionCritical second)).symm endpointsNe⟩

/-- Symmetric endpoint-in-shoulders square exit. -/
theorem hasFourCycle_of_endpoint_mem_shoulders_of_triangular_first
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {first second : Port object center} (distinct : first ≠ second)
    (member : HighCenterPort.endpoint object center second ∈
      HighCenterPort.shoulderVertices object center first)
    (triangular : HighCenterPort.portType object center centerHigh
      deletionCritical first = .triangular) :
    HasCycleWithLength object.graph HighCenterStructure.FourLength :=
  hasFourCycle_of_endpoint_mem_shoulders_of_triangular object center centerHigh
    deletionCritical distinct.symm member triangular

/-- The same witnessed endpoint edge closes through the triangle at the
source port, even when the witness was stated using the opposite shoulder
list. -/
theorem hasFourCycle_of_endpoint_mem_opposite_shoulders_of_triangular_first
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {first second : Port object center} (distinct : first ≠ second)
    (member : HighCenterPort.endpoint object center first ∈
      HighCenterPort.shoulderVertices object center second)
    (triangular : HighCenterPort.portType object center centerHigh
      deletionCritical first = .triangular) :
    HasCycleWithLength object.graph HighCenterStructure.FourLength := by
  have endpointAdjacent : object.graph.Adj
      (HighCenterPort.endpoint object center first)
      (HighCenterPort.endpoint object center second) :=
    (HighCenterPort.adjacent_of_mem_shoulders object center second member).symm
  have secondNeCenter : HighCenterPort.endpoint object center second ≠ center :=
    (HighCenterPort.endpoint_adjacent object center second).ne.symm
  have symmetricMember :=
    HighCenterPort.mem_shoulders_of_adjacent_endpoint_of_ne_center object center
      first endpointAdjacent secondNeCenter
  exact hasFourCycle_of_endpoint_mem_shoulders_of_triangular_first object center
    centerHigh deletionCritical distinct symmetricMember triangular

/-- Symmetric source-triangular form. -/
theorem hasFourCycle_of_opposite_endpoint_mem_shoulders_of_triangular_second
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {first second : Port object center} (distinct : first ≠ second)
    (member : HighCenterPort.endpoint object center second ∈
      HighCenterPort.shoulderVertices object center first)
    (triangular : HighCenterPort.portType object center centerHigh
      deletionCritical second = .triangular) :
    HasCycleWithLength object.graph HighCenterStructure.FourLength :=
  hasFourCycle_of_endpoint_mem_opposite_shoulders_of_triangular_first object
    center centerHigh deletionCritical distinct.symm member triangular

namespace FanDecision

/-- Semantic validity of a compatibility decision.  Failure firstness is
stored directly in the residual constructors. -/
def Valid {first second : Port object center} :
    FanDecision object center first second → Prop
  | .compatible _exact => HighCenterPort.FanCompatible object center first second
  | .failed _residual => ¬HighCenterPort.FanCompatible object center first second

theorem valid {first second : Port object center}
    (decision : FanDecision object center first second) : decision.Valid := by
  cases decision with
  | compatible exact => exact exact
  | failed residual => exact failure_not_compatible object center residual

end FanDecision

theorem classifyFan_valid (first second : Port object center) :
    (classifyFan object center first second).Valid :=
  FanDecision.valid object center _

/-- Complete local pair table.  It classifies only the supplied ports and
does not claim that either port is a canonical surplus slot. -/
structure PairTable
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (first second : Port object center) where
  typeCase : PairCase object center centerHigh deletionCritical first second
  fan : FanDecision object center first second

noncomputable def pairTable
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (first second : Port object center) :
    PairTable object center centerHigh deletionCritical first second where
  typeCase := classifyPairCase object center centerHigh deletionCritical first second
  fan := classifyFan object center first second

/-- Root-high table: the divergent pair is tabulated and the recovered third
port is classified separately.  Deletion criticality is explicit because it
is not a field of `RootHigh`; caller provenance is retained verbatim. -/
structure RootResult
    {divergence : RootIncidence.Divergence object center}
    {third : RootIncidence.Third object center divergence}
    {Provenance : Type v}
    (output : HighSeparatorPort.RootHigh object divergence third Provenance)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) where
  divergent : PairTable object center output.centerHigh deletionCritical
    output.leftPort output.rightPort
  thirdClass : PortClass object center output.centerHigh deletionCritical
    output.thirdPort
  provenance : Provenance

noncomputable def classifyRoot
    {divergence : RootIncidence.Divergence object center}
    {third : RootIncidence.Third object center divergence}
    {Provenance : Type v}
    (output : HighSeparatorPort.RootHigh object divergence third Provenance)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    RootResult object center output deletionCritical where
  divergent := pairTable object center output.centerHigh deletionCritical
    output.leftPort output.rightPort
  thirdClass := classifyPort object center output.centerHigh deletionCritical
    output.thirdPort
  provenance := output.provenance

/-- After-edge table: predecessor is classified, while the two outgoing
divergent ports form the exhaustive ordered pair table. -/
structure AfterEdgeResult
    {incidence : RootIncidence.AfterEdge object center}
    {Provenance : Type v}
    (output : HighSeparatorPort.AfterEdgeHigh object incidence Provenance)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) where
  predecessorClass : PortClass object center output.centerHigh deletionCritical
    output.predecessorPort
  divergent : PairTable object center output.centerHigh deletionCritical
    output.leftPort output.rightPort
  provenance : Provenance

noncomputable def classifyAfterEdge
    {incidence : RootIncidence.AfterEdge object center}
    {Provenance : Type v}
    (output : HighSeparatorPort.AfterEdgeHigh object incidence Provenance)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    AfterEdgeResult object center output deletionCritical where
  predecessorClass := classifyPort object center output.centerHigh
    deletionCritical output.predecessorPort
  divergent := pairTable object center output.centerHigh deletionCritical
    output.leftPort output.rightPort
  provenance := output.provenance

/-- Static primitive-predicate currency for one pair classification.  Each
shoulder list has length two under deletion criticality: two chord-adjacency
tests classify the ports, endpoint exclusion uses at most four vertex
equalities, and shoulder disjointness uses at most four pair equalities. -/
structure PredicateBudget where
  chordAdjacency : Nat
  endpointShoulderEquality : Nat
  shoulderPairEquality : Nat

namespace PredicateBudget

def total (budget : PredicateBudget) : Nat :=
  budget.chordAdjacency + budget.endpointShoulderEquality +
    budget.shoulderPairEquality

end PredicateBudget

def classifierBudget : PredicateBudget where
  chordAdjacency := 2
  endpointShoulderEquality := 4
  shoulderPairEquality := 4

/-- Worst-case fixed local predicate budget.  Short-circuiting may use fewer
checks; this is an upper currency, not an exact runtime trace. -/
def checks : Nat := classifierBudget.total

theorem checks_eq_ten : checks = 10 := rfl

end StructuralExhaustion.Graph.HighSeparatorPortClassification
