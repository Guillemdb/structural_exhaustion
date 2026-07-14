import StructuralExhaustion.Graph.AssignedSupportCharge
import StructuralExhaustion.Graph.FanClosedPort

namespace StructuralExhaustion.Graph.AssignedFanCharge

open StructuralExhaustion

universe u

/-!
# Exact assigned fan-neighbour charge

At a high center every neighbour is cubic by deletion criticality.  Its
assigned fan-envelope degree is one center edge plus the number of its two
non-center incidences selected by the support.  This file computes that
degree and the exact augmented quarter charge `11 - 4d_X`; cubic closure and
the `-1`/`3` bounds are derived from the two literal shoulder incidences.
-/

variable {V : Type u} (object : FiniteObject V) (center : V)
variable (centerHigh : 4 ≤ object.degree center)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
variable (Assigned : FanClosedPort.LocalCarrier V → Prop)
variable (assignedDecidable : ∀ carrier, Decidable (Assigned carrier))

/-- Literal closure: both non-center incidences of the cubic endpoint belong
to the assigned fan support. -/
def CubicClosed (port : HighCenterPort.Port object center) : Prop :=
  ∀ other, object.graph.Adj (HighCenterPort.endpoint object center port) other →
    other ≠ center →
      Assigned (HighCenterPort.endpoint object center port, other)

def cubicClosedDecidable : ∀ port, Decidable
    (CubicClosed object center Assigned port) := by
  intro port
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : DecidablePred Assigned := assignedDecidable
  unfold CubicClosed
  infer_instance

def firstAssigned (port : HighCenterPort.Port object center) : Prop :=
  Assigned (HighCenterPort.endpoint object center port,
    HighCenterPort.firstShoulder object center centerHigh deletionCritical port)

def secondAssigned (port : HighCenterPort.Port object center) : Prop :=
  Assigned (HighCenterPort.endpoint object center port,
    HighCenterPort.secondShoulder object center centerHigh deletionCritical port)

def assignedShoulderCount (port : HighCenterPort.Port object center) : Nat :=
  @ite Nat (firstAssigned object center centerHigh deletionCritical Assigned port)
      (assignedDecidable _) 1 0 +
    @ite Nat (secondAssigned object center centerHigh deletionCritical Assigned port)
      (assignedDecidable _) 1 0

def internalDegree (port : HighCenterPort.Port object center) : Nat :=
  1 + assignedShoulderCount object center centerHigh deletionCritical Assigned
    assignedDecidable port

/-- Exact augmented support charge of the neighbour, in quarter units. -/
def quarterCharge (port : HighCenterPort.Port object center) : Int :=
  11 - 4 * (internalDegree object center centerHigh deletionCritical Assigned
    assignedDecidable port : Int)

theorem cubicClosed_iff_both_assigned
    (port : HighCenterPort.Port object center) :
    CubicClosed object center Assigned port ↔
      firstAssigned object center centerHigh deletionCritical Assigned port ∧
        secondAssigned object center centerHigh deletionCritical Assigned port := by
  constructor
  · intro closed
    constructor
    · exact closed _
        (HighCenterPort.firstShoulder_adjacent_endpoint object center centerHigh
          deletionCritical port).symm
        (HighCenterPort.ne_center_of_mem_shoulders object center port
          (HighCenterPort.firstShoulder_mem object center centerHigh
            deletionCritical port))
    · exact closed _
        (HighCenterPort.secondShoulder_adjacent_endpoint object center centerHigh
          deletionCritical port).symm
        (HighCenterPort.ne_center_of_mem_shoulders object center port
          (HighCenterPort.secondShoulder_mem object center centerHigh
            deletionCritical port))
  · rintro ⟨first, second⟩ other adjacent neCenter
    have member := HighCenterPort.mem_shoulders_of_adjacent_endpoint_of_ne_center
      object center port adjacent neCenter
    rcases HighCenterPort.eq_firstShoulder_or_eq_secondShoulder_of_mem object
        center centerHigh deletionCritical port member with equal | equal
    · subst other
      exact first
    · subst other
      exact second

theorem quarterCharge_eq_neg_one_of_cubicClosed
    (port : HighCenterPort.Port object center)
    (closed : CubicClosed object center Assigned port) :
    quarterCharge object center centerHigh deletionCritical Assigned
      assignedDecidable port = -1 := by
  have both := (cubicClosed_iff_both_assigned object center centerHigh
    deletionCritical Assigned port).1 closed
  have first : Assigned (HighCenterPort.endpoint object center port,
      HighCenterPort.firstShoulder object center centerHigh deletionCritical port) := by
    simpa [firstAssigned] using both.1
  have second : Assigned (HighCenterPort.endpoint object center port,
      HighCenterPort.secondShoulder object center centerHigh deletionCritical port) := by
    simpa [secondAssigned] using both.2
  simp [quarterCharge, internalDegree, assignedShoulderCount, firstAssigned,
    secondAssigned, first, second]

theorem quarterCharge_ge_three_of_not_cubicClosed
    (port : HighCenterPort.Port object center)
    (openPort : ¬CubicClosed object center Assigned port) :
    3 ≤ quarterCharge object center centerHigh deletionCritical Assigned
      assignedDecidable port := by
  have notBoth : ¬(firstAssigned object center centerHigh deletionCritical
      Assigned port ∧ secondAssigned object center centerHigh deletionCritical
        Assigned port) := by
    intro both
    exact openPort ((cubicClosed_iff_both_assigned object center centerHigh
      deletionCritical Assigned port).2 both)
  by_cases first : firstAssigned object center centerHigh deletionCritical
      Assigned port
  · have second : ¬secondAssigned object center centerHigh deletionCritical
        Assigned port := fun second => notBoth ⟨first, second⟩
    have first' : Assigned (HighCenterPort.endpoint object center port,
        HighCenterPort.firstShoulder object center centerHigh deletionCritical port) := by
      simpa [firstAssigned] using first
    have second' : ¬Assigned (HighCenterPort.endpoint object center port,
        HighCenterPort.secondShoulder object center centerHigh deletionCritical port) := by
      simpa [secondAssigned] using second
    simp [quarterCharge, internalDegree, assignedShoulderCount, firstAssigned,
      secondAssigned, first', second']
  · by_cases second : secondAssigned object center centerHigh deletionCritical
        Assigned port
    · have first' : ¬Assigned (HighCenterPort.endpoint object center port,
          HighCenterPort.firstShoulder object center centerHigh deletionCritical port) := by
        simpa [firstAssigned] using first
      have second' : Assigned (HighCenterPort.endpoint object center port,
          HighCenterPort.secondShoulder object center centerHigh deletionCritical port) := by
        simpa [secondAssigned] using second
      simp [quarterCharge, internalDegree, assignedShoulderCount, firstAssigned,
        secondAssigned, first', second']
    · have first' : ¬Assigned (HighCenterPort.endpoint object center port,
          HighCenterPort.firstShoulder object center centerHigh deletionCritical port) := by
        simpa [firstAssigned] using first
      have second' : ¬Assigned (HighCenterPort.endpoint object center port,
          HighCenterPort.secondShoulder object center centerHigh deletionCritical port) := by
        simpa [secondAssigned] using second
      simp [quarterCharge, internalDegree, assignedShoulderCount, firstAssigned,
        secondAssigned, first', second']

/-- The assigned fan charge is a lower bound for the literal induced-core
charge whenever every core incidence at the cubic endpoint is assigned.
External/window incidences may also be assigned; they only decrease the local
lower bound and therefore remain safe. -/
theorem quarterCharge_le_inducedCoreQuarterCharge
    (core : Finset V) (port : HighCenterPort.Port object center)
    (internalAssigned : ∀ other,
      object.graph.Adj (HighCenterPort.endpoint object center port) other →
      other ∈ core → other ≠ center →
        Assigned (HighCenterPort.endpoint object center port, other)) :
    quarterCharge object center centerHigh deletionCritical Assigned
        assignedDecidable port ≤
      4 * ((3 -
        (letI : FinEnum V := object.input.vertices
         letI : DecidableEq V := object.input.vertices.decEq
         letI : DecidableRel object.graph.Adj := object.input.decideAdj
         (object.graph.neighborFinset
            (HighCenterPort.endpoint object center port) ∩ core).card) : Nat) : Int) - 1 := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  let endpoint := HighCenterPort.endpoint object center port
  let first := HighCenterPort.firstShoulder object center centerHigh
    deletionCritical port
  let second := HighCenterPort.secondShoulder object center centerHigh
    deletionCritical port
  let coreNeighbors := object.graph.neighborFinset endpoint ∩ core
  have endpointCubic : object.degree endpoint = 3 :=
    HighCenterPort.endpoint_cubic object center centerHigh deletionCritical port
  have firstAdj : object.graph.Adj endpoint first := by
    exact (HighCenterPort.firstShoulder_adjacent_endpoint object center
      centerHigh deletionCritical port).symm
  have secondAdj : object.graph.Adj endpoint second := by
    exact (HighCenterPort.secondShoulder_adjacent_endpoint object center
      centerHigh deletionCritical port).symm
  have firstNeCenter : first ≠ center := by
    exact HighCenterPort.ne_center_of_mem_shoulders object center port
      (HighCenterPort.firstShoulder_mem object center centerHigh
        deletionCritical port)
  have secondNeCenter : second ≠ center := by
    exact HighCenterPort.ne_center_of_mem_shoulders object center port
      (HighCenterPort.secondShoulder_mem object center centerHigh
        deletionCritical port)
  have firstNeSecond : first ≠ second := by
    exact HighCenterPort.firstShoulder_ne_secondShoulder object center
      centerHigh deletionCritical port
  have subsetThree : coreNeighbors ⊆ {center, first, second} := by
    intro other member
    have adjacent : object.graph.Adj endpoint other := by
      simpa [SimpleGraph.mem_neighborFinset] using
        (Finset.mem_inter.mp member).1
    by_cases equalCenter : other = center
    · subst other
      simp
    · have shoulderMember :=
        HighCenterPort.mem_shoulders_of_adjacent_endpoint_of_ne_center
          object center port adjacent equalCenter
      rcases HighCenterPort.eq_firstShoulder_or_eq_secondShoulder_of_mem
          object center centerHigh deletionCritical port shoulderMember with
        equalFirst | equalSecond
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Or.inl equalFirst)
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Or.inr equalSecond)
  have coreDegreeLeThree : coreNeighbors.card ≤ 3 := by
    calc
      coreNeighbors.card ≤ ({center, first, second} : Finset V).card :=
        Finset.card_le_card subsetThree
      _ = 3 := by
        simp [firstNeSecond,
          Ne.symm firstNeCenter, Ne.symm secondNeCenter]
  have firstCore_of_notAssigned
      (notAssigned : ¬Assigned (endpoint, first)) : first ∉ core := by
    intro firstCore
    exact notAssigned (internalAssigned first firstAdj firstCore firstNeCenter)
  have secondCore_of_notAssigned
      (notAssigned : ¬Assigned (endpoint, second)) : second ∉ core := by
    intro secondCore
    exact notAssigned (internalAssigned second secondAdj secondCore secondNeCenter)
  have coreDegree_le_assigned :
      coreNeighbors.card ≤
        internalDegree object center centerHigh deletionCritical Assigned
          assignedDecidable port := by
    by_cases firstIsAssigned : Assigned (endpoint, first)
    · by_cases secondIsAssigned : Assigned (endpoint, second)
      · simp [internalDegree, assignedShoulderCount, firstAssigned,
          secondAssigned, endpoint, first, second, firstIsAssigned,
          secondIsAssigned]
        exact coreDegreeLeThree
      · have secondNotCore := secondCore_of_notAssigned secondIsAssigned
        have subsetTwo : coreNeighbors ⊆ {center, first} := by
          intro other member
          have three := subsetThree member
          simp only [Finset.mem_insert, Finset.mem_singleton] at three ⊢
          rcases three with equalCenter | equalFirst | equalSecond
          · exact Or.inl equalCenter
          · exact Or.inr equalFirst
          · subst other
            exact False.elim (secondNotCore (Finset.mem_inter.mp member).2)
        have degreeLeTwo : coreNeighbors.card ≤ 2 := by
          calc
            coreNeighbors.card ≤ ({center, first} : Finset V).card :=
              Finset.card_le_card subsetTwo
            _ = 2 := by simp [Ne.symm firstNeCenter]
        simp [internalDegree, assignedShoulderCount, firstAssigned,
          secondAssigned, endpoint, first, second, firstIsAssigned,
          secondIsAssigned]
        exact degreeLeTwo
    · have firstNotCore := firstCore_of_notAssigned firstIsAssigned
      by_cases secondIsAssigned : Assigned (endpoint, second)
      · have subsetTwo : coreNeighbors ⊆ {center, second} := by
          intro other member
          have three := subsetThree member
          simp only [Finset.mem_insert, Finset.mem_singleton] at three ⊢
          rcases three with equalCenter | equalFirst | equalSecond
          · exact Or.inl equalCenter
          · subst other
            exact False.elim (firstNotCore (Finset.mem_inter.mp member).2)
          · exact Or.inr equalSecond
        have degreeLeTwo : coreNeighbors.card ≤ 2 := by
          calc
            coreNeighbors.card ≤ ({center, second} : Finset V).card :=
              Finset.card_le_card subsetTwo
            _ = 2 := by simp [Ne.symm secondNeCenter]
        simp [internalDegree, assignedShoulderCount, firstAssigned,
          secondAssigned, endpoint, first, second, firstIsAssigned,
          secondIsAssigned]
        exact degreeLeTwo
      · have secondNotCore := secondCore_of_notAssigned secondIsAssigned
        have subsetOne : coreNeighbors ⊆ {center} := by
          intro other member
          have three := subsetThree member
          simp only [Finset.mem_insert, Finset.mem_singleton] at three ⊢
          rcases three with equalCenter | equalFirst | equalSecond
          · exact equalCenter
          · subst other
            exact False.elim (firstNotCore (Finset.mem_inter.mp member).2)
          · subst other
            exact False.elim (secondNotCore (Finset.mem_inter.mp member).2)
        have degreeLeOne : coreNeighbors.card ≤ 1 := by
          calc
            coreNeighbors.card ≤ ({center} : Finset V).card :=
              Finset.card_le_card subsetOne
            _ = 1 := Finset.card_singleton center
        simp [internalDegree, assignedShoulderCount, firstAssigned,
          secondAssigned, endpoint, first, second, firstIsAssigned,
          secondIsAssigned]
        exact degreeLeOne
  have assignedDegreeLeThree :
      internalDegree object center centerHigh deletionCritical Assigned
          assignedDecidable port ≤ 3 := by
    unfold internalDegree assignedShoulderCount
    split <;> split <;> simp
  unfold quarterCharge
  change 11 - 4 *
      (internalDegree object center centerHigh deletionCritical Assigned
        assignedDecidable port : Int) ≤
    4 * ((3 - coreNeighbors.card : Nat) : Int) - 1
  omega

/-- Assigned shoulder incidences that leave the counted core. -/
noncomputable def externalAssignedShoulderCount
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (Assigned : FanClosedPort.LocalCarrier V → Prop)
    (assignedDecidable : ∀ carrier, Decidable (Assigned carrier))
    (core : Finset V)
    (port : HighCenterPort.Port object center) : Nat := by
  letI : DecidableEq V := object.input.vertices.decEq
  letI : Decidable (firstAssigned object center centerHigh deletionCritical
      Assigned port) := assignedDecidable _
  letI : Decidable (secondAssigned object center centerHigh deletionCritical
      Assigned port) := assignedDecidable _
  exact
    (if firstAssigned object center centerHigh deletionCritical Assigned port ∧
        HighCenterPort.firstShoulder object center centerHigh deletionCritical
          port ∉ core then 1 else 0) +
      (if secondAssigned object center centerHigh deletionCritical Assigned port ∧
        HighCenterPort.secondShoulder object center centerHigh deletionCritical
          port ∉ core then 1 else 0)

/-- Each assigned shoulder that leaves the induced core contributes four
quarter-units of literal core-charge correction. -/
theorem quarterCharge_add_externalCorrection_le_inducedCoreQuarterCharge
    (core : Finset V) (centerMem : center ∈ core)
    (port : HighCenterPort.Port object center)
    (internalAssigned : ∀ other,
      object.graph.Adj (HighCenterPort.endpoint object center port) other →
      other ∈ core → other ≠ center →
        Assigned (HighCenterPort.endpoint object center port, other)) :
    quarterCharge object center centerHigh deletionCritical Assigned
        assignedDecidable port +
        4 * (externalAssignedShoulderCount object center centerHigh
          deletionCritical Assigned assignedDecidable core port : Int) ≤
      4 * ((3 -
        (letI : FinEnum V := object.input.vertices
         letI : DecidableEq V := object.input.vertices.decEq
         letI : DecidableRel object.graph.Adj := object.input.decideAdj
         (object.graph.neighborFinset
            (HighCenterPort.endpoint object center port) ∩ core).card) : Nat) : Int) - 1 := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  let endpoint := HighCenterPort.endpoint object center port
  let first := HighCenterPort.firstShoulder object center centerHigh
    deletionCritical port
  let second := HighCenterPort.secondShoulder object center centerHigh
    deletionCritical port
  let coreDegree := (object.graph.neighborFinset endpoint ∩ core).card
  change quarterCharge object center centerHigh deletionCritical Assigned
      assignedDecidable port +
      4 * (externalAssignedShoulderCount object center centerHigh
        deletionCritical Assigned assignedDecidable core port : Int) ≤
    4 * ((3 - coreDegree : Nat) : Int) - 1
  have degreeEq := HighCenterPort.inducedCoreDegree_eq_one_add_shoulders
    object center centerHigh deletionCritical core centerMem port
  change coreDegree =
      1 + (if first ∈ core then 1 else 0) +
        (if second ∈ core then 1 else 0) at degreeEq
  have firstAdj : object.graph.Adj endpoint first := by
    exact (HighCenterPort.firstShoulder_adjacent_endpoint object center
      centerHigh deletionCritical port).symm
  have secondAdj : object.graph.Adj endpoint second := by
    exact (HighCenterPort.secondShoulder_adjacent_endpoint object center
      centerHigh deletionCritical port).symm
  have firstNeCenter : first ≠ center :=
    HighCenterPort.ne_center_of_mem_shoulders object center port
      (HighCenterPort.firstShoulder_mem object center centerHigh
        deletionCritical port)
  have secondNeCenter : second ≠ center :=
    HighCenterPort.ne_center_of_mem_shoulders object center port
      (HighCenterPort.secondShoulder_mem object center centerHigh
        deletionCritical port)
  have firstAssignedOfCore (member : first ∈ core) :
      Assigned (endpoint, first) :=
    internalAssigned first firstAdj member firstNeCenter
  have secondAssignedOfCore (member : second ∈ core) :
      Assigned (endpoint, second) :=
    internalAssigned second secondAdj member secondNeCenter
  by_cases firstIsAssigned : Assigned (endpoint, first) <;>
    by_cases secondIsAssigned : Assigned (endpoint, second) <;>
      by_cases firstCore : first ∈ core <;>
        by_cases secondCore : second ∈ core
  all_goals
    simp_all [quarterCharge, internalDegree, assignedShoulderCount,
      externalAssignedShoulderCount, firstAssigned, secondAssigned,
      endpoint, first, second]

end StructuralExhaustion.Graph.AssignedFanCharge
