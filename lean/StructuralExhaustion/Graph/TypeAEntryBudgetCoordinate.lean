import StructuralExhaustion.Graph.TypeAFirstEntryCoordinate
import StructuralExhaustion.Core.WorkBudget

namespace StructuralExhaustion.Graph.TypeAEntryBudgetCoordinate

open StructuralExhaustion
open TypeACanonicalReceiverTrace

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : SupportProfile object)

abbrev Receiver := TypeACompletionPortCoordinate.Receiver object profile
abbrev Port := TypeACompletionPortCoordinate.Coordinate object profile

/-- Actual ambient neighbours of a receiver that remain inside the supplied
support.  This is the complementary local incidence class to completion
ports. -/
abbrev InternalEndpoint (receiver : Receiver object profile) :=
  {neighbor : TypeACompletionPortCoordinate.Neighbor object profile receiver //
    neighbor.1 ∈ profile.support}

private noncomputable def internalEndpointEquivNeighborSet
    (receiver : Receiver object profile) :
    InternalEndpoint object profile receiver ≃
      (profile.supportObject object).graph.neighborSet receiver.1 where
  toFun endpoint := by
    refine ⟨⟨endpoint.1.1, endpoint.2⟩, ?_⟩
    exact endpoint.1.2
  invFun neighbor := by
    refine ⟨⟨neighbor.1.1, ?_⟩, neighbor.1.2⟩
    exact neighbor.2
  left_inv endpoint := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv neighbor := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The completion-port count is exactly ambient degree minus internal degree.
The proof partitions only the three actual neighbour incidences of the fixed
receiver. -/
theorem endpoints_card_eq_three_sub_degree
    (receiver : Receiver object profile) :
    (TypeACompletionPortCoordinate.endpoints object profile receiver).card =
      3 - (profile.supportObject object).degree receiver := by
  letI : FinEnum (TypeACompletionPortCoordinate.Neighbor object profile receiver) :=
    TypeACompletionPortCoordinate.neighbors object profile receiver
  letI : FinEnum (TypeACompletionPortCoordinate.Endpoint object profile receiver) :=
    TypeACompletionPortCoordinate.endpoints object profile receiver
  letI : Fintype (InternalEndpoint object profile receiver) := Fintype.ofFinite _
  letI : Fintype
      ((profile.supportObject object).graph.neighborSet receiver.1) :=
    Fintype.ofFinite _
  have internalCard : Fintype.card (InternalEndpoint object profile receiver) =
      (profile.supportObject object).degree receiver := by
    rw [Fintype.card_congr (internalEndpointEquivNeighborSet object profile receiver)]
    rw [← Nat.card_eq_fintype_card]
    change ((profile.supportObject object).graph.neighborSet receiver.1).ncard =
      (profile.supportObject object).degree receiver
    exact ((profile.supportObject object).degree_eq_ncard_neighborSet receiver).symm
  calc
    (TypeACompletionPortCoordinate.endpoints object profile receiver).card =
        Fintype.card
          (TypeACompletionPortCoordinate.Endpoint object profile receiver) :=
      FinEnum.card_eq_fintypeCard
    _ =
        Fintype.card (TypeACompletionPortCoordinate.Neighbor object profile receiver) -
          Fintype.card (InternalEndpoint object profile receiver) := by
      simpa only [InternalEndpoint] using
        (Fintype.card_subtype_compl
          (fun neighbor : TypeACompletionPortCoordinate.Neighbor object profile receiver =>
            neighbor.1 ∈ profile.support))
    _ = 3 - (profile.supportObject object).degree receiver := by
      rw [internalCard]
      have ambientCard : Fintype.card
          (TypeACompletionPortCoordinate.Neighbor object profile receiver) = 3 := by
        simpa [FinEnum.card_eq_fintypeCard] using
          TypeACompletionPortCoordinate.neighbors_card_eq_three object profile receiver
      rw [ambientCard]

theorem endpoints_card_eq_one_of_degree_eq_two
    (receiver : Receiver object profile)
    (degreeTwo : (profile.supportObject object).degree receiver = 2) :
    (TypeACompletionPortCoordinate.endpoints object profile receiver).card = 1 := by
  rw [endpoints_card_eq_three_sub_degree object profile receiver, degreeTwo]

/-- A degree-two receiver has one literal completion port. -/
theorem port_eq_of_same_degree_two_receiver
    (terminal candidate : Port object profile)
    (degreeTwo : (profile.supportObject object).degree
      (terminal.receiver object profile) = 2)
    (sameReceiver : candidate.receiver object profile =
      terminal.receiver object profile) :
    candidate = terminal := by
  letI : FinEnum (TypeACompletionPortCoordinate.Endpoint object profile terminal.1) :=
    TypeACompletionPortCoordinate.endpoints object profile terminal.1
  obtain ⟨terminalReceiver, terminalEndpoint⟩ := terminal
  obtain ⟨candidateReceiver, candidateEndpoint⟩ := candidate
  change candidateReceiver.1 = terminalReceiver.1 at sameReceiver
  have receiverExact : candidateReceiver = terminalReceiver := Subtype.ext sameReceiver
  subst candidateReceiver
  have endpointCard : Fintype.card
      (TypeACompletionPortCoordinate.Endpoint object profile terminalReceiver) = 1 :=
    by
      simpa [FinEnum.card_eq_fintypeCard] using
        endpoints_card_eq_one_of_degree_eq_two object profile terminalReceiver degreeTwo
  have endpointExact : candidateEndpoint = terminalEndpoint :=
    by
      obtain ⟨only, unique⟩ := Fintype.card_eq_one_iff.mp endpointCard
      exact (unique candidateEndpoint).trans (unique terminalEndpoint).symm
  subst candidateEndpoint
  rfl

/-- The exact completion-port coordinate through which one stored return first
enters the support. -/
def firstEntryPort
    (terminal : Port object profile)
    (anchored : TypeAAnchoredReturnCoordinate.AnchoredReturn object profile terminal)
    (first : TypeAFirstEntryCoordinate.FirstEntry object profile terminal anchored) :
    Port object profile := by
  let receiver : Receiver object profile :=
    ⟨⟨first.entry object profile terminal anchored,
      first.entry_mem_support object profile terminal anchored⟩,
      first.entry_internal_degree_le_two object profile terminal anchored⟩
  let neighbor : TypeACompletionPortCoordinate.Neighbor object profile receiver :=
    ⟨first.predecessor object profile terminal anchored,
      (first.predecessor_adjacent_entry object profile terminal anchored).symm⟩
  let endpoint : TypeACompletionPortCoordinate.Endpoint object profile receiver :=
    ⟨neighbor, first.predecessor_outside object profile terminal anchored⟩
  exact ⟨receiver, endpoint⟩

namespace firstEntryPort

theorem receiver_eq_entry
    (terminal : Port object profile)
    (anchored : TypeAAnchoredReturnCoordinate.AnchoredReturn object profile terminal)
    (first : TypeAFirstEntryCoordinate.FirstEntry object profile terminal anchored) :
    ((firstEntryPort object profile terminal anchored first).receiver object profile).1 =
      first.entry object profile terminal anchored := rfl

theorem outside_eq_predecessor
    (terminal : Port object profile)
    (anchored : TypeAAnchoredReturnCoordinate.AnchoredReturn object profile terminal)
    (first : TypeAFirstEntryCoordinate.FirstEntry object profile terminal anchored) :
    (firstEntryPort object profile terminal anchored first).outside object profile =
      first.predecessor object profile terminal anchored := rfl

end firstEntryPort

/-- The paper's degree-two exclusion for an arbitrary proof-supplied anchored
return. -/
theorem firstEntry_receiver_ne_terminal
    (terminal : Port object profile)
    (degreeTwo : (profile.supportObject object).degree
      (terminal.receiver object profile) = 2)
    (anchored : TypeAAnchoredReturnCoordinate.AnchoredReturn object profile terminal)
    (first : TypeAFirstEntryCoordinate.FirstEntry object profile terminal anchored) :
    (firstEntryPort object profile terminal anchored first).receiver object profile ≠
      terminal.receiver object profile := by
  intro sameReceiver
  have portExact := port_eq_of_same_degree_two_receiver object profile
    terminal (firstEntryPort object profile terminal anchored first) degreeTwo sameReceiver
  have deletedAdj := first.predecessor_adjacent_entry_deleted object profile terminal anchored
  rw [← firstEntryPort.outside_eq_predecessor object profile terminal anchored first,
    ← firstEntryPort.receiver_eq_entry object profile terminal anchored first,
    portExact] at deletedAdj
  exact deletedAdj.2 (by
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨by
        rw [Set.mem_singleton_iff]
        exact Sym2.eq_swap,
      (terminal.receiver_ne_outside object profile).symm⟩)

/-- All distinct external first-entry edges of all anchored returns through one
terminal port, represented only as a subset of the existing finite local port
schedule.  Returns themselves are proof-level witnesses and are not scanned. -/
def possibleFirstEntryEdges (terminal : Port object profile) : Set (Port object profile) :=
  {entryPort | ∃
    (anchored : TypeAAnchoredReturnCoordinate.AnchoredReturn object profile terminal)
    (first : TypeAFirstEntryCoordinate.FirstEntry object profile terminal anchored),
      firstEntryPort object profile terminal anchored first = entryPort}

/-- Receivers other than the terminal receiver. -/
abbrev OtherReceiver (terminal : Port object profile) :=
  {receiver : Receiver object profile // receiver ≠ terminal.1}

/-- Completion ports based at a receiver other than the terminal receiver. -/
abbrev OtherPort (terminal : Port object profile) :=
  {entryPort : Port object profile // entryPort.1 ≠ terminal.1}

private def otherPortEquiv
    (terminal : Port object profile) :
    OtherPort object profile terminal ≃
      Sigma fun receiver : OtherReceiver object profile terminal =>
        TypeACompletionPortCoordinate.Endpoint object profile receiver.1 where
  toFun entryPort := ⟨⟨entryPort.1.1, entryPort.2⟩, entryPort.1.2⟩
  invFun entryPort := ⟨⟨entryPort.1.1, entryPort.2⟩, entryPort.1.2⟩
  left_inv entryPort := by
    apply Subtype.ext
    rfl
  right_inv entryPort := by
    apply Sigma.ext
    · rfl
    · rfl

/-- Exact manuscript quantity: the sum of `q(r)` over receivers other than the
terminal, with `q(r)` realized as the number of actual outside incidences. -/
noncomputable def otherReceiverCapacity (terminal : Port object profile) : Nat := by
  letI : FinEnum (Receiver object profile) :=
    TypeACompletionPortCoordinate.receivers object profile
  letI : (receiver : Receiver object profile) →
      FinEnum (TypeACompletionPortCoordinate.Endpoint object profile receiver) :=
    TypeACompletionPortCoordinate.endpoints object profile
  exact ∑ receiver : OtherReceiver object profile terminal,
    (TypeACompletionPortCoordinate.endpoints object profile receiver.1).card

noncomputable def otherReceiverDeficiencySum
    (terminal : Port object profile) : Nat := by
  letI : FinEnum (Receiver object profile) :=
    TypeACompletionPortCoordinate.receivers object profile
  exact Finset.univ.sum fun receiver : OtherReceiver object profile terminal =>
    3 - (profile.supportObject object).degree receiver.1

theorem otherReceiverCapacity_eq_deficiencySum
    (terminal : Port object profile) :
    otherReceiverCapacity object profile terminal =
      otherReceiverDeficiencySum object profile terminal := by
  letI : FinEnum (Receiver object profile) :=
    TypeACompletionPortCoordinate.receivers object profile
  letI : (receiver : Receiver object profile) →
      FinEnum (TypeACompletionPortCoordinate.Endpoint object profile receiver) :=
    TypeACompletionPortCoordinate.endpoints object profile
  unfold otherReceiverCapacity otherReceiverDeficiencySum
  apply Finset.sum_congr rfl
  intro receiver _member
  exact endpoints_card_eq_three_sub_degree object profile receiver.1

theorem possibleFirstEntryEdges_ncard_le_otherReceiverCapacity
    (terminal : Port object profile)
    (degreeTwo : (profile.supportObject object).degree
      (terminal.receiver object profile) = 2) :
    (possibleFirstEntryEdges object profile terminal).ncard ≤
      otherReceiverCapacity object profile terminal := by
  letI : FinEnum (Receiver object profile) :=
    TypeACompletionPortCoordinate.receivers object profile
  letI : (receiver : Receiver object profile) →
      FinEnum (TypeACompletionPortCoordinate.Endpoint object profile receiver) :=
    TypeACompletionPortCoordinate.endpoints object profile
  let eligible : Set (Port object profile) :=
    {entryPort | entryPort.1 ≠ terminal.1}
  have subset : possibleFirstEntryEdges object profile terminal ⊆ eligible := by
    rintro entryPort ⟨anchored, first, rfl⟩
    intro same
    apply firstEntry_receiver_ne_terminal object profile terminal degreeTwo anchored first
    exact congrArg Subtype.val same
  calc
    (possibleFirstEntryEdges object profile terminal).ncard ≤ eligible.ncard :=
      Set.ncard_le_ncard subset
    _ = otherReceiverCapacity object profile terminal := by
      classical
      rw [Set.ncard_eq_toFinset_card']
      rw [Set.toFinset_card]
      change Fintype.card (OtherPort object profile terminal) =
        otherReceiverCapacity object profile terminal
      rw [Fintype.card_congr (otherPortEquiv object profile terminal)]
      rw [Fintype.card_sigma]
      unfold otherReceiverCapacity
      simp only [FinEnum.card_eq_fintypeCard]
      apply Finset.sum_congr
      · ext receiver
        simp
      · intro receiver _member
        rfl

/-- No extra scan is introduced: the possible-edge family is a logical subset
of the already constructed completion-port schedule. -/
def additionalChecks : Nat := 0

theorem additionalChecks_eq_zero : additionalChecks = 0 := rfl

theorem totalVisibleChecks_polynomial :
    TypeACompletionPortCoordinate.visibleChecks object profile + additionalChecks ≤
      4 * object.input.vertices.card := by
  simpa [additionalChecks] using
    TypeACompletionPortCoordinate.visibleChecks_polynomial object profile

end StructuralExhaustion.Graph.TypeAEntryBudgetCoordinate
