import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Core.FiniteRefinedLedger

universe uDemand uCandidate uCarrier

/-!
# Finite refined ledgers

This core profile separates a finite demand schedule from the finite candidate
entries available at each demand.  It states the exact global alternative:
either one candidate can be chosen at every demand with pairwise-disjoint
carrier supports, or the full demand schedule is already an overlap
obstruction.  The theorem is proof-level and never enumerates candidate
products or demand subsets.
-/

structure Profile (Demand : Type uDemand) (Carrier : Type uCarrier) where
  Candidate : Demand → Type uCandidate
  demands : FinEnum Demand
  finiteCandidates : ∀ demand, Finite (Candidate demand)
  carrierSupport : (demand : Demand) → Candidate demand → Finset Carrier
  demandSupport : Demand → Finset Carrier
  carrierSupport_subset : ∀ demand candidate,
    carrierSupport demand candidate ⊆ demandSupport demand

namespace Profile

variable {Demand : Type uDemand} {Carrier : Type uCarrier}
variable (profile : Profile.{uDemand, uCandidate, uCarrier} Demand Carrier)

/-- A dependent choice of one entry at every demand in an explicit schedule,
with pairwise-disjoint carrier supports. -/
structure Choice (selected : List Demand) where
  entry : (demand : {demand // demand ∈ selected}) →
    profile.Candidate demand.1
  pairwiseDisjoint : ∀ left right,
    left.1 ≠ right.1 →
      Disjoint
        (profile.carrierSupport left.1 (entry left))
        (profile.carrierSupport right.1 (entry right))

/-- Carrier disjointness remains valid for any literal support extracted from
each chosen candidate, provided that extracted support is a subset of the
candidate carrier.  This is the reusable bridge from an abstract CT12 choice
to the concrete resources consumed by a downstream ledger. -/
theorem Choice.refinedSupport_pairwiseDisjoint
    {selected : List Demand}
    (choice : profile.Choice selected)
    (refinedSupport : (demand : Demand) →
      profile.Candidate demand → Finset Carrier)
    (refined_subset : ∀ demand candidate,
      refinedSupport demand candidate ⊆
        profile.carrierSupport demand candidate)
    (left right : {demand // demand ∈ selected})
    (distinct : left.1 ≠ right.1) :
    Disjoint
      (refinedSupport left.1 (choice.entry left))
      (refinedSupport right.1 (choice.entry right)) :=
  (choice.pairwiseDisjoint left right distinct).mono
    (refined_subset left.1 (choice.entry left))
    (refined_subset right.1 (choice.entry right))

/-- Combine choices on two scheduled blocks when every declared demand
support on the left is disjoint from every declared demand support on the
right. -/
noncomputable def Choice.append {left right : List Demand}
    (leftChoice : profile.Choice left)
    (rightChoice : profile.Choice right)
    (crossDisjoint : ∀ leftDemand, leftDemand ∈ left →
      ∀ rightDemand, rightDemand ∈ right →
        Disjoint (profile.demandSupport leftDemand)
          (profile.demandSupport rightDemand)) :
    profile.Choice (left ++ right) where
  entry := fun demand => by
    classical
    by_cases inLeft : demand.1 ∈ left
    · exact leftChoice.entry ⟨demand.1, inLeft⟩
    · have inRight : demand.1 ∈ right :=
        (List.mem_append.mp demand.2).resolve_left inLeft
      exact rightChoice.entry ⟨demand.1, inRight⟩
  pairwiseDisjoint := by
    classical
    intro first second distinct
    by_cases firstLeft : first.1 ∈ left
    · by_cases secondLeft : second.1 ∈ left
      · have separated := leftChoice.pairwiseDisjoint
          ⟨first.1, firstLeft⟩ ⟨second.1, secondLeft⟩ distinct
        simpa [firstLeft, secondLeft] using separated
      · have secondRight : second.1 ∈ right :=
          (List.mem_append.mp second.2).resolve_left secondLeft
        let firstCandidate := leftChoice.entry ⟨first.1, firstLeft⟩
        let secondCandidate := rightChoice.entry ⟨second.1, secondRight⟩
        have separated : Disjoint
            (profile.carrierSupport first.1 firstCandidate)
            (profile.carrierSupport second.1 secondCandidate) :=
          (crossDisjoint first.1 firstLeft second.1 secondRight).mono
          (profile.carrierSupport_subset first.1 firstCandidate)
          (profile.carrierSupport_subset second.1 secondCandidate)
        simpa [firstLeft, secondLeft, firstCandidate, secondCandidate] using separated
    · have firstRight : first.1 ∈ right :=
        (List.mem_append.mp first.2).resolve_left firstLeft
      by_cases secondLeft : second.1 ∈ left
      · let firstCandidate := rightChoice.entry ⟨first.1, firstRight⟩
        let secondCandidate := leftChoice.entry ⟨second.1, secondLeft⟩
        have separated : Disjoint
            (profile.carrierSupport first.1 firstCandidate)
            (profile.carrierSupport second.1 secondCandidate) :=
          ((crossDisjoint second.1 secondLeft first.1 firstRight).mono
            (profile.carrierSupport_subset second.1 secondCandidate)
            (profile.carrierSupport_subset first.1 firstCandidate)).symm
        simpa [firstLeft, secondLeft, firstCandidate, secondCandidate] using separated
      · have secondRight : second.1 ∈ right :=
          (List.mem_append.mp second.2).resolve_left secondLeft
        have separated := rightChoice.pairwiseDisjoint
          ⟨first.1, firstRight⟩ ⟨second.1, secondRight⟩ distinct
        simpa [firstLeft, secondLeft] using separated

/-- Merge choices on two disjoint scheduled subfamilies whose union covers an
ambient schedule.  Unlike `Choice.append`, the two blocks need not occur as a
prefix and suffix of the ambient list. -/
noncomputable def Choice.merge {selected left right : List Demand}
    (leftChoice : profile.Choice left)
    (rightChoice : profile.Choice right)
    (cover : ∀ demand, demand ∈ selected → demand ∈ left ∨ demand ∈ right)
    (crossDisjoint : ∀ leftDemand, leftDemand ∈ left →
      ∀ rightDemand, rightDemand ∈ right →
        Disjoint (profile.demandSupport leftDemand)
          (profile.demandSupport rightDemand)) :
    profile.Choice selected where
  entry := fun demand => by
    classical
    by_cases inLeft : demand.1 ∈ left
    · exact leftChoice.entry ⟨demand.1, inLeft⟩
    · have inRight : demand.1 ∈ right :=
        (cover demand.1 demand.2).resolve_left inLeft
      exact rightChoice.entry ⟨demand.1, inRight⟩
  pairwiseDisjoint := by
    classical
    intro first second distinct
    by_cases firstLeft : first.1 ∈ left
    · by_cases secondLeft : second.1 ∈ left
      · have separated := leftChoice.pairwiseDisjoint
          ⟨first.1, firstLeft⟩ ⟨second.1, secondLeft⟩ distinct
        simpa [firstLeft, secondLeft] using separated
      · have secondRight : second.1 ∈ right :=
          (cover second.1 second.2).resolve_left secondLeft
        let firstCandidate := leftChoice.entry ⟨first.1, firstLeft⟩
        let secondCandidate := rightChoice.entry ⟨second.1, secondRight⟩
        have separated : Disjoint
            (profile.carrierSupport first.1 firstCandidate)
            (profile.carrierSupport second.1 secondCandidate) :=
          (crossDisjoint first.1 firstLeft second.1 secondRight).mono
            (profile.carrierSupport_subset first.1 firstCandidate)
            (profile.carrierSupport_subset second.1 secondCandidate)
        simpa [firstLeft, secondLeft, firstCandidate, secondCandidate] using separated
    · have firstRight : first.1 ∈ right :=
        (cover first.1 first.2).resolve_left firstLeft
      by_cases secondLeft : second.1 ∈ left
      · let firstCandidate := rightChoice.entry ⟨first.1, firstRight⟩
        let secondCandidate := leftChoice.entry ⟨second.1, secondLeft⟩
        have separated : Disjoint
            (profile.carrierSupport first.1 firstCandidate)
            (profile.carrierSupport second.1 secondCandidate) :=
          ((crossDisjoint second.1 secondLeft first.1 firstRight).mono
            (profile.carrierSupport_subset second.1 secondCandidate)
            (profile.carrierSupport_subset first.1 firstCandidate)).symm
        simpa [firstLeft, secondLeft, firstCandidate, secondCandidate] using separated
      · have secondRight : second.1 ∈ right :=
          (cover second.1 second.2).resolve_left secondLeft
        have separated := rightChoice.pairwiseDisjoint
          ⟨first.1, firstRight⟩ ⟨second.1, secondRight⟩ distinct
        simpa [firstLeft, secondLeft] using separated

/-- A nonempty scheduled demand family for which no disjoint candidate choice
exists. -/
structure OverlapObstruction (selected : List Demand) : Prop where
  nonempty : selected ≠ []
  noChoice : ¬Nonempty (profile.Choice selected)

/-- Inclusion-minimal obstruction in the order inherited from the declared
demand schedule.  Because the schedule is duplicate-free, its sublists are
exactly its demand subfamilies with their canonical order retained. -/
structure MinimalOverlapObstruction (selected : List Demand) : Prop where
  obstruction : profile.OverlapObstruction selected
  properChoice : ∀ smaller : List Demand,
    smaller.Sublist selected → smaller ≠ [] →
      smaller.length < selected.length →
        Nonempty (profile.Choice smaller)

/-- An order-independent bipartition of a scheduled obstruction into two
nonempty proper subfamilies with no declared carrier interaction across the
partition. -/
structure SeparatedPartition (selected : List Demand) where
  left : List Demand
  right : List Demand
  cover : ∀ demand, demand ∈ selected ↔ demand ∈ left ∨ demand ∈ right
  membershipDisjoint : ∀ demand, demand ∈ left → demand ∉ right
  left_nonempty : left ≠ []
  right_nonempty : right ≠ []
  left_shorter : left.length < selected.length
  right_shorter : right.length < selected.length
  left_sublist : left.Sublist selected
  right_sublist : right.Sublist selected
  crossDisjoint : ∀ leftDemand, leftDemand ∈ left →
    ∀ rightDemand, rightDemand ∈ right →
      Disjoint (profile.demandSupport leftDemand)
        (profile.demandSupport rightDemand)

/-- A minimal overlap obstruction cannot be partitioned into two carrier-
disjoint nonempty demand blocks.  The partition may interleave in the declared
schedule; no list-order assumption is used. -/
theorem MinimalOverlapObstruction.no_separatedPartition
    {selected : List Demand}
    (minimal : profile.MinimalOverlapObstruction selected) :
    profile.SeparatedPartition selected → False := by
  intro partition
  have leftChoice := Classical.choice (minimal.properChoice partition.left
    partition.left_sublist partition.left_nonempty partition.left_shorter)
  have rightChoice := Classical.choice (minimal.properChoice partition.right
    partition.right_sublist partition.right_nonempty partition.right_shorter)
  have merged : profile.Choice selected :=
    Choice.merge profile leftChoice rightChoice
      (fun demand member => (partition.cover demand).1 member)
      partition.crossDisjoint
  apply minimal.obstruction.noChoice
  exact ⟨merged⟩

/-- Two demands interact when their complete declared carrier universes
overlap. -/
def Interacts (left right : Demand) : Prop :=
  ¬Disjoint (profile.demandSupport left) (profile.demandSupport right)

/-- Reachability in the demand-interaction graph, restricted to the selected
schedule.  The inductive presentation avoids constructing or enumerating a
graph of demand pairs. -/
inductive InteractionReachable (selected : List Demand) (start : Demand) :
    Demand → Prop
  | refl (start_mem : start ∈ selected) : InteractionReachable selected start start
  | step {left right : Demand} :
      InteractionReachable selected start left →
      right ∈ selected → profile.Interacts left right →
      InteractionReachable selected start right

theorem InteractionReachable.target_mem
    {selected : List Demand} {start target : Demand}
    (reachable : profile.InteractionReachable selected start target) :
    target ∈ selected := by
  cases reachable with
  | refl start_mem => exact start_mem
  | step _ right_mem _ => exact right_mem

/-- The interaction graph of every minimal overlap obstruction is connected.
Otherwise its interaction component and complement would form a forbidden
carrier-disjoint bipartition. -/
theorem MinimalOverlapObstruction.interaction_connected
    {selected : List Demand}
    (minimal : profile.MinimalOverlapObstruction selected)
    (start target : Demand)
    (start_mem : start ∈ selected)
    (target_mem : target ∈ selected) :
    profile.InteractionReachable selected start target := by
  classical
  by_contra target_not_reachable
  let ReachableFromStart : Demand → Prop :=
    profile.InteractionReachable selected start
  let left := selected.filter ReachableFromStart
  let right := selected.filter fun demand => ¬ReachableFromStart demand
  have mem_left_iff (demand : Demand) :
      demand ∈ left ↔ demand ∈ selected ∧ ReachableFromStart demand := by
    simp [left]
  have mem_right_iff (demand : Demand) :
      demand ∈ right ↔ demand ∈ selected ∧ ¬ReachableFromStart demand := by
    simp [right]
  have left_sublist : left.Sublist selected := by
    exact List.filter_sublist
  have right_sublist : right.Sublist selected := by
    exact List.filter_sublist
  have start_reachable : ReachableFromStart start :=
    InteractionReachable.refl start_mem
  have start_left : start ∈ left := by
    exact (mem_left_iff start).2 ⟨start_mem, start_reachable⟩
  have target_right : target ∈ right := by
    exact (mem_right_iff target).2 ⟨target_mem, target_not_reachable⟩
  have left_nonempty : left ≠ [] := List.ne_nil_of_mem start_left
  have right_nonempty : right ≠ [] := List.ne_nil_of_mem target_right
  have target_not_left : target ∉ left := by
    intro target_left
    exact target_not_reachable ((mem_left_iff target).1 target_left).2
  have start_not_right : start ∉ right := by
    intro start_right
    exact ((mem_right_iff start).1 start_right).2 start_reachable
  have left_shorter : left.length < selected.length := by
    have lengthLe := left_sublist.length_le
    have lengthNe : left.length ≠ selected.length := by
      intro lengthEq
      have listEq := left_sublist.eq_of_length lengthEq
      exact target_not_left (by simpa [listEq] using target_mem)
    omega
  have right_shorter : right.length < selected.length := by
    have lengthLe := right_sublist.length_le
    have lengthNe : right.length ≠ selected.length := by
      intro lengthEq
      have listEq := right_sublist.eq_of_length lengthEq
      exact start_not_right (by simpa [listEq] using start_mem)
    omega
  have cover : ∀ demand, demand ∈ selected ↔ demand ∈ left ∨ demand ∈ right := by
    intro demand
    constructor
    · intro member
      by_cases reachable : ReachableFromStart demand
      · exact Or.inl ((mem_left_iff demand).2 ⟨member, reachable⟩)
      · exact Or.inr ((mem_right_iff demand).2 ⟨member, reachable⟩)
    · rintro (member | member)
      · exact ((mem_left_iff demand).1 member).1
      · exact ((mem_right_iff demand).1 member).1
  have membershipDisjoint : ∀ demand, demand ∈ left → demand ∉ right := by
    intro demand leftMember rightMember
    exact ((mem_right_iff demand).1 rightMember).2
      ((mem_left_iff demand).1 leftMember).2
  have crossDisjoint : ∀ leftDemand, leftDemand ∈ left →
      ∀ rightDemand, rightDemand ∈ right →
        Disjoint (profile.demandSupport leftDemand)
          (profile.demandSupport rightDemand) := by
    intro leftDemand leftMember rightDemand rightMember
    rw [Finset.disjoint_left]
    intro carrier carrierLeft carrierRight
    have leftReachable : ReachableFromStart leftDemand :=
      ((mem_left_iff leftDemand).1 leftMember).2
    have rightNotReachable : ¬ReachableFromStart rightDemand :=
      ((mem_right_iff rightDemand).1 rightMember).2
    apply rightNotReachable
    exact InteractionReachable.step leftReachable
      ((mem_right_iff rightDemand).1 rightMember).1
      (fun disjoint => (Finset.disjoint_left.mp disjoint) carrierLeft carrierRight)
  apply MinimalOverlapObstruction.no_separatedPartition (profile := profile)
    minimal
  exact {
    left := left
    right := right
    cover := cover
    membershipDisjoint := membershipDisjoint
    left_nonempty := left_nonempty
    right_nonempty := right_nonempty
    left_shorter := left_shorter
    right_shorter := right_shorter
    left_sublist := left_sublist
    right_sublist := right_sublist
    crossDisjoint := crossDisjoint }

abbrev fullSchedule : List Demand := profile.demands.orderedValues

abbrev FullChoice := profile.Choice profile.fullSchedule

abbrev FullObstruction := profile.OverlapObstruction profile.fullSchedule

/-- An empty declared schedule has the unique vacuous dependent choice. -/
def emptyFullChoice (empty : profile.fullSchedule = []) :
    profile.FullChoice where
  entry := fun demand => False.elim (by
    simpa only [empty, List.not_mem_nil] using demand.2)
  pairwiseDisjoint := fun left _right _ne => False.elim (by
    simpa only [empty, List.not_mem_nil] using left.2)

/-- The exact finite B2-style alternative, including the empty demand
schedule.  The proof uses excluded middle on the semantic choice proposition;
it performs no candidate-product or subset enumeration. -/
theorem fullChoice_or_obstruction :
    Nonempty profile.FullChoice ∨ profile.FullObstruction := by
  by_cases empty : profile.fullSchedule = []
  · exact Or.inl ⟨profile.emptyFullChoice empty⟩
  · by_cases choice : Nonempty profile.FullChoice
    · exact Or.inl choice
    · exact Or.inr { noChoice := choice, nonempty := empty }

/-- Every full-family obstruction contains a minimal nonempty obstructing
subschedule.  `Nat.find` selects a least cardinality proof-theoretically; no
subfamily or candidate-product enumeration is executed. -/
theorem exists_minimal_obstruction (full : profile.FullObstruction) :
    ∃ selected : List Demand,
      selected.Sublist profile.fullSchedule ∧
        profile.MinimalOverlapObstruction selected := by
  classical
  let HasObstructionSize : Nat → Prop := fun size =>
    ∃ selected : List Demand,
      selected.Sublist profile.fullSchedule ∧ selected ≠ [] ∧
        selected.length = size ∧
          ¬Nonempty (profile.Choice selected)
  have existsSize : ∃ size, HasObstructionSize size := by
    exact ⟨profile.fullSchedule.length, profile.fullSchedule,
      List.Sublist.refl _, full.nonempty, rfl, full.noChoice⟩
  let minimumSize := Nat.find existsSize
  obtain ⟨selected, selectedSublist, selectedNonempty, selectedLength,
      selectedNoChoice⟩ := Nat.find_spec existsSize
  refine ⟨selected, selectedSublist, {
    obstruction := ⟨selectedNonempty, selectedNoChoice⟩
    properChoice := ?_ }⟩
  intro smaller smallerSublist smallerNonempty smallerLength
  by_contra smallerNoChoice
  have smallerFull : smaller.Sublist profile.fullSchedule :=
    smallerSublist.trans selectedSublist
  have smallerHas : HasObstructionSize smaller.length :=
    ⟨smaller, smallerFull, smallerNonempty, rfl, smallerNoChoice⟩
  have minimumLe := Nat.find_min' existsSize smallerHas
  rw [← selectedLength] at minimumLe
  omega

/-- Choice or a minimal obstruction, valid unconditionally for empty and
nonempty demand schedules. -/
theorem fullChoice_or_minimal_obstruction :
    Nonempty profile.FullChoice ∨
      ∃ selected : List Demand,
        selected.Sublist profile.fullSchedule ∧
          profile.MinimalOverlapObstruction selected := by
  rcases profile.fullChoice_or_obstruction with choice | obstruction
  · exact Or.inl choice
  · exact Or.inr (profile.exists_minimal_obstruction obstruction)

/-- Carrier union of the declared finite carrier universes attached to the
scheduled demands.  Empty valid candidate fibres remain visible here. -/
noncomputable def overlapSupport (selected : List Demand) : Set Carrier := by
  classical
  exact {carrier | ∃ demand, demand ∈ selected ∧
    carrier ∈ profile.demandSupport demand}

theorem mem_overlapSupport_iff (selected : List Demand) (carrier : Carrier) :
    carrier ∈ profile.overlapSupport selected ↔
      ∃ demand, demand ∈ selected ∧
        carrier ∈ profile.demandSupport demand := by
  classical
  rfl

/-- Passing to a demand subschedule can only shrink its candidate-carrier
support. -/
theorem overlapSupport_mono {smaller larger : List Demand}
    (sublist : smaller.Sublist larger) :
    profile.overlapSupport smaller ⊆ profile.overlapSupport larger := by
  intro carrier member
  rcases (profile.mem_overlapSupport_iff smaller carrier).1 member with
    ⟨demand, demandMem, carrierMem⟩
  exact (profile.mem_overlapSupport_iff larger carrier).2
    ⟨demand, sublist.mem demandMem, carrierMem⟩

/-- Generic global-to-local reflection for any support property hereditary
under set inclusion. -/
theorem reflect_hereditary_property
    (Property : Set Carrier → Prop)
    (hereditary : ∀ ⦃smaller larger⦄,
      smaller ⊆ larger → Property larger → Property smaller)
    {selected : List Demand}
    (sublist : selected.Sublist profile.fullSchedule)
    (global : Property (profile.overlapSupport profile.fullSchedule)) :
    Property (profile.overlapSupport selected) :=
  hereditary (profile.overlapSupport_mono sublist) global

end Profile

end StructuralExhaustion.Core.FiniteRefinedLedger
