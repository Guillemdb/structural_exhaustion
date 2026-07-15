import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import StructuralExhaustion.Graph.InducedPathPacking
import StructuralExhaustion.Graph.PositiveDeficiencyWedge
import StructuralExhaustion.Graph.SurplusTokenRole

namespace StructuralExhaustion.Graph.InducedPathWindowLedger

open StructuralExhaustion

universe u

variable {V : Type u}

/-!
# Local incidence ledger of a selected induced-path packing

The token universe below scans only the already selected CT12 windows, their
fixed path positions, and the actual neighbours of those positions.  It never
enumerates path embeddings or graph families.  An external incidence is an
ambient edge end not belonging to the induced path edges of its own window.
For pairwise-disjoint induced windows, these are exactly the window--remainder
edge ends and the two window ends of cross-window edges.
-/

private theorem positive_thirteen : 0 < 13 := by decide

abbrev Window (object : FiniteObject V) :=
  InducedPathPacking.Window object 13

noncomputable def windows (object : FiniteObject V) : List (Window object) :=
  InducedPathPacking.windows object 13 positive_thirteen

noncomputable def packingNumber (object : FiniteObject V) : Nat :=
  (windows object).length

theorem packingNumber_eq_inducedPathPacking (object : FiniteObject V) :
    packingNumber object =
      InducedPathPacking.packingNumber object 13 positive_thirteen := rfl

theorem windows_nodup (object : FiniteObject V) : (windows object).Nodup :=
  (InducedPathPacking.profile object 13 positive_thirteen).values_nodup

/-- Unordered selected-window family. -/
noncomputable def selectedWindows (object : FiniteObject V) :
    Finset (Window object) := by
  classical
  exact (windows object).toFinset

theorem selectedWindows_eq_maximum (object : FiniteObject V) :
    selectedWindows object =
      (InducedPathPacking.profile object 13 positive_thirteen).maximum.1 := by
  classical
  let profile := InducedPathPacking.profile object 13 positive_thirteen
  unfold selectedWindows windows InducedPathPacking.windows
  unfold Core.FiniteDisjointPacking.Profile.values
  change profile.maximum.1.toList.toFinset = profile.maximum.1
  exact Finset.toList_toFinset profile.maximum.1

/-- Index in the actual selected CT12 maximum packing. -/
abbrev WindowIndex (object : FiniteObject V) :=
  {window : Window object // window ∈
    selectedWindows object}

/-- The actual selected induced embedding at an index. -/
noncomputable def selectedWindow (object : FiniteObject V)
    (index : WindowIndex object) : Window object :=
  index.1

@[implicit_reducible]
noncomputable def windowIndices (object : FiniteObject V) :
    FinEnum (WindowIndex object) := by
  classical
  exact FinEnum.ofNodupList (selectedWindows object).attach.toList
    (by intro index; simp) (selectedWindows object).attach.nodup_toList

theorem windowIndex_card_eq_packingNumber (object : FiniteObject V) :
    (windowIndices object).card = packingNumber object := by
  classical
  letI : FinEnum (WindowIndex object) := windowIndices object
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_coe]
  change (selectedWindows object).card = (windows object).length
  change (windows object).toFinset.card = (windows object).length
  rw [List.toFinset_card_of_nodup (windows_nodup object)]

/-- Degree in the fixed thirteen-vertex source path. -/
def pathDegree (position : Fin 13) : Nat :=
  if position.val = 0 ∨ position.val = 12 then 1 else 2

/-- Path neighbours of one position, mapped into the host graph. -/
noncomputable def internalNeighbors (object : FiniteObject V)
    (windowIndex : WindowIndex object) (position : Fin 13) : Finset V := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : DecidableRel (SimpleGraph.pathGraph 13).Adj := by
    intro left right
    rw [SimpleGraph.pathGraph_adj]
    infer_instance
  let window := selectedWindow object windowIndex
  exact (Finset.univ.filter fun other : Fin 13 =>
    (SimpleGraph.pathGraph 13).Adj position other).image window

/-- Actual ambient neighbour set with all finite instances installed from the
declared graph input. -/
noncomputable def ambientNeighbors (object : FiniteObject V)
    (windowIndex : WindowIndex object) (position : Fin 13) : Finset V := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact object.graph.neighborFinset
    (selectedWindow object windowIndex position)

/-- Actual ambient neighbours not joined to this position by an internal
edge of its own induced path. -/
noncomputable def externalNeighbors (object : FiniteObject V)
    (windowIndex : WindowIndex object) (position : Fin 13) : Finset V := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact ambientNeighbors object windowIndex position \
    internalNeighbors object windowIndex position

/-- One actual external edge end of one selected window. -/
abbrev Token (object : FiniteObject V) :=
  Sigma fun windowIndex : WindowIndex object =>
    Sigma fun position : Fin 13 =>
      {neighbor : V // neighbor ∈
        externalNeighbors object windowIndex position}

/-- Exact finite token enumeration. -/
@[reducible] noncomputable def tokens (object : FiniteObject V) :
    FinEnum (Token object) := by
  letI : FinEnum (WindowIndex object) := windowIndices object
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  exact inferInstance

/-- The literal local scan count of external window incidences. -/
noncomputable def tokenCount (object : FiniteObject V) : Nat :=
  ∑ windowIndex : WindowIndex object,
    ∑ position : Fin 13,
      (externalNeighbors object windowIndex position).card

/-- Window surplus, summed once over each position of each selected window. -/
noncomputable def windowSurplus (object : FiniteObject V) : Nat :=
  ∑ windowIndex : WindowIndex object,
    ∑ position : Fin 13,
      (object.degree (selectedWindow object windowIndex position) - 3)

/-- Equivalent unordered view: total surplus on the exact covered vertex
set `W`. -/
noncomputable def coveredSurplus (object : FiniteObject V) : Nat :=
  ∑ vertex ∈ InducedPathPacking.coveredVertices object 13 positive_thirteen,
    (object.degree vertex - 3)

/-- Total surplus on the exact complement `R`. -/
noncomputable def remainderSurplus (object : FiniteObject V) : Nat :=
  ∑ vertex ∈ InducedPathPacking.remainderVertices object 13 positive_thirteen,
    (object.degree vertex - 3)

/-- Total degree surplus of the host graph. -/
noncomputable def totalSurplus (object : FiniteObject V) : Nat :=
  (object.input.vertices.orderedValues.map
    (fun vertex => object.degree vertex - 3)).sum

/-- Whether an external incidence joins another packed window or the
remainder.  Because the selected supports are pairwise disjoint, the first
case counts one token at each end of a cross-window edge. -/
noncomputable def tokenSubtype (object : FiniteObject V) (token : Token object) :
    SurplusTokenRole.TokenSubtype := by
  classical
  exact if token.2.2.1 ∈ InducedPathPacking.coveredVertices object 13
      positive_thirteen then
    .crossWindow
  else
    .windowRemainder

theorem internalNeighbors_card (object : FiniteObject V)
    (windowIndex : WindowIndex object) (position : Fin 13) :
    (internalNeighbors object windowIndex position).card =
      pathDegree position := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : DecidableRel (SimpleGraph.pathGraph 13).Adj := by
    intro left right
    rw [SimpleGraph.pathGraph_adj]
    infer_instance
  rw [internalNeighbors, Finset.card_image_of_injective _
    (selectedWindow object windowIndex).injective]
  simp only [SimpleGraph.pathGraph_adj]
  fin_cases position <;> decide

theorem internalNeighbors_subset (object : FiniteObject V)
    (windowIndex : WindowIndex object) (position : Fin 13) :
    internalNeighbors object windowIndex position ⊆
      ambientNeighbors object windowIndex position := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : DecidableRel (SimpleGraph.pathGraph 13).Adj := by
    intro left right
    rw [SimpleGraph.pathGraph_adj]
    infer_instance
  intro vertex member
  rw [internalNeighbors, Finset.mem_image] at member
  rcases member with ⟨source, sourceMember, rfl⟩
  rw [ambientNeighbors, SimpleGraph.mem_neighborFinset]
  exact (selectedWindow object windowIndex).map_adj_iff.mpr
    (Finset.mem_filter.mp sourceMember).2

theorem internal_add_external_eq_degree (object : FiniteObject V)
    (windowIndex : WindowIndex object) (position : Fin 13) :
    (internalNeighbors object windowIndex position).card +
        (externalNeighbors object windowIndex position).card =
      object.degree (selectedWindow object windowIndex position) := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  have partition := Finset.card_sdiff_add_card_eq_card
    (internalNeighbors_subset object windowIndex position)
  rw [Nat.add_comm]
  simpa [externalNeighbors, ambientNeighbors, FiniteObject.degree] using partition

/-- One thirteen-vertex path has internal degree sum `24`. -/
theorem path13_internal_degree_sum :
    (∑ position : Fin 13, pathDegree position) = 24 := by
  decide

private theorem position_sum_eq_support_sum (object : FiniteObject V)
    (window : Window object) :
    (∑ position : Fin 13, (object.degree (window position) - 3)) =
      ∑ vertex ∈ InducedPathPacking.support object 13 window,
        (object.degree vertex - 3) := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  unfold InducedPathPacking.support
  rw [Finset.sum_image]
  intro left _ right _ equal
  exact window.injective equal

/-- The position-indexed execution ledger is exactly the surplus on the
covered set, with each covered vertex counted once. -/
theorem windowSurplus_eq_coveredSurplus (object : FiniteObject V) :
    windowSurplus object = coveredSurplus object := by
  classical
  let profile := InducedPathPacking.profile object 13 positive_thirteen
  have selectedEq : selectedWindows object = profile.maximum.1 := by
    exact selectedWindows_eq_maximum object
  have pairwise : (selectedWindows object : Set (Window object)).PairwiseDisjoint
      (InducedPathPacking.support object 13) := by
    rw [selectedEq]
    exact profile.maximum.2
  unfold windowSurplus
  simp only [selectedWindow]
  calc
    (∑ window : WindowIndex object,
        ∑ position : Fin 13, (object.degree (window.1 position) - 3)) =
      ∑ window : WindowIndex object,
        ∑ vertex ∈ InducedPathPacking.support object 13 window.1,
          (object.degree vertex - 3) := by
      apply Finset.sum_congr rfl
      intro window _
      exact position_sum_eq_support_sum object window.1
    _ = ∑ vertex ∈ (selectedWindows object).biUnion
        (InducedPathPacking.support object 13),
          (object.degree vertex - 3) :=
      Core.FiniteDisjointPacking.Profile.sum_subtype_supports
        (selectedWindows object)
        (InducedPathPacking.support object 13) pairwise
        (fun vertex => object.degree vertex - 3)
    _ = coveredSurplus object := by
      rw [selectedEq]
      rfl

/-- Exact `W ⊔ R` surplus partition. -/
theorem covered_add_remainder_eq_totalSurplus (object : FiniteObject V) :
    coveredSurplus object + remainderSurplus object = totalSurplus object := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  let covered := InducedPathPacking.coveredVertices object 13 positive_thirteen
  have partition : covered ∪
      InducedPathPacking.remainderVertices object 13 positive_thirteen =
        (Finset.univ : Finset V) := by
    ext vertex
    by_cases member : vertex ∈ covered
    · simp [member, covered]
    · simp [member, covered, InducedPathPacking.remainderVertices]
  have disjoint : Disjoint covered
      (InducedPathPacking.remainderVertices object 13 positive_thirteen) := by
    rw [Finset.disjoint_left]
    intro vertex coveredMember remainderMember
    exact (Finset.mem_sdiff.mp remainderMember).2 coveredMember
  unfold coveredSurplus remainderSurplus totalSurplus
  rw [FinEnum.sum_orderedValues object.input.vertices]
  change (∑ vertex ∈ covered, (object.degree vertex - 3)) +
      (∑ vertex ∈ InducedPathPacking.remainderVertices object 13
        positive_thirteen, (object.degree vertex - 3)) = _
  calc
    (∑ vertex ∈ covered, (object.degree vertex - 3)) +
        (∑ vertex ∈ InducedPathPacking.remainderVertices object 13
          positive_thirteen, (object.degree vertex - 3)) =
      ∑ vertex ∈ covered ∪
        InducedPathPacking.remainderVertices object 13 positive_thirteen,
          (object.degree vertex - 3) :=
      (Finset.sum_union (f := fun vertex => object.degree vertex - 3)
        disjoint).symm
    _ = ∑ vertex ∈ (Finset.univ : Finset V),
        (object.degree vertex - 3) := by rw [partition]
    _ = ∑ vertex : V, (object.degree vertex - 3) := by simp

theorem window_add_remainder_eq_totalSurplus (object : FiniteObject V) :
    windowSurplus object + remainderSurplus object = totalSurplus object := by
  rw [windowSurplus_eq_coveredSurplus,
    covered_add_remainder_eq_totalSurplus]

/-- Any vertex weight on the selected covered set is exactly the iterated
sum over selected windows and their thirteen declared positions. -/
theorem sum_covered_eq_window_positions (object : FiniteObject V)
    (weight : V → Nat) :
    (∑ vertex ∈ InducedPathPacking.coveredVertices object 13
        positive_thirteen, weight vertex) =
      ∑ windowIndex : WindowIndex object,
        ∑ position : Fin 13,
          weight (selectedWindow object windowIndex position) := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  let profile := InducedPathPacking.profile object 13 positive_thirteen
  have selectedEq : selectedWindows object = profile.maximum.1 :=
    selectedWindows_eq_maximum object
  have pairwise : (selectedWindows object : Set (Window object)).PairwiseDisjoint
      (InducedPathPacking.support object 13) := by
    rw [selectedEq]
    exact profile.maximum.2
  calc
    (∑ vertex ∈ InducedPathPacking.coveredVertices object 13
        positive_thirteen, weight vertex) =
      ∑ vertex ∈ (selectedWindows object).biUnion
          (InducedPathPacking.support object 13), weight vertex := by
        apply Finset.sum_congr
        · unfold InducedPathPacking.coveredVertices
          ext vertex
          rw [selectedEq]
          simp [profile]
        · intro vertex _member
          rfl
    _ = ∑ window : WindowIndex object,
        ∑ vertex ∈ InducedPathPacking.support object 13 window.1,
          weight vertex :=
      (Core.FiniteDisjointPacking.Profile.sum_subtype_supports
        (selectedWindows object)
        (InducedPathPacking.support object 13) pairwise weight).symm
    _ = ∑ windowIndex : WindowIndex object,
        ∑ position : Fin 13,
          weight (selectedWindow object windowIndex position) := by
      apply Finset.sum_congr rfl
      intro windowIndex _member
      unfold InducedPathPacking.support selectedWindow
      rw [Finset.sum_image]
      intro left _ right _ equal
      exact windowIndex.1.injective equal

theorem internalNeighbors_subset_covered (object : FiniteObject V)
    (windowIndex : WindowIndex object) (position : Fin 13) :
    internalNeighbors object windowIndex position ⊆
      InducedPathPacking.coveredVertices object 13 positive_thirteen := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  intro vertex member
  unfold internalNeighbors at member
  rw [Finset.mem_image] at member
  rcases member with ⟨source, _sourceMember, rfl⟩
  rw [InducedPathPacking.mem_coveredVertices_iff]
  refine ⟨selectedWindow object windowIndex, ?_, ?_⟩
  · let profile := InducedPathPacking.profile object 13 positive_thirteen
    have maxMember : windowIndex.1 ∈ profile.maximum.1 := by
      rw [← selectedWindows_eq_maximum object]
      exact windowIndex.2
    exact profile.mem_values_iff windowIndex.1 |>.2 maxMember
  unfold InducedPathPacking.support
  simp

/-- The positive-deficiency profile on the exact packed-path remainder. -/
noncomputable def remainderDeficiencyProfile (object : FiniteObject V) :
    PositiveDeficiencyWedge.Profile object where
  core := InducedPathPacking.remainderVertices object 13 positive_thirteen

/-- Every boundary incidence of the selected remainder appears among the
literal external-incidence tokens of the selected windows.  Cross-window
tokens are harmless extra capacity and are not discarded. -/
theorem remainderBoundaryIncidences_le_tokenCount (object : FiniteObject V) :
    (remainderDeficiencyProfile object).boundaryIncidences ≤
      tokenCount object := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  let remainder := InducedPathPacking.remainderVertices object 13 positive_thirteen
  let covered := InducedPathPacking.coveredVertices object 13 positive_thirteen
  have externalEq (vertex : V) :
      (remainderDeficiencyProfile object).externalDegree vertex =
        (object.graph.neighborFinset vertex ∩ covered).card := by
    unfold PositiveDeficiencyWedge.Profile.externalDegree
      remainderDeficiencyProfile
    dsimp [remainder, covered]
    apply congrArg Finset.card
    ext neighbor
    simp [InducedPathPacking.remainderVertices]
  have onePosition (windowIndex : WindowIndex object) (position : Fin 13) :
      (∑ vertex ∈ remainder,
          if object.graph.Adj vertex
              (selectedWindow object windowIndex position) then 1 else 0) ≤
        (externalNeighbors object windowIndex position).card := by
    rw [Finset.sum_boole]
    apply Finset.card_le_card
    intro vertex member
    have parts := Finset.mem_filter.mp member
    have ambient : vertex ∈ ambientNeighbors object windowIndex position := by
      unfold ambientNeighbors
      simpa [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm] using parts.2
    have notInternal : vertex ∉ internalNeighbors object windowIndex position := by
      intro internal
      have coveredMember := internalNeighbors_subset_covered object windowIndex
        position internal
      exact (Finset.mem_sdiff.mp parts.1).2 coveredMember
    exact Finset.mem_sdiff.mpr ⟨ambient, notInternal⟩
  calc
    (remainderDeficiencyProfile object).boundaryIncidences =
        ∑ vertex ∈ remainder,
          (object.graph.neighborFinset vertex ∩ covered).card := by
      unfold PositiveDeficiencyWedge.Profile.boundaryIncidences
      apply Finset.sum_congr rfl
      intro vertex _member
      exact externalEq vertex
    _ = ∑ vertex ∈ remainder,
        ∑ windowVertex ∈ covered,
          if object.graph.Adj vertex windowVertex then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro vertex _member
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext windowVertex
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    _ = ∑ windowVertex ∈ covered,
        ∑ vertex ∈ remainder,
          if object.graph.Adj vertex windowVertex then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ windowIndex : WindowIndex object,
        ∑ position : Fin 13,
          ∑ vertex ∈ remainder,
            if object.graph.Adj vertex
              (selectedWindow object windowIndex position) then 1 else 0 := by
      exact sum_covered_eq_window_positions object (fun windowVertex =>
        ∑ vertex ∈ remainder,
          if object.graph.Adj vertex windowVertex then 1 else 0)
    _ ≤ ∑ windowIndex : WindowIndex object,
        ∑ position : Fin 13,
          (externalNeighbors object windowIndex position).card := by
      exact Finset.sum_le_sum fun windowIndex _member =>
        Finset.sum_le_sum fun position _member => onePosition windowIndex position
    _ = tokenCount object := rfl

theorem remainderPositiveDeficiency_le_tokenCount
    (object : FiniteObject V)
    (baseline : ∀ vertex, 3 ≤ object.degree vertex) :
    (remainderDeficiencyProfile object).positiveDeficiency ≤
      tokenCount object :=
  ((remainderDeficiencyProfile object).positiveDeficiency_le_boundaryIncidences
      baseline).trans (remainderBoundaryIncidences_le_tokenCount object)

theorem one_window_degree_sum (object : FiniteObject V)
    (windowIndex : WindowIndex object) :
    (∑ position : Fin 13,
        object.degree (selectedWindow object windowIndex position)) =
      24 + ∑ position : Fin 13,
        (externalNeighbors object windowIndex position).card := by
  calc
    (∑ position : Fin 13,
        object.degree (selectedWindow object windowIndex position)) =
        ∑ position : Fin 13,
          ((internalNeighbors object windowIndex position).card +
            (externalNeighbors object windowIndex position).card) := by
              apply Finset.sum_congr rfl
              intro position _
              exact (internal_add_external_eq_degree object windowIndex position).symm
    _ = (∑ position : Fin 13,
          (internalNeighbors object windowIndex position).card) +
        ∑ position : Fin 13,
          (externalNeighbors object windowIndex position).card := by
            rw [Finset.sum_add_distrib]
    _ = 24 + ∑ position : Fin 13,
          (externalNeighbors object windowIndex position).card := by
            rw [show (∑ position : Fin 13,
              (internalNeighbors object windowIndex position).card) = 24 by
                simpa [internalNeighbors_card] using path13_internal_degree_sum]

theorem one_window_surplus_degree_sum (object : FiniteObject V)
    (baseline : ∀ vertex, 3 ≤ object.degree vertex)
    (windowIndex : WindowIndex object) :
    (∑ position : Fin 13,
        object.degree (selectedWindow object windowIndex position)) =
      39 + ∑ position : Fin 13,
        (object.degree (selectedWindow object windowIndex position) - 3) := by
  have pointwise : ∀ position : Fin 13,
      object.degree (selectedWindow object windowIndex position) =
        3 + (object.degree (selectedWindow object windowIndex position) - 3) := by
    intro position
    have := baseline (selectedWindow object windowIndex position)
    omega
  calc
    (∑ position : Fin 13,
        object.degree (selectedWindow object windowIndex position)) =
        ∑ position : Fin 13,
          (3 + (object.degree
            (selectedWindow object windowIndex position) - 3)) := by
              apply Finset.sum_congr rfl
              intro position _
              exact pointwise position
    _ = 39 + ∑ position : Fin 13,
          (object.degree (selectedWindow object windowIndex position) - 3) := by
            simp [Finset.sum_add_distrib]

/-- Exact manuscript identity at node `[135]`.  The left side is the actual
finite external-incidence universe, hence one token per `R--W` edge and two
endpoint tokens per cross-window edge. -/
theorem tokenCount_eq_fifteen_mul_packing_add_surplus
    (object : FiniteObject V)
    (baseline : ∀ vertex, 3 ≤ object.degree vertex) :
    tokenCount object = 15 * packingNumber object + windowSurplus object := by
  have perWindow : ∀ windowIndex : WindowIndex object,
      24 + ∑ position : Fin 13,
          (externalNeighbors object windowIndex position).card =
        39 + ∑ position : Fin 13,
          (object.degree (selectedWindow object windowIndex position) - 3) := by
    intro windowIndex
    rw [← one_window_degree_sum object windowIndex,
      one_window_surplus_degree_sum object baseline windowIndex]
  have summed := Finset.sum_congr
    (s₁ := (Finset.univ : Finset (WindowIndex object)))
    (s₂ := (Finset.univ : Finset (WindowIndex object))) rfl
    (fun windowIndex _ => perWindow windowIndex)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at summed
  have indexCard : Fintype.card (WindowIndex object) = packingNumber object := by
    simpa [FinEnum.card_eq_fintypeCard] using
      windowIndex_card_eq_packingNumber object
  rw [indexCard] at summed
  have summed' :
      24 * packingNumber object + tokenCount object =
        39 * packingNumber object + windowSurplus object := by
    simpa [tokenCount, windowSurplus, Nat.mul_comm] using summed
  omega

theorem remainderPositiveDeficiency_le_fifteen_mul_packing_add_surplus
    (object : FiniteObject V)
    (baseline : ∀ vertex, 3 ≤ object.degree vertex) :
    (remainderDeficiencyProfile object).positiveDeficiency ≤
      15 * packingNumber object + windowSurplus object := by
  rw [← tokenCount_eq_fifteen_mul_packing_add_surplus object baseline]
  exact remainderPositiveDeficiency_le_tokenCount object baseline

/-- The exact surplus-adjusted form of the window-stub inequality.  This is
the finite natural-number statement used before any near-cubic normalization:
the same remainder surplus is removed from both sides of the literal
incidence bound. -/
theorem remainderPositiveDeficiency_sub_remainderSurplus_le
    (object : FiniteObject V)
    (baseline : ∀ vertex, 3 ≤ object.degree vertex) :
    (remainderDeficiencyProfile object).positiveDeficiency -
        remainderSurplus object ≤
      15 * packingNumber object + windowSurplus object -
        remainderSurplus object := by
  exact Nat.sub_le_sub_right
    (remainderPositiveDeficiency_le_fifteen_mul_packing_add_surplus
      object baseline) (remainderSurplus object)

theorem tokens_card_eq_tokenCount (object : FiniteObject V) :
    (tokens object).card = tokenCount object := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : FinEnum (WindowIndex object) := windowIndices object
  rw [FinEnum.card_eq_fintypeCard]
  simp only [Token, tokenCount, Fintype.card_sigma, Fintype.card_coe]

theorem tokens_card_eq_fifteen_mul_packing_add_surplus
    (object : FiniteObject V)
    (baseline : ∀ vertex, 3 ≤ object.degree vertex) :
    (tokens object).card = 15 * packingNumber object + windowSurplus object := by
  rw [tokens_card_eq_tokenCount,
    tokenCount_eq_fifteen_mul_packing_add_surplus object baseline]

/-- The exact local work count: selected windows times thirteen positions
times the declared ambient vertex schedule. -/
noncomputable def checks (object : FiniteObject V) : Nat :=
  packingNumber object * (13 * object.input.vertices.card)

theorem checks_le_thirteen_mul_square (object : FiniteObject V) :
    checks object ≤ 13 * object.input.vertices.card ^ 2 := by
  have packed := InducedPathPacking.packing_vertices_bound object 13
    positive_thirteen
  unfold checks
  rw [packingNumber_eq_inducedPathPacking]
  nlinarith

end StructuralExhaustion.Graph.InducedPathWindowLedger
