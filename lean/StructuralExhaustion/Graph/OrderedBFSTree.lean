import StructuralExhaustion.Core.FiniteSearch
import StructuralExhaustion.Graph.FiniteObject

namespace StructuralExhaustion.Graph.OrderedBFSTree

open StructuralExhaustion

universe u

variable {V : Type u}

/-!
# Ordered finite BFS layers

This module is the executable base of a shared rooted BFS tree.  Every scan
uses the vertex order and adjacency decision bundled in `FiniteObject`.
It provides verified layers, total first parents, and depth-recursive shared
root paths.  Prefix coherence is derived from the same parent map; separator
consequences remain downstream consumers.
-/

structure Profile (object : FiniteObject V) where
  root : V

structure State (object : FiniteObject V) where
  discovered : Finset V
  frontier : Finset V

namespace Profile

variable {object : FiniteObject V} (profile : Profile object)

private def initial : State object where
  discovered := {profile.root}
  frontier := {profile.root}

/-- One literal BFS layer scan.  New vertices are exactly the not-yet-seen
vertices adjacent to the current frontier. -/
def advance (_profile : Profile object) (current : State object) : State object := by
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  let next := object.vertexFinset.filter fun vertex =>
    vertex ∉ current.discovered ∧
      ∃ parent ∈ current.frontier, object.graph.Adj parent vertex
  exact {
    discovered := current.discovered ∪ next
    frontier := next
  }

/-- State after exactly `steps` ordered layer scans. -/
def state (profile : Profile object) : Nat → State object
  | 0 => profile.initial
  | steps + 1 => profile.advance (profile.state steps)

def discovered (steps : Nat) : Finset V :=
  (profile.state steps).discovered

def layer (steps : Nat) : Finset V :=
  (profile.state steps).frontier

@[simp] theorem discovered_zero : profile.discovered 0 = {profile.root} := rfl

@[simp] theorem layer_zero : profile.layer 0 = {profile.root} := rfl

@[simp] theorem root_mem_discovered_zero :
    profile.root ∈ profile.discovered 0 := by simp

theorem layer_subset_discovered (steps : Nat) :
    profile.layer steps ⊆ profile.discovered steps := by
  letI : DecidableEq V := object.input.vertices.decEq
  induction steps with
  | zero => simp [layer, discovered, state, initial]
  | succ steps _ih =>
      intro vertex member
      simp only [discovered, state]
      exact Finset.mem_union_right _ member

theorem discovered_mono_step (steps : Nat) :
    profile.discovered steps ⊆ profile.discovered (steps + 1) := by
  letI : DecidableEq V := object.input.vertices.decEq
  intro vertex member
  simp only [discovered, state, advance]
  exact Finset.mem_union_left _ member

theorem discovered_mono {first last : Nat} (order : first ≤ last) :
    profile.discovered first ⊆ profile.discovered last := by
  induction order with
  | refl => exact Finset.Subset.rfl
  | @step last order ih =>
      exact ih.trans (profile.discovered_mono_step last)

theorem root_mem_discovered (steps : Nat) :
    profile.root ∈ profile.discovered steps := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      exact profile.discovered_mono_step steps ih

theorem layer_subset_vertices (steps : Nat) :
    profile.layer steps ⊆ object.vertexFinset := by
  intro vertex _member
  exact object.mem_vertexFinset vertex

theorem discovered_subset_vertices (steps : Nat) :
    profile.discovered steps ⊆ object.vertexFinset := by
  intro vertex _member
  exact object.mem_vertexFinset vertex

theorem card_layer_le_order (steps : Nat) :
    (profile.layer steps).card ≤ object.input.vertices.card := by
  rw [← object.card_vertexFinset]
  exact Finset.card_le_card (profile.layer_subset_vertices steps)

theorem card_discovered_le_order (steps : Nat) :
    (profile.discovered steps).card ≤ object.input.vertices.card := by
  rw [← object.card_vertexFinset]
  exact Finset.card_le_card (profile.discovered_subset_vertices steps)

/-- Exact characterization of membership in a positive BFS layer. -/
theorem mem_layer_succ_iff (steps : Nat) (vertex : V) :
    vertex ∈ profile.layer (steps + 1) ↔
      vertex ∉ profile.discovered steps ∧
        ∃ parent ∈ profile.layer steps, object.graph.Adj parent vertex := by
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  change vertex ∈ (profile.advance (profile.state steps)).frontier ↔
    vertex ∉ (profile.state steps).discovered ∧
      ∃ parent ∈ (profile.state steps).frontier,
        object.graph.Adj parent vertex
  simp [advance]

theorem mem_discovered_succ_iff (steps : Nat) (vertex : V) :
    vertex ∈ profile.discovered (steps + 1) ↔
      vertex ∈ profile.discovered steps ∨ vertex ∈ profile.layer (steps + 1) := by
  letI : DecidableEq V := object.input.vertices.decEq
  simp [discovered, layer, state, advance]

/-- Any neighbour of an already discovered vertex is discovered after one
additional layer scan. -/
theorem adjacent_discovered_succ (steps : Nat) {vertex next : V}
    (member : vertex ∈ profile.discovered steps)
    (adjacent : object.graph.Adj vertex next) :
    next ∈ profile.discovered (steps + 1) := by
  induction steps generalizing vertex next with
  | zero =>
      have vertexEq : vertex = profile.root := by simpa using member
      subst vertex
      by_cases seen : next ∈ profile.discovered 0
      · exact profile.discovered_mono_step 0 seen
      · apply (profile.mem_discovered_succ_iff 0 next).mpr
        right
        apply (profile.mem_layer_succ_iff 0 next).mpr
        exact ⟨seen, profile.root, by simp, adjacent⟩
  | succ steps ih =>
      rcases (profile.mem_discovered_succ_iff steps vertex).mp member with
        old | current
      · exact profile.discovered_mono_step (steps + 1) (ih old adjacent)
      · by_cases seen : next ∈ profile.discovered (steps + 1)
        · exact profile.discovered_mono_step (steps + 1) seen
        · apply (profile.mem_discovered_succ_iff (steps + 1) next).mpr
          right
          apply (profile.mem_layer_succ_iff (steps + 1) next).mpr
          exact ⟨seen, vertex, current, adjacent⟩

/-- Following any ambient walk from a discovered start preserves discovery,
with one additional scan per edge. -/
theorem walk_finish_mem_discovered
    {start finish : V} (steps : Nat)
    (startMem : start ∈ profile.discovered steps)
    (walk : object.graph.Walk start finish) :
    finish ∈ profile.discovered (steps + walk.length) := by
  induction walk generalizing steps with
  | nil => simpa using startMem
  | @cons start middle finish adjacent tail ih =>
      have middleMem := profile.adjacent_discovered_succ steps startMem adjacent
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (steps := steps + 1) middleMem

/-- A discovered vertex has an ambient root walk whose length is bounded by
the number of completed layer scans. -/
theorem discovered_iff_bounded_walk (steps : Nat) (vertex : V) :
    vertex ∈ profile.discovered steps ↔
      ∃ walk : object.graph.Walk profile.root vertex, walk.length ≤ steps := by
  constructor
  · intro member
    induction steps generalizing vertex with
    | zero =>
        have vertexEq : vertex = profile.root := by simpa using member
        subst vertex
        exact ⟨.nil, by simp⟩
    | succ steps ih =>
        rcases (profile.mem_discovered_succ_iff steps vertex).mp member with
          old | fresh
        · obtain ⟨walk, bound⟩ := ih vertex old
          exact ⟨walk, bound.trans (Nat.le_succ steps)⟩
        · obtain ⟨_unseen, parent, parentLayer, adjacent⟩ :=
            (profile.mem_layer_succ_iff steps vertex).mp fresh
          obtain ⟨walk, bound⟩ := ih parent
            (profile.layer_subset_discovered steps parentLayer)
          refine ⟨walk.concat adjacent, ?_⟩
          simpa [SimpleGraph.Walk.length_concat] using Nat.add_le_add_right bound 1
  · rintro ⟨walk, bound⟩
    have reached := profile.walk_finish_mem_discovered 0
      (profile.root_mem_discovered 0) walk
    exact Finset.mem_of_subset
      (by
        induction bound with
        | refl => exact Finset.Subset.rfl
        | @step upper _ ih =>
            exact ih.trans (profile.discovered_mono_step upper))
      (by simpa using reached)

/-- Preconnectedness supplies a simple root path of length below the declared
vertex count, so the finite BFS has discovered every vertex by that count. -/
theorem all_discovered_by_order
    (preconnected : object.graph.Preconnected) (vertex : V) :
    vertex ∈ profile.discovered object.input.vertices.card := by
  letI : FinEnum V := object.input.vertices
  exact (preconnected profile.root vertex).elim_path fun path =>
    (profile.discovered_iff_bounded_walk object.input.vertices.card vertex).mpr
      ⟨path, by
        simpa [FinEnum.card_eq_fintypeCard] using path.property.length_lt.le⟩

abbrev DepthPredicate (vertex : V) (level : Nat) : Prop :=
  vertex ∈ profile.discovered level

/-- Executable first-discovery scan over the bounded level schedule
`0, ..., |V|`. -/
def depthSearch (vertex : V) :=
  Core.FiniteSearch.firstOnList
    (List.range (object.input.vertices.card + 1))
    (profile.DepthPredicate vertex)
    (fun level => by
      letI : DecidableEq V := object.input.vertices.decEq
      exact inferInstance)

def depth? (vertex : V) : Option Nat :=
  (profile.depthSearch vertex).value?

theorem depth?_exists (preconnected : object.graph.Preconnected)
    (vertex : V) : ∃ depth, profile.depth? vertex = some depth := by
  cases result : profile.depthSearch vertex with
  | found hit =>
      exact ⟨hit.value, by
        simp [depth?, result, Core.FiniteSearch.FirstResult.value?]⟩
  | absent absentProof =>
      have member := profile.all_discovered_by_order preconnected vertex
      exact (absentProof object.input.vertices.card
        (by simp) member).elim

theorem depth?_isSome (preconnected : object.graph.Preconnected)
    (vertex : V) : (profile.depth? vertex).isSome := by
  obtain ⟨depth, selected⟩ := profile.depth?_exists preconnected vertex
  simp [selected]

/-- Total executable depth on a preconnected finite graph. -/
def depth (preconnected : object.graph.Preconnected) (vertex : V) : Nat :=
  (profile.depth? vertex).get (profile.depth?_isSome preconnected vertex)

theorem depth?_eq_some_depth (preconnected : object.graph.Preconnected)
    (vertex : V) :
    profile.depth? vertex = some (profile.depth preconnected vertex) := by
  exact (Option.coe_get (profile.depth?_isSome preconnected vertex)).symm

theorem depth_mem_discovered (preconnected : object.graph.Preconnected)
    (vertex : V) :
    vertex ∈ profile.discovered (profile.depth preconnected vertex) := by
  have selected := profile.depth?_eq_some_depth preconnected vertex
  cases result : profile.depthSearch vertex with
  | found hit =>
      simp [depth?, result, Core.FiniteSearch.FirstResult.value?] at selected
      rw [← selected]
      exact hit.holds
  | absent absentProof =>
      simp [depth?, result, Core.FiniteSearch.FirstResult.value?] at selected

theorem depth_le_order (preconnected : object.graph.Preconnected)
    (vertex : V) :
    profile.depth preconnected vertex ≤ object.input.vertices.card := by
  have selected := profile.depth?_eq_some_depth preconnected vertex
  cases result : profile.depthSearch vertex with
  | found hit =>
      have valueEq : hit.value = profile.depth preconnected vertex := by
        simpa [depth?, result, Core.FiniteSearch.FirstResult.value?] using selected
      rw [← valueEq]
      have member := hit.member
      simp only [List.mem_range] at member
      omega
  | absent absentProof =>
      simp [depth?, result, Core.FiniteSearch.FirstResult.value?] at selected

theorem depthSearch_is_found (preconnected : object.graph.Preconnected)
    (vertex : V) :
    ∃ hit : Core.FiniteSearch.FirstHit
        (List.range (object.input.vertices.card + 1))
        (profile.DepthPredicate vertex),
      profile.depthSearch vertex = .found hit ∧
        hit.value = profile.depth preconnected vertex := by
  have selected := profile.depth?_eq_some_depth preconnected vertex
  cases result : profile.depthSearch vertex with
  | found hit =>
      refine ⟨hit, rfl, ?_⟩
      simpa [depth?, result, Core.FiniteSearch.FirstResult.value?] using selected
  | absent absentProof =>
      simp [depth?, result, Core.FiniteSearch.FirstResult.value?] at selected

private theorem depthHit_before_length (vertex : V)
    (hit : Core.FiniteSearch.FirstHit
      (List.range (object.input.vertices.card + 1))
      (profile.DepthPredicate vertex)) :
    hit.before.length = hit.value := by
  have lengths := congrArg List.length hit.split
  have bound : hit.before.length < object.input.vertices.card + 1 := by
    simp only [List.length_range, List.length_append, List.length_cons] at lengths
    omega
  have entries := congrArg (fun values : List Nat => values[hit.before.length]?) hit.split
  simpa [bound] using entries

theorem depthHit_before_eq_range (vertex : V)
    (hit : Core.FiniteSearch.FirstHit
      (List.range (object.input.vertices.card + 1))
      (profile.DepthPredicate vertex)) :
    hit.before = List.range hit.value := by
  have prefixEq := congrArg (List.take hit.before.length) hit.split
  have bound : hit.before.length ≤ object.input.vertices.card + 1 := by
    have member := hit.member
    simp only [List.mem_range] at member
    rw [profile.depthHit_before_length vertex hit]
    omega
  have valueBound : hit.value ≤ object.input.vertices.card + 1 := by
    simpa [profile.depthHit_before_length vertex hit] using bound
  symm
  simpa [List.take_range, profile.depthHit_before_length vertex hit,
    Nat.min_eq_left valueBound] using prefixEq

theorem depth_minimal (preconnected : object.graph.Preconnected)
    (vertex : V) {level : Nat}
    (less : level < profile.depth preconnected vertex) :
    vertex ∉ profile.discovered level := by
  obtain ⟨hit, _run, valueEq⟩ :=
    profile.depthSearch_is_found preconnected vertex
  apply hit.beforeAbsent level
  rw [profile.depthHit_before_eq_range vertex hit]
  simp [valueEq, less]

theorem depth_root (preconnected : object.graph.Preconnected) :
    profile.depth preconnected profile.root = 0 := by
  by_contra nonzero
  have positive : 0 < profile.depth preconnected profile.root := Nat.pos_of_ne_zero nonzero
  exact profile.depth_minimal preconnected profile.root positive
    profile.root_mem_discovered_zero

theorem depth_positive_of_ne_root (preconnected : object.graph.Preconnected)
    {vertex : V} (nonroot : vertex ≠ profile.root) :
    0 < profile.depth preconnected vertex := by
  apply Nat.pos_of_ne_zero
  intro zero
  have member := profile.depth_mem_discovered preconnected vertex
  rw [zero] at member
  have : vertex = profile.root := by simpa using member
  exact nonroot this

theorem depth_le_of_mem_discovered (preconnected : object.graph.Preconnected)
    {vertex : V} {steps : Nat}
    (member : vertex ∈ profile.discovered steps) :
    profile.depth preconnected vertex ≤ steps := by
  by_contra notLe
  exact profile.depth_minimal preconnected vertex (Nat.lt_of_not_ge notLe) member

theorem depth_eq_of_mem_layer (preconnected : object.graph.Preconnected)
    {vertex : V} {steps : Nat} (member : vertex ∈ profile.layer steps) :
    profile.depth preconnected vertex = steps := by
  have upper := profile.depth_le_of_mem_discovered preconnected
    (profile.layer_subset_discovered steps member)
  apply Nat.le_antisymm upper
  by_contra notLe
  have strict : profile.depth preconnected vertex < steps := Nat.lt_of_not_ge notLe
  cases steps with
  | zero => omega
  | succ previous =>
      have previousMem : vertex ∈ profile.discovered previous :=
        profile.discovered_mono (Nat.le_of_lt_succ strict)
          (profile.depth_mem_discovered preconnected vertex)
      exact ((profile.mem_layer_succ_iff previous vertex).mp member).1 previousMem

abbrev ParentPredicate (steps : Nat) (vertex parent : V) : Prop :=
  parent ∈ profile.layer steps ∧ object.graph.Adj parent vertex

/-- Executable first-parent scan in the graph's declared vertex order. -/
def parentSearch (steps : Nat) (vertex : V) :=
  Core.FiniteSearch.first object.input.vertices
    (profile.ParentPredicate steps vertex)
    (fun parent => by
      letI : DecidableEq V := object.input.vertices.decEq
      letI : DecidableRel object.graph.Adj := object.input.decideAdj
      exact inferInstance)

theorem parent_exists_of_mem_layer_succ (steps : Nat) {vertex : V}
    (member : vertex ∈ profile.layer (steps + 1)) :
    ∃ parent : V, profile.ParentPredicate steps vertex parent :=
  (profile.mem_layer_succ_iff steps vertex).mp member |>.2

/-- Executable optional parent.  Positive-layer membership proves this option
is populated; keeping the executable option avoids extracting data from a
propositional existential. -/
def parent? (steps : Nat) (vertex : V) : Option V :=
  (profile.parentSearch steps vertex).value?

theorem parent?_exists_of_mem_layer_succ (steps : Nat) {vertex : V}
    (member : vertex ∈ profile.layer (steps + 1)) :
    ∃ parent : V, profile.parent? steps vertex = some parent := by
  have witness := profile.parent_exists_of_mem_layer_succ steps member
  cases result : profile.parentSearch steps vertex with
  | found hit =>
      exact ⟨hit.value, by simp [parent?, result,
        Core.FiniteSearch.FirstResult.value?]⟩
  | absent absentProof =>
      rcases witness with ⟨parent, parentHolds⟩
      exact (absentProof parent (object.input.vertices.mem_orderedValues parent)
        parentHolds).elim

theorem parent?_sound (steps : Nat) (vertex parent : V)
    (selected : profile.parent? steps vertex = some parent) :
    parent ∈ profile.layer steps ∧ object.graph.Adj parent vertex := by
  unfold parent? at selected
  cases result : profile.parentSearch steps vertex with
  | found hit =>
      simp [Core.FiniteSearch.FirstResult.value?, result] at selected
      subst parent
      exact hit.holds
  | absent absentProof =>
      simp [Core.FiniteSearch.FirstResult.value?, result] at selected

/-- The selected parent is the first valid parent in declared vertex order. -/
theorem parent?_is_first (steps : Nat) (vertex parent : V)
    (selected : profile.parent? steps vertex = some parent) :
    ∃ before after : List V,
      object.input.vertices.orderedValues = before ++ parent :: after ∧
      ∀ candidate ∈ before,
        ¬profile.ParentPredicate steps vertex candidate := by
  unfold parent? at selected
  cases result : profile.parentSearch steps vertex with
  | found hit =>
      simp [Core.FiniteSearch.FirstResult.value?, result] at selected
      subst parent
      exact ⟨hit.before, hit.after, hit.split, hit.beforeAbsent⟩
  | absent absentProof =>
      simp [Core.FiniteSearch.FirstResult.value?, result] at selected

def parentLevel (preconnected : object.graph.Preconnected) (vertex : V) : Nat :=
  profile.depth preconnected vertex - 1

theorem parentLevel_succ_eq_depth (preconnected : object.graph.Preconnected)
    {vertex : V} (nonroot : vertex ≠ profile.root) :
    profile.parentLevel preconnected vertex + 1 =
      profile.depth preconnected vertex := by
  unfold parentLevel
  exact Nat.sub_add_cancel (profile.depth_positive_of_ne_root preconnected nonroot)

theorem nonroot_mem_parent_layer_succ
    (preconnected : object.graph.Preconnected)
    {vertex : V} (nonroot : vertex ≠ profile.root) :
    vertex ∈ profile.layer (profile.parentLevel preconnected vertex + 1) := by
  have depthMem := profile.depth_mem_discovered preconnected vertex
  have levelLt : profile.parentLevel preconnected vertex <
      profile.depth preconnected vertex := by
    rw [← profile.parentLevel_succ_eq_depth preconnected nonroot]
    omega
  have unseen := profile.depth_minimal preconnected vertex levelLt
  rw [← profile.parentLevel_succ_eq_depth preconnected nonroot] at depthMem
  rcases (profile.mem_discovered_succ_iff
      (profile.parentLevel preconnected vertex) vertex).mp depthMem with
    old | current
  · exact (unseen old).elim
  · exact current

theorem parentAtDepth_isSome (preconnected : object.graph.Preconnected)
    {vertex : V} (nonroot : vertex ≠ profile.root) :
    (profile.parent? (profile.parentLevel preconnected vertex) vertex).isSome := by
  obtain ⟨parent, selected⟩ := profile.parent?_exists_of_mem_layer_succ
    (profile.parentLevel preconnected vertex)
    (profile.nonroot_mem_parent_layer_succ preconnected nonroot)
  simp [selected]

/-- Total declared-order parent of a nonroot vertex. -/
def treeParent (preconnected : object.graph.Preconnected)
    (vertex : V) (nonroot : vertex ≠ profile.root) : V :=
  (profile.parent? (profile.parentLevel preconnected vertex) vertex).get
    (profile.parentAtDepth_isSome preconnected nonroot)

theorem parent?_eq_some_treeParent (preconnected : object.graph.Preconnected)
    (vertex : V) (nonroot : vertex ≠ profile.root) :
    profile.parent? (profile.parentLevel preconnected vertex) vertex =
      some (profile.treeParent preconnected vertex nonroot) := by
  exact (Option.coe_get (profile.parentAtDepth_isSome preconnected nonroot)).symm

theorem treeParent_adjacent (preconnected : object.graph.Preconnected)
    (vertex : V) (nonroot : vertex ≠ profile.root) :
    object.graph.Adj (profile.treeParent preconnected vertex nonroot) vertex :=
  (profile.parent?_sound _ _ _
    (profile.parent?_eq_some_treeParent preconnected vertex nonroot)).2

theorem treeParent_depth_drop (preconnected : object.graph.Preconnected)
    (vertex : V) (nonroot : vertex ≠ profile.root) :
    profile.depth preconnected (profile.treeParent preconnected vertex nonroot) + 1 =
      profile.depth preconnected vertex := by
  have parentLayer := (profile.parent?_sound _ _ _
    (profile.parent?_eq_some_treeParent preconnected vertex nonroot)).1
  rw [profile.depth_eq_of_mem_layer preconnected parentLayer,
    profile.parentLevel_succ_eq_depth preconnected nonroot]

theorem treeParent_is_first (preconnected : object.graph.Preconnected)
    (vertex : V) (nonroot : vertex ≠ profile.root) :
    ∃ before after : List V,
      object.input.vertices.orderedValues =
          before ++ profile.treeParent preconnected vertex nonroot :: after ∧
        ∀ candidate ∈ before,
          ¬profile.ParentPredicate (profile.parentLevel preconnected vertex)
            vertex candidate :=
  profile.parent?_is_first _ _ _
    (profile.parent?_eq_some_treeParent preconnected vertex nonroot)

theorem eq_root_of_depth_eq_zero (preconnected : object.graph.Preconnected)
    {vertex : V} (zero : profile.depth preconnected vertex = 0) :
    vertex = profile.root := by
  by_contra nonroot
  have positive := profile.depth_positive_of_ne_root preconnected nonroot
  omega

def nonrootOfDepthSucc (preconnected : object.graph.Preconnected)
    (steps : Nat) (vertex : V)
    (depthEq : profile.depth preconnected vertex = steps + 1) :
    vertex ≠ profile.root := by
  intro equal
  subst vertex
  rw [profile.depth_root preconnected] at depthEq
  omega

theorem parentOfDepthSucc_depth (preconnected : object.graph.Preconnected)
    (steps : Nat) (vertex : V)
    (depthEq : profile.depth preconnected vertex = steps + 1) :
    profile.depth preconnected
        (profile.treeParent preconnected vertex
          (profile.nonrootOfDepthSucc preconnected steps vertex depthEq)) = steps := by
  have drop := profile.treeParent_depth_drop preconnected vertex
    (profile.nonrootOfDepthSucc preconnected steps vertex depthEq)
  rw [depthEq] at drop
  omega

/-- Depth-recursive shared BFS walk.  Each positive-depth step follows the
single total declared-order parent, so all later paths use one common parent
map rather than independent shortest-path choices. -/
def treeWalkAux (preconnected : object.graph.Preconnected) :
    (steps : Nat) → (vertex : V) →
      profile.depth preconnected vertex = steps →
      object.graph.Walk profile.root vertex
  | 0, _vertex, depthEq =>
      .copy .nil rfl (profile.eq_root_of_depth_eq_zero preconnected depthEq).symm
  | steps + 1, vertex, depthEq =>
      (treeWalkAux preconnected steps
        (profile.treeParent preconnected vertex
          (profile.nonrootOfDepthSucc preconnected steps vertex depthEq))
        (profile.parentOfDepthSucc_depth preconnected steps vertex depthEq)).concat
          (profile.treeParent_adjacent preconnected vertex
            (profile.nonrootOfDepthSucc preconnected steps vertex depthEq))

def treeWalk (preconnected : object.graph.Preconnected) (vertex : V) :
    object.graph.Walk profile.root vertex :=
  profile.treeWalkAux preconnected (profile.depth preconnected vertex) vertex rfl

theorem treeWalkAux_proof_irrel (preconnected : object.graph.Preconnected)
    (steps : Nat) (vertex : V)
    (left right : profile.depth preconnected vertex = steps) :
    profile.treeWalkAux preconnected steps vertex left =
      profile.treeWalkAux preconnected steps vertex right := by
  have proofsEqual : left = right := Subsingleton.elim _ _
  subst right
  rfl

theorem treeWalk_eq_treeWalkAux (preconnected : object.graph.Preconnected)
    (steps : Nat) (vertex : V)
    (depthEq : profile.depth preconnected vertex = steps) :
    profile.treeWalk preconnected vertex =
      profile.treeWalkAux preconnected steps vertex depthEq := by
  subst steps
  exact profile.treeWalkAux_proof_irrel preconnected _ vertex _ _

theorem treeWalkAux_succ_eq (preconnected : object.graph.Preconnected)
    (steps : Nat) (vertex : V)
    (depthEq : profile.depth preconnected vertex = steps + 1) :
    profile.treeWalkAux preconnected (steps + 1) vertex depthEq =
      (profile.treeWalkAux preconnected steps
        (profile.treeParent preconnected vertex
          (profile.nonrootOfDepthSucc preconnected steps vertex depthEq))
        (profile.parentOfDepthSucc_depth preconnected steps vertex depthEq)).concat
          (profile.treeParent_adjacent preconnected vertex
            (profile.nonrootOfDepthSucc preconnected steps vertex depthEq)) :=
  rfl

theorem treeWalkAux_length (preconnected : object.graph.Preconnected)
    (steps : Nat) (vertex : V)
    (depthEq : profile.depth preconnected vertex = steps) :
    (profile.treeWalkAux preconnected steps vertex depthEq).length = steps := by
  induction steps generalizing vertex with
  | zero =>
      simp [treeWalkAux]
  | succ steps ih =>
      rw [treeWalkAux, SimpleGraph.Walk.length_concat]
      simp only [Nat.add_right_cancel_iff]
      apply ih

theorem treeWalk_length (preconnected : object.graph.Preconnected)
    (vertex : V) :
    (profile.treeWalk preconnected vertex).length =
      profile.depth preconnected vertex :=
  profile.treeWalkAux_length preconnected _ vertex rfl

theorem treeWalkAux_support_depth_le
    (preconnected : object.graph.Preconnected)
    (steps : Nat) (vertex : V)
    (depthEq : profile.depth preconnected vertex = steps) :
    ∀ point ∈ (profile.treeWalkAux preconnected steps vertex depthEq).support,
      profile.depth preconnected point ≤ steps := by
  induction steps generalizing vertex with
  | zero =>
      intro point member
      simp [treeWalkAux] at member
      subst point
      simp [profile.depth_root preconnected]
  | succ steps ih =>
      intro point member
      rw [treeWalkAux, SimpleGraph.Walk.support_concat] at member
      rcases List.mem_append.mp member with earlier | endpoint
      · exact (ih _ _ point earlier).trans (Nat.le_succ steps)
      · simp only [List.mem_singleton] at endpoint
        subst point
        exact depthEq.le

theorem treeWalkAux_isPath
    (preconnected : object.graph.Preconnected)
    (steps : Nat) (vertex : V)
    (depthEq : profile.depth preconnected vertex = steps) :
    (profile.treeWalkAux preconnected steps vertex depthEq).IsPath := by
  induction steps generalizing vertex with
  | zero =>
      simp [treeWalkAux]
  | succ steps ih =>
      rw [treeWalkAux]
      apply SimpleGraph.Walk.IsPath.concat (ih _ _)
      intro member
      have bound := profile.treeWalkAux_support_depth_le preconnected steps _ _
        vertex member
      omega

theorem treeWalk_isPath (preconnected : object.graph.Preconnected)
    (vertex : V) :
    (profile.treeWalk preconnected vertex).IsPath :=
  profile.treeWalkAux_isPath preconnected _ vertex rfl

/-- BFS depth is no larger than the length of any competing root walk. -/
theorem depth_le_walk_length (preconnected : object.graph.Preconnected)
    (vertex : V) (walk : object.graph.Walk profile.root vertex) :
    profile.depth preconnected vertex ≤ walk.length :=
  profile.depth_le_of_mem_discovered preconnected
    ((profile.discovered_iff_bounded_walk walk.length vertex).mpr ⟨walk, le_rfl⟩)

theorem treeWalk_shortest (preconnected : object.graph.Preconnected)
    (vertex : V) :
    (profile.treeWalk preconnected vertex).length =
      object.graph.dist profile.root vertex := by
  apply Nat.le_antisymm
  · rw [profile.treeWalk_length]
    obtain ⟨path, isPath, shortest⟩ :=
      (preconnected profile.root vertex).exists_path_of_dist
    rw [← shortest]
    exact profile.depth_le_walk_length preconnected vertex path
  · exact SimpleGraph.dist_le (profile.treeWalk preconnected vertex)

theorem treeWalk_getVert_depth (preconnected : object.graph.Preconnected)
    (vertex : V) (index : Nat)
    (bound : index ≤ (profile.treeWalk preconnected vertex).length) :
    profile.depth preconnected
        ((profile.treeWalk preconnected vertex).getVert index) = index := by
  let walk := profile.treeWalk preconnected vertex
  let point := walk.getVert index
  have prefixShortest :
      (walk.take index).length = object.graph.dist profile.root point :=
    SimpleGraph.length_eq_dist_of_subwalk
      (profile.treeWalk_shortest preconnected vertex)
      (SimpleGraph.Walk.isSubwalk_take walk index)
  calc
    profile.depth preconnected point = object.graph.dist profile.root point := by
      rw [← profile.treeWalk_shortest preconnected point,
        profile.treeWalk_length]
    _ = (walk.take index).length := prefixShortest.symm
    _ = index := by simp [walk, SimpleGraph.Walk.take_length,
      Nat.min_eq_left bound]

theorem treeWalk_successive_adjacent (preconnected : object.graph.Preconnected)
    (vertex : V) {index : Nat}
    (bound : index < (profile.treeWalk preconnected vertex).length) :
    object.graph.Adj
      ((profile.treeWalk preconnected vertex).getVert index)
      ((profile.treeWalk preconnected vertex).getVert (index + 1)) :=
  (profile.treeWalk preconnected vertex).adj_getVert_succ bound

/-- The walk to a nonroot vertex unfolds by one literal parent edge. -/
theorem treeWalk_eq_parent_concat (preconnected : object.graph.Preconnected)
    (vertex : V) (nonroot : vertex ≠ profile.root) :
    profile.treeWalk preconnected vertex =
      (profile.treeWalk preconnected
        (profile.treeParent preconnected vertex nonroot)).concat
          (profile.treeParent_adjacent preconnected vertex nonroot) := by
  let steps := profile.parentLevel preconnected vertex
  have depthEq : profile.depth preconnected vertex = steps + 1 :=
    (profile.parentLevel_succ_eq_depth preconnected nonroot).symm
  have unfolded := profile.treeWalkAux_succ_eq preconnected steps vertex depthEq
  rw [profile.treeWalk_eq_treeWalkAux preconnected (steps + 1) vertex depthEq,
    unfolded]
  congr 1
  symm
  apply profile.treeWalk_eq_treeWalkAux

theorem parent_support_prefix (preconnected : object.graph.Preconnected)
    (vertex : V) (nonroot : vertex ≠ profile.root) :
    (profile.treeWalk preconnected
        (profile.treeParent preconnected vertex nonroot)).support <+:
      (profile.treeWalk preconnected vertex).support := by
  rw [profile.treeWalk_eq_parent_concat preconnected vertex nonroot,
    SimpleGraph.Walk.support_concat]
  exact List.prefix_append _ _

/-- A vertex shared by two tree paths occurs at the same depth-index on both.
This is the index-level coherence fact used by later prefix comparison. -/
theorem common_support_has_same_depth_index
    (preconnected : object.graph.Preconnected)
    (left right point : V)
    (leftMem : point ∈ (profile.treeWalk preconnected left).support)
    (rightMem : point ∈ (profile.treeWalk preconnected right).support) :
    ∃ index : Nat,
      index ≤ (profile.treeWalk preconnected left).length ∧
      index ≤ (profile.treeWalk preconnected right).length ∧
      (profile.treeWalk preconnected left).getVert index = point ∧
      (profile.treeWalk preconnected right).getVert index = point := by
  obtain ⟨leftIndex, leftEq, leftBound⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp leftMem
  obtain ⟨rightIndex, rightEq, rightBound⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp rightMem
  have leftDepth := profile.treeWalk_getVert_depth preconnected left
    leftIndex leftBound
  have rightDepth := profile.treeWalk_getVert_depth preconnected right
    rightIndex rightBound
  rw [leftEq] at leftDepth
  rw [rightEq] at rightDepth
  have indexEq : leftIndex = rightIndex := leftDepth.symm.trans rightDepth
  rw [← indexEq] at rightBound rightEq
  exact ⟨leftIndex, leftBound, rightBound, leftEq, rightEq⟩

/-- Prefix coherence in list form: if `point` occurs on the tree path to
`vertex`, then the canonical tree path to `point` is exactly the prefix ending
at its depth-index. -/
theorem support_eq_take_of_mem (preconnected : object.graph.Preconnected) :
    ∀ (steps : Nat) (vertex point : V),
      profile.depth preconnected vertex = steps →
      point ∈ (profile.treeWalk preconnected vertex).support →
      (profile.treeWalk preconnected point).support =
        (profile.treeWalk preconnected vertex).support.take
          (profile.depth preconnected point + 1) := by
  intro steps
  induction steps with
  | zero =>
      intro vertex point depthEq member
      have vertexEq := profile.eq_root_of_depth_eq_zero preconnected depthEq
      subst vertex
      have rootWalk : profile.treeWalk preconnected profile.root = .nil := by
        apply SimpleGraph.Walk.Nil.eq_nil
        rw [← SimpleGraph.Walk.length_eq_zero_iff,
          profile.treeWalk_length, profile.depth_root]
      rw [rootWalk] at member ⊢
      simp at member
      subst point
      simpa [profile.depth_root preconnected] using
        congrArg SimpleGraph.Walk.support rootWalk
  | succ steps ih =>
      intro vertex point depthEq member
      have nonroot : vertex ≠ profile.root := by
        intro equal
        subst vertex
        rw [profile.depth_root preconnected] at depthEq
        omega
      let parent := profile.treeParent preconnected vertex nonroot
      have parentDepth : profile.depth preconnected parent = steps := by
        have drop := profile.treeParent_depth_drop preconnected vertex nonroot
        have drop' : profile.depth preconnected parent + 1 = steps + 1 := by
          simpa [parent, depthEq] using drop
        omega
      rw [profile.treeWalk_eq_parent_concat preconnected vertex nonroot,
        SimpleGraph.Walk.support_concat] at member ⊢
      rcases List.mem_append.mp member with parentMem | endpoint
      · have coherent := ih parent point parentDepth parentMem
        rw [coherent]
        have auxMem : point ∈
            (profile.treeWalkAux preconnected steps parent parentDepth).support := by
          rw [← profile.treeWalk_eq_treeWalkAux preconnected steps parent parentDepth]
          exact parentMem
        have pointDepth := profile.treeWalkAux_support_depth_le preconnected
          steps parent parentDepth point auxMem
        have takeBound : profile.depth preconnected point + 1 ≤
            (profile.treeWalk preconnected parent).support.length := by
          rw [SimpleGraph.Walk.length_support,
            profile.treeWalk_length, parentDepth]
          omega
        exact (List.take_append_of_le_length takeBound).symm
      · simp only [List.mem_singleton] at endpoint
        subst point
        have fullLength :
            (profile.treeWalk preconnected parent).support.length + 1 =
              profile.depth preconnected vertex + 1 := by
          rw [SimpleGraph.Walk.length_support,
            profile.treeWalk_length, parentDepth, depthEq]
        rw [profile.treeWalk_eq_parent_concat preconnected vertex nonroot,
          SimpleGraph.Walk.support_concat, ← fullLength]
        simp [parent]

theorem treeWalk_getVert_support_eq_take
    (preconnected : object.graph.Preconnected)
    (vertex : V) (index : Nat)
    (bound : index ≤ (profile.treeWalk preconnected vertex).length) :
    (profile.treeWalk preconnected
        ((profile.treeWalk preconnected vertex).getVert index)).support =
      (profile.treeWalk preconnected vertex).support.take (index + 1) := by
  have coherent := profile.support_eq_take_of_mem preconnected
    (profile.depth preconnected vertex) vertex
    ((profile.treeWalk preconnected vertex).getVert index) rfl
    ((profile.treeWalk preconnected vertex).getVert_mem_support index)
  rw [profile.treeWalk_getVert_depth preconnected vertex index bound] at coherent
  exact coherent

theorem common_vertex_forces_equal_prefixes
    (preconnected : object.graph.Preconnected)
    (left right point : V)
    (leftMem : point ∈ (profile.treeWalk preconnected left).support)
    (rightMem : point ∈ (profile.treeWalk preconnected right).support) :
    (profile.treeWalk preconnected left).support.take
        (profile.depth preconnected point + 1) =
      (profile.treeWalk preconnected right).support.take
        (profile.depth preconnected point + 1) := by
  rw [← profile.support_eq_take_of_mem preconnected
      (profile.depth preconnected left) left point rfl leftMem,
    ← profile.support_eq_take_of_mem preconnected
      (profile.depth preconnected right) right point rfl rightMem]

/-- Proof-carrying deterministic longest-common-prefix decomposition. -/
structure PrefixScan (left right : List V) where
  common : List V
  leftRest : List V
  rightRest : List V
  left_eq : left = common ++ leftRest
  right_eq : right = common ++ rightRest
  boundary : leftRest = [] ∨ rightRest = [] ∨
    ∃ leftNext leftTail rightNext rightTail,
      leftRest = leftNext :: leftTail ∧
      rightRest = rightNext :: rightTail ∧
      leftNext ≠ rightNext

/-- Literal head-by-head longest-common-prefix scan. -/
def prefixScan [DecidableEq V] :
    (left right : List V) → PrefixScan left right
  | [], right => {
      common := []
      leftRest := []
      rightRest := right
      left_eq := rfl
      right_eq := rfl
      boundary := Or.inl rfl
    }
  | left, [] => {
      common := []
      leftRest := left
      rightRest := []
      left_eq := rfl
      right_eq := rfl
      boundary := Or.inr (Or.inl rfl)
    }
  | leftHead :: leftTail, rightHead :: rightTail =>
      if equal : leftHead = rightHead then
        let rest := prefixScan leftTail rightTail
        {
          common := leftHead :: rest.common
          leftRest := rest.leftRest
          rightRest := rest.rightRest
          left_eq := by simp [equal, rest.left_eq]
          right_eq := by simp [equal, rest.right_eq]
          boundary := rest.boundary
        }
      else {
        common := []
        leftRest := leftHead :: leftTail
        rightRest := rightHead :: rightTail
        left_eq := rfl
        right_eq := rfl
        boundary := Or.inr (Or.inr
          ⟨leftHead, leftTail, rightHead, rightTail, rfl, rfl, equal⟩)
      }

theorem prefixScan_common_prefix_left [DecidableEq V]
    (left right : List V) :
    (prefixScan left right).common <+: left := by
  induction left generalizing right with
  | nil => simp [prefixScan]
  | cons head tail ih =>
      cases right with
      | nil => simp [prefixScan]
      | cons other rest =>
          by_cases equal : head = other
          · simp [prefixScan, equal, ih rest]
          · simp [prefixScan, equal]

theorem prefixScan_common_prefix_right [DecidableEq V]
    (left right : List V) :
    (prefixScan left right).common <+: right := by
  induction left generalizing right with
  | nil => simp [prefixScan]
  | cons head tail ih =>
      cases right with
      | nil => simp [prefixScan]
      | cons other rest =>
          by_cases equal : head = other
          · subst other
            simp [prefixScan, ih rest]
          · simp [prefixScan, equal]

theorem prefixScan_budget [DecidableEq V] (left right : List V) :
    (prefixScan left right).common.length + 1 ≤ left.length + 1 ∧
      (prefixScan left right).common.length + 1 ≤ right.length + 1 := by
  constructor
  · exact Nat.add_le_add_right
      (List.IsPrefix.length_le (prefixScan_common_prefix_left left right)) 1
  · exact Nat.add_le_add_right
      (List.IsPrefix.length_le (prefixScan_common_prefix_right left right)) 1

/-- An entry of a decomposed tree-path suffix has the index obtained by
adding its suffix index to the common-prefix length. -/
theorem suffix_getElem_depth (preconnected : object.graph.Preconnected)
    (vertex : V) (common rest : List V)
    (decomposition :
      (profile.treeWalk preconnected vertex).support = common ++ rest)
    (index : Nat) (bound : index < rest.length) :
    profile.depth preconnected rest[index] = common.length + index := by
  let walk := profile.treeWalk preconnected vertex
  have supportLength : walk.support.length = common.length + rest.length := by
    rw [decomposition, List.length_append]
  have walkBound : common.length + index ≤ walk.length := by
    rw [SimpleGraph.Walk.length_support] at supportLength
    omega
  have atDepth := profile.treeWalk_getVert_depth preconnected vertex
    (common.length + index) walkBound
  rw [walk.getVert_eq_support_getElem walkBound] at atDepth
  have valueEq :
      walk.support[common.length + index]'(by
        rw [SimpleGraph.Walk.length_support]
        omega) = rest[index]'bound := by
    have valueOption := congrArg
      (fun values : List V => values[common.length + index]?) decomposition
    have leftIn : common.length + index < walk.support.length := by
      rw [SimpleGraph.Walk.length_support]
      omega
    rw [List.getElem?_eq_getElem leftIn] at valueOption
    simp [bound] at valueOption
    exact valueOption
  rw [valueEq] at atDepth
  simpa [walk] using atDepth

/-- Every vertex in a decomposed suffix lies at or below the first suffix
level.  The existential index is retained for consumers that need the exact
level rather than only the lower bound. -/
theorem suffix_mem_depth (preconnected : object.graph.Preconnected)
    (vertex point : V) (common rest : List V)
    (decomposition :
      (profile.treeWalk preconnected vertex).support = common ++ rest)
    (member : point ∈ rest) :
    ∃ index : Fin rest.length, rest[index] = point ∧
      profile.depth preconnected point = common.length + index := by
  obtain ⟨index, value⟩ := List.mem_iff_get.mp member
  refine ⟨index, value, ?_⟩
  rw [← value]
  exact profile.suffix_getElem_depth preconnected vertex common rest
    decomposition index index.isLt

private theorem next_eq_of_equal_deep_takes
    {common leftTail rightTail : List V} {leftNext rightNext : V}
    {level : Nat}
    (deep : common.length < level)
    (equalTakes :
      (common ++ leftNext :: leftTail).take level =
        (common ++ rightNext :: rightTail).take level) :
    leftNext = rightNext := by
  have atBoundary := congrArg (List.drop common.length) equalTakes
  have heads := congrArg List.head? atBoundary
  have positive : 0 < level - common.length := by omega
  cases difference : level - common.length with
  | zero => omega
  | succ remaining =>
      simpa [List.drop_take, difference] using heads

/-- Once two canonical tree paths leave their longest common prefix through
distinct next vertices, their residual supports cannot meet again. -/
theorem distinct_next_suffixes_disjoint
    (preconnected : object.graph.Preconnected)
    (left right leftNext rightNext : V)
    (common leftTail rightTail : List V)
    (leftDecomposition :
      (profile.treeWalk preconnected left).support =
        common ++ leftNext :: leftTail)
    (rightDecomposition :
      (profile.treeWalk preconnected right).support =
        common ++ rightNext :: rightTail)
    (distinct : leftNext ≠ rightNext) :
    List.Disjoint (leftNext :: leftTail) (rightNext :: rightTail) := by
  rw [List.disjoint_left]
  intro point leftMem rightMem
  obtain ⟨leftIndex, _leftValue, leftDepth⟩ :=
    profile.suffix_mem_depth preconnected left point common
      (leftNext :: leftTail) leftDecomposition leftMem
  obtain ⟨rightIndex, _rightValue, rightDepth⟩ :=
    profile.suffix_mem_depth preconnected right point common
      (rightNext :: rightTail) rightDecomposition rightMem
  have equalPrefixes := profile.common_vertex_forces_equal_prefixes
    preconnected left right point
    (leftDecomposition.symm ▸ List.mem_append_right common leftMem)
    (rightDecomposition.symm ▸ List.mem_append_right common rightMem)
  have deep : common.length < profile.depth preconnected point + 1 := by
    omega
  have nextEqual := next_eq_of_equal_deep_takes deep (by
    simpa [leftDecomposition, rightDecomposition] using equalPrefixes)
  exact distinct nextEqual

/-- Consecutive entries exposed by an exact support decomposition are joined
by an ambient graph edge. -/
theorem adjacent_at_support_boundary
    (preconnected : object.graph.Preconnected)
    (vertex predecessor next : V) (before after : List V)
    (decomposition :
      (profile.treeWalk preconnected vertex).support =
        before ++ predecessor :: next :: after) :
    object.graph.Adj predecessor next := by
  let walk := profile.treeWalk preconnected vertex
  have supportLength :
      walk.support.length = before.length + (predecessor :: next :: after).length := by
    rw [decomposition, List.length_append]
  have edgeBound : before.length < walk.length := by
    rw [SimpleGraph.Walk.length_support] at supportLength
    simp only [List.length_cons] at supportLength
    omega
  have predecessorIn : before.length < walk.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have nextIn : before.length + 1 < walk.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have adjacent := profile.treeWalk_successive_adjacent preconnected vertex edgeBound
  rw [walk.getVert_eq_support_getElem edgeBound.le,
    walk.getVert_eq_support_getElem (by omega)] at adjacent
  have predecessorEq : walk.support[before.length]'predecessorIn = predecessor := by
    have valueOption := congrArg
      (fun values : List V => values[before.length]?) decomposition
    rw [List.getElem?_eq_getElem predecessorIn] at valueOption
    simpa using valueOption
  have nextEq : walk.support[before.length + 1]'nextIn = next := by
    have valueOption := congrArg
      (fun values : List V => values[before.length + 1]?) decomposition
    rw [List.getElem?_eq_getElem nextIn] at valueOption
    simpa using valueOption
  simpa [predecessorEq, nextEq] using adjacent

/-- Deterministic comparison data for two shared BFS tree paths. -/
def compareTreePaths (preconnected : object.graph.Preconnected)
    (left right : V) :
    PrefixScan (profile.treeWalk preconnected left).support
      (profile.treeWalk preconnected right).support := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact prefixScan _ _

/-- The divergent boundary returned by `compareTreePaths` is a genuine
no-reconvergence split of the two canonical tree supports. -/
theorem compareTreePaths_divergent_disjoint
    (preconnected : object.graph.Preconnected)
    (left right leftNext rightNext : V)
    (leftTail rightTail : List V)
    (leftRest :
      (profile.compareTreePaths preconnected left right).leftRest =
        leftNext :: leftTail)
    (rightRest :
      (profile.compareTreePaths preconnected left right).rightRest =
        rightNext :: rightTail)
    (distinct : leftNext ≠ rightNext) :
    List.Disjoint (leftNext :: leftTail) (rightNext :: rightTail) := by
  let comparison := profile.compareTreePaths preconnected left right
  apply profile.distinct_next_suffixes_disjoint preconnected left right
    leftNext rightNext comparison.common leftTail rightTail
  · simpa [comparison, leftRest] using comparison.left_eq
  · simpa [comparison, rightRest] using comparison.right_eq
  · exact distinct

/-- Both canonical paths start at the common root, hence their deterministic
longest common prefix does too. -/
theorem compareTreePaths_common_eq_root_cons
    (preconnected : object.graph.Preconnected) (left right : V) :
    ∃ commonTail : List V,
      (profile.compareTreePaths preconnected left right).common =
        profile.root :: commonTail := by
  letI : DecidableEq V := object.input.vertices.decEq
  rw [compareTreePaths,
    ← (profile.treeWalk preconnected left).cons_tail_support,
    ← (profile.treeWalk preconnected right).cons_tail_support]
  simp [prefixScan]

private structure LastTwoSplit (values : List V) where
  stem : List V
  predecessor : V
  separator : V
  split : values = stem ++ [predecessor, separator]

private def splitLastTwo : (values : List V) →
    2 ≤ values.length → LastTwoSplit values
  | [], lengthBound => by simp at lengthBound
  | [_], lengthBound => by simp at lengthBound
  | [first, second], _ => ⟨[], first, second, rfl⟩
  | first :: second :: third :: remaining, _ =>
      let rest := splitLastTwo (second :: third :: remaining) (by simp)
      ⟨first :: rest.stem, rest.predecessor, rest.separator, by
        have lifted := congrArg (List.cons first) rest.split
        simpa using lifted⟩

/-- Proof-carrying exhaustive comparison of two canonical rooted tree paths.
The equality case is deterministic: when both paths agree, `leftPrefix` is
chosen. -/
inductive TreePathComparison (preconnected : object.graph.Preconnected)
    (left right : V) : Type u where
  | leftPrefix (rightRest : List V)
      (right_eq :
        (profile.treeWalk preconnected right).support =
          (profile.treeWalk preconnected left).support ++ rightRest)
  | rightPrefix (leftRest : List V)
      (left_eq :
        (profile.treeWalk preconnected left).support =
          (profile.treeWalk preconnected right).support ++ leftRest)
  | divergeAtRoot
      (leftNext rightNext : V) (leftTail rightTail : List V)
      (left_eq :
        (profile.treeWalk preconnected left).support =
          [profile.root] ++ leftNext :: leftTail)
      (right_eq :
        (profile.treeWalk preconnected right).support =
          [profile.root] ++ rightNext :: rightTail)
      (distinct : leftNext ≠ rightNext)
      (leftAdjacent : object.graph.Adj profile.root leftNext)
      (rightAdjacent : object.graph.Adj profile.root rightNext)
      (residualDisjoint :
        List.Disjoint (leftNext :: leftTail) (rightNext :: rightTail))
  | divergeAfterEdge
      (stem : List V) (predecessor separator leftNext rightNext : V)
      (leftTail rightTail : List V)
      (left_eq :
        (profile.treeWalk preconnected left).support =
          (stem ++ [predecessor, separator]) ++ leftNext :: leftTail)
      (right_eq :
        (profile.treeWalk preconnected right).support =
          (stem ++ [predecessor, separator]) ++ rightNext :: rightTail)
      (predecessorAdjacent : object.graph.Adj predecessor separator)
      (leftAdjacent : object.graph.Adj separator leftNext)
      (rightAdjacent : object.graph.Adj separator rightNext)
      (distinct : leftNext ≠ rightNext)
      (residualDisjoint :
        List.Disjoint (leftNext :: leftTail) (rightNext :: rightTail))

/-- Total deterministic classifier obtained directly from the executable
prefix scan. -/
def classifyTreePaths (preconnected : object.graph.Preconnected)
    (left right : V) : profile.TreePathComparison preconnected left right := by
  let comparison := profile.compareTreePaths preconnected left right
  cases leftRestEq : comparison.leftRest with
  | nil =>
    apply TreePathComparison.leftPrefix comparison.rightRest
    calc
      (profile.treeWalk preconnected right).support =
          comparison.common ++ comparison.rightRest := comparison.right_eq
      _ = (profile.treeWalk preconnected left).support ++ comparison.rightRest := by
        have leftSupport :
            (profile.treeWalk preconnected left).support = comparison.common := by
          calc
            _ = comparison.common ++ comparison.leftRest := comparison.left_eq
            _ = comparison.common := by rw [leftRestEq]; simp
        exact congrArg (fun values => values ++ comparison.rightRest)
          leftSupport.symm
  | cons leftNext leftTail =>
    cases rightRestEq : comparison.rightRest with
    | nil =>
      apply TreePathComparison.rightPrefix comparison.leftRest
      calc
        (profile.treeWalk preconnected left).support =
            comparison.common ++ comparison.leftRest := comparison.left_eq
        _ = (profile.treeWalk preconnected right).support ++ comparison.leftRest := by
          have rightSupport :
              (profile.treeWalk preconnected right).support = comparison.common := by
            calc
              _ = comparison.common ++ comparison.rightRest := comparison.right_eq
              _ = comparison.common := by rw [rightRestEq]; simp
          exact congrArg (fun values => values ++ comparison.leftRest)
            rightSupport.symm
    | cons rightNext rightTail =>
      have distinct : leftNext ≠ rightNext := by
        rcases comparison.boundary with leftEmpty | rightEmpty | divergent
        · rw [leftRestEq] at leftEmpty
          simp at leftEmpty
        · rw [rightRestEq] at rightEmpty
          simp at rightEmpty
        · obtain ⟨otherLeft, otherLeftTail, otherRight, otherRightTail,
            otherLeftEq, otherRightEq, otherDistinct⟩ := divergent
          rw [leftRestEq] at otherLeftEq
          rw [rightRestEq] at otherRightEq
          cases otherLeftEq
          cases otherRightEq
          exact otherDistinct
      have leftDecomposition :
          (profile.treeWalk preconnected left).support =
            comparison.common ++ leftNext :: leftTail := by
        simpa [leftRestEq] using comparison.left_eq
      have rightDecomposition :
          (profile.treeWalk preconnected right).support =
            comparison.common ++ rightNext :: rightTail := by
        simpa [rightRestEq] using comparison.right_eq
      have disjoint := profile.distinct_next_suffixes_disjoint preconnected
        left right leftNext rightNext comparison.common leftTail rightTail
        leftDecomposition rightDecomposition distinct
      cases commonEq : comparison.common with
      | nil =>
          have impossible : False := by
            obtain ⟨commonTail, commonRoot⟩ :=
              profile.compareTreePaths_common_eq_root_cons preconnected left right
            rw [commonEq] at commonRoot
            simp at commonRoot
          exact impossible.elim
      | cons commonHead commonTail =>
        have headEq : commonHead = profile.root := by
          obtain ⟨rootTail, commonRoot⟩ :=
            profile.compareTreePaths_common_eq_root_cons preconnected left right
          rw [commonEq] at commonRoot
          exact List.cons.inj commonRoot |>.1
        cases commonTail with
        | nil =>
          have rootCommon : comparison.common = [profile.root] := by
            simpa [headEq] using commonEq
          apply TreePathComparison.divergeAtRoot leftNext rightNext
            leftTail rightTail
          · simpa [rootCommon] using leftDecomposition
          · simpa [rootCommon] using rightDecomposition
          · exact distinct
          · apply profile.adjacent_at_support_boundary preconnected
              left profile.root leftNext [] leftTail
            simpa [rootCommon] using leftDecomposition
          · apply profile.adjacent_at_support_boundary preconnected
              right profile.root rightNext [] rightTail
            simpa [rootCommon] using rightDecomposition
          · exact disjoint
        | cons second remaining =>
          let split := splitLastTwo comparison.common (by
            rw [commonEq]
            simp)
          apply TreePathComparison.divergeAfterEdge split.stem
            split.predecessor split.separator
            leftNext rightNext leftTail rightTail
          · simpa [split.split] using leftDecomposition
          · simpa [split.split] using rightDecomposition
          · apply profile.adjacent_at_support_boundary preconnected left
              split.predecessor split.separator split.stem
              (leftNext :: leftTail)
            simpa [split.split, List.append_assoc] using leftDecomposition
          · apply profile.adjacent_at_support_boundary preconnected left
              split.separator leftNext (split.stem ++ [split.predecessor]) leftTail
            simpa [split.split, List.append_assoc] using leftDecomposition
          · apply profile.adjacent_at_support_boundary preconnected right
              split.separator rightNext (split.stem ++ [split.predecessor]) rightTail
            simpa [split.split, List.append_assoc] using rightDecomposition
          · exact distinct
          · exact disjoint

@[simp] theorem treeWalk_root (preconnected : object.graph.Preconnected) :
    profile.treeWalk preconnected profile.root = .nil := by
  apply SimpleGraph.Walk.Nil.eq_nil
  rw [← SimpleGraph.Walk.length_eq_zero_iff,
    profile.treeWalk_length, profile.depth_root]

/-- Two-stage executable target selection: first scan bounded BFS levels,
then scan the declared vertex order inside the first occupied target level. -/
structure TargetSelection (preconnected : object.graph.Preconnected)
    (target : Finset V) where
  levelHit : Core.FiniteSearch.FirstHit
    (List.range (object.input.vertices.card + 1))
    (fun level => ∃ vertex ∈ target,
      profile.depth preconnected vertex = level)
  vertexHit : Core.FiniteSearch.FirstHit object.input.vertices.orderedValues
    (fun vertex => vertex ∈ target ∧
      profile.depth preconnected vertex = levelHit.value)

/-- Total target selector for a nonempty finite target. -/
def selectTarget (preconnected : object.graph.Preconnected)
    (target : Finset V) (nonempty : target.Nonempty) :
    profile.TargetSelection preconnected target := by
  letI : DecidableEq V := object.input.vertices.decEq
  let levelResult := Core.FiniteSearch.firstOnList
    (List.range (object.input.vertices.card + 1))
    (fun level => ∃ vertex ∈ target,
      profile.depth preconnected vertex = level)
    (fun _ => inferInstance)
  cases levelEq : levelResult with
  | absent absent =>
      have impossible : False := by
        obtain ⟨vertex, member⟩ := nonempty
        exact absent (profile.depth preconnected vertex)
          (by simp [profile.depth_le_order preconnected vertex])
          ⟨vertex, member, rfl⟩
      exact impossible.elim
  | found levelHit =>
      let vertexResult := Core.FiniteSearch.firstOnList
        object.input.vertices.orderedValues
        (fun vertex => vertex ∈ target ∧
          profile.depth preconnected vertex = levelHit.value)
        (fun _ => inferInstance)
      cases vertexEq : vertexResult with
      | absent absent =>
          have impossible : False := by
            obtain ⟨vertex, member, depthEq⟩ := levelHit.holds
            exact absent vertex (object.input.vertices.mem_orderedValues vertex)
              ⟨member, depthEq⟩
          exact impossible.elim
      | found vertexHit => exact ⟨levelHit, vertexHit⟩

def TargetSelection.vertex
    {preconnected : object.graph.Preconnected} {target : Finset V}
    (selection : profile.TargetSelection preconnected target) : V :=
  selection.vertexHit.value

def TargetSelection.before
    {preconnected : object.graph.Preconnected} {target : Finset V}
    (selection : profile.TargetSelection preconnected target) : List V :=
  selection.vertexHit.before

theorem TargetSelection.vertex_mem
    {preconnected : object.graph.Preconnected} {target : Finset V}
    (selection : profile.TargetSelection preconnected target) :
    selection.vertex ∈ target :=
  selection.vertexHit.holds.1

theorem TargetSelection.depth_eq_level
    {preconnected : object.graph.Preconnected} {target : Finset V}
    (selection : profile.TargetSelection preconnected target) :
    profile.depth preconnected selection.vertex = selection.levelHit.value :=
  selection.vertexHit.holds.2

private theorem rangeHit_before_eq_range {predicate : Nat → Prop}
    {bound : Nat}
    (hit : Core.FiniteSearch.FirstHit (List.range bound) predicate) :
    hit.before = List.range hit.value := by
  have lengths := congrArg List.length hit.split
  have valueBound : hit.value < bound := by
    have := hit.member
    simpa using this
  have beforeLength : hit.before.length = hit.value := by
    have entries := congrArg
      (fun values : List Nat => values[hit.before.length]?) hit.split
    simp only [List.length_range, List.length_append, List.length_cons] at lengths
    have prefixBound : hit.before.length < bound := by omega
    simpa [prefixBound] using entries
  have taken := congrArg (List.take hit.before.length) hit.split
  simpa [beforeLength, Nat.min_eq_left valueBound.le] using taken.symm

theorem TargetSelection.minimal_depth
    {preconnected : object.graph.Preconnected} {target : Finset V}
    (selection : profile.TargetSelection preconnected target)
    {candidate : V} (member : candidate ∈ target) :
    profile.depth preconnected selection.vertex ≤
      profile.depth preconnected candidate := by
  rw [selection.depth_eq_level]
  by_contra shallower
  have candidateBefore : profile.depth preconnected candidate ∈
      selection.levelHit.before := by
    rw [rangeHit_before_eq_range]
    simp
    omega
  exact selection.levelHit.beforeAbsent
    (profile.depth preconnected candidate) candidateBefore
    ⟨candidate, member, rfl⟩

/-- The retained vertex is the first declared vertex at the minimum target
depth. -/
theorem TargetSelection.declared_tie_break
    {preconnected : object.graph.Preconnected} {target : Finset V}
    (selection : profile.TargetSelection preconnected target) :
    ∀ candidate ∈ selection.before,
      ¬(candidate ∈ target ∧
        profile.depth preconnected candidate =
          profile.depth preconnected selection.vertex) := by
  intro candidate earlier
  rw [selection.depth_eq_level]
  exact selection.vertexHit.beforeAbsent candidate earlier

/-- The canonical root walk reaches the selected target for the first time at
its endpoint. -/
theorem TargetSelection.treeWalk_first_lands
    {preconnected : object.graph.Preconnected} {target : Finset V}
    (selection : profile.TargetSelection preconnected target) :
    selection.vertex ∈ target ∧
      ∀ index < (profile.treeWalk preconnected selection.vertex).length,
        (profile.treeWalk preconnected selection.vertex).getVert index ∉ target := by
  refine ⟨selection.vertex_mem, ?_⟩
  intro index indexBound pointMem
  have minimum := TargetSelection.minimal_depth profile selection pointMem
  rw [profile.treeWalk_getVert_depth preconnected selection.vertex index
      indexBound.le] at minimum
  rw [profile.treeWalk_length] at indexBound
  omega

/-- The selected tree walk is no longer than any root walk ending in the
target. -/
theorem TargetSelection.shortest_to_target
    {preconnected : object.graph.Preconnected} {target : Finset V}
    (selection : profile.TargetSelection preconnected target)
    {candidate : V} (member : candidate ∈ target)
    (walk : object.graph.Walk profile.root candidate) :
    (profile.treeWalk preconnected selection.vertex).length ≤ walk.length := by
  rw [profile.treeWalk_length]
  exact (TargetSelection.minimal_depth profile selection member).trans
    (profile.depth_le_walk_length preconnected candidate walk)

/-- Static upper budget for one layer construction: one declared-vertex scan,
with at most one full current-frontier scan per vertex.  This is an algebraic
budget, not an instrumented execution counter. -/
def stepBudget (steps : Nat) : Nat :=
  object.input.vertices.card * ((profile.layer steps).card + 1)

def budget (profile : Profile object) : Nat → Nat
  | 0 => 1
  | steps + 1 => profile.budget steps + profile.stepBudget steps

theorem stepBudget_le_quadratic (steps : Nat) :
    profile.stepBudget steps ≤
      object.input.vertices.card * (object.input.vertices.card + 1) := by
  unfold stepBudget
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (profile.card_layer_le_order steps) 1)

theorem budget_polynomial (steps : Nat) :
    profile.budget steps ≤
      1 + steps *
        (object.input.vertices.card * (object.input.vertices.card + 1)) := by
  induction steps with
  | zero => simp [budget]
  | succ steps ih =>
      rw [budget]
      calc
        _ ≤ (1 + steps *
              (object.input.vertices.card * (object.input.vertices.card + 1))) +
            object.input.vertices.card * (object.input.vertices.card + 1) :=
          Nat.add_le_add ih (profile.stepBudget_le_quadratic steps)
        _ = 1 + (steps + 1) *
              (object.input.vertices.card * (object.input.vertices.card + 1)) := by
          rw [Nat.add_mul]
          simp [Nat.add_assoc]

end Profile

end StructuralExhaustion.Graph.OrderedBFSTree
