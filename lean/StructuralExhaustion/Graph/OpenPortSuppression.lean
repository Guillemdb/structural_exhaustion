import Mathlib.Tactic
import StructuralExhaustion.Graph.PackedMinimumDegreeCycle

namespace StructuralExhaustion.Graph.OpenPortSuppression

open StructuralExhaustion
open scoped Sym2

universe u

/-!
# Suppression of one open cubic port

This module implements the local graph operation which deletes one cubic port
vertex and replaces its two shoulder incidences by the shoulder edge.  Its
input is only the four named vertices and their local adjacency facts.  In
particular, neither the construction nor any theorem below enumerates paths,
subgraphs, or finite graphs.
-/

/-- Local data for an open cubic port at a high centre. -/
structure Setup {V : Type u} (object : FiniteObject V) where
  center : V
  endpoint : V
  first : V
  second : V
  endpoint_ne_center : endpoint ≠ center
  endpoint_ne_first : endpoint ≠ first
  endpoint_ne_second : endpoint ≠ second
  first_ne_second : first ≠ second
  center_ne_first : center ≠ first
  center_ne_second : center ≠ second
  endpoint_neighbors : ∀ vertex,
    object.graph.Adj endpoint vertex ↔
      vertex = center ∨ vertex = first ∨ vertex = second
  open_shoulders : ¬object.graph.Adj first second
  center_high : 4 ≤ object.degree center

namespace Setup

variable {V : Type u} {object : FiniteObject V} (setup : Setup object)

/-- The surviving vertex type after deleting the port endpoint. -/
abbrev Vertex := {vertex : V // vertex ≠ setup.endpoint}

def centerVertex : setup.Vertex := ⟨setup.center, setup.endpoint_ne_center.symm⟩
def firstVertex : setup.Vertex := ⟨setup.first, setup.endpoint_ne_first.symm⟩
def secondVertex : setup.Vertex := ⟨setup.second, setup.endpoint_ne_second.symm⟩

/-- The suppressed graph: old edges away from the endpoint, together with the
one new undirected shoulder edge.  Simplicity is built into `SimpleGraph` and
proved directly from the open-port inequalities. -/
def graph : SimpleGraph setup.Vertex where
  Adj left right :=
    object.graph.Adj left.1 right.1 ∨
      (left.1 = setup.first ∧ right.1 = setup.second) ∨
      (left.1 = setup.second ∧ right.1 = setup.first)
  symm.symm := by
    intro left right adjacent
    rcases adjacent with old | forward | backward
    · exact Or.inl old.symm
    · exact Or.inr (Or.inr ⟨forward.2, forward.1⟩)
    · exact Or.inr (Or.inl ⟨backward.2, backward.1⟩)
  loopless.irrefl := by
    intro vertex adjacent
    rcases adjacent with old | forward | backward
    · exact old.ne rfl
    · exact setup.first_ne_second (forward.1.symm.trans forward.2)
    · exact setup.first_ne_second (backward.2.symm.trans backward.1)

@[simp] theorem graph_adj_iff (left right : setup.Vertex) :
    setup.graph.Adj left right ↔
      object.graph.Adj left.1 right.1 ∨
        (left.1 = setup.first ∧ right.1 = setup.second) ∨
        (left.1 = setup.second ∧ right.1 = setup.first) :=
  Iff.rfl

@[simp] theorem first_second_adj :
    setup.graph.Adj setup.firstVertex setup.secondVertex := by
  exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- Explicit finite execution object for the suppressed graph. -/
def suppressedObject : FiniteObject setup.Vertex where
  graph := setup.graph
  input := {
    vertices := Core.Enumeration.subtype object.input.vertices
      (fun vertex => vertex ≠ setup.endpoint) (by
        letI : DecidableEq V := object.input.vertices.decEq
        infer_instance)
    decideAdj := by
      letI : DecidableEq V := object.input.vertices.decEq
      letI : DecidableEq V := object.input.vertices.decEq
      letI : DecidableRel object.graph.Adj := object.input.decideAdj
      intro left right
      change Decidable (object.graph.Adj left.1 right.1 ∨
        (left.1 = setup.first ∧ right.1 = setup.second) ∨
        (left.1 = setup.second ∧ right.1 = setup.first))
      infer_instance
  }

theorem suppressed_vertexCount_lt :
    setup.suppressedObject.input.vertices.card <
      object.input.vertices.card := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : FinEnum setup.Vertex := setup.suppressedObject.input.vertices
  rw [FinEnum.card_eq_fintypeCard, FinEnum.card_eq_fintypeCard]
  exact Fintype.card_subtype_lt (p := fun vertex : V => vertex ≠ setup.endpoint)
    (x := setup.endpoint) (by simp)

/-- Strict decrease in the packed lexicographic rank comes solely from the
one deleted vertex; the added shoulder edge need not be counted. -/
theorem packedRank_lt :
    (PackedFiniteObject.pack setup.suppressedObject).lexRank <
      (PackedFiniteObject.pack object).lexRank := by
  apply PackedFiniteObject.lexRank_lt_of_vertexCount_lt
  simp only [PackedFiniteObject.vertexCount_pack]
  exact setup.suppressed_vertexCount_lt

private def liftAway (vertex : setup.Vertex) [DecidableEq V]
    (other : V) : setup.Vertex :=
  if equal : other = setup.endpoint then vertex else ⟨other, equal⟩

private theorem liftAway_eq [DecidableEq V] (vertex : setup.Vertex) {other : V}
    (away : other ≠ setup.endpoint) : setup.liftAway vertex other = ⟨other, away⟩ := by
  simp [liftAway, away]

private theorem oldNeighborInjection (vertex : setup.Vertex) :
    (object.graph.neighborSet vertex.1 \ {setup.endpoint}).ncard ≤
      setup.suppressedObject.degree vertex := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : FinEnum setup.Vertex := setup.suppressedObject.input.vertices
  letI : DecidableRel setup.graph.Adj := setup.suppressedObject.input.decideAdj
  let domain := object.graph.neighborSet vertex.1 \ {setup.endpoint}
  let f : V → setup.Vertex := setup.liftAway vertex
  have maps : ∀ other ∈ domain,
      f other ∈ setup.graph.neighborSet vertex := by
    intro other member
    have away : other ≠ setup.endpoint := by simpa [domain] using member.2
    have adjacent : object.graph.Adj vertex.1 other := member.1
    simpa [f, liftAway_eq setup vertex away] using (Or.inl adjacent)
  have injective : Set.InjOn f domain := by
    intro left leftMem right rightMem equal
    have leftAway : left ≠ setup.endpoint := by simpa [domain] using leftMem.2
    have rightAway : right ≠ setup.endpoint := by simpa [domain] using rightMem.2
    simpa [f, liftAway_eq setup vertex leftAway,
      liftAway_eq setup vertex rightAway] using congrArg Subtype.val equal
  rw [setup.suppressedObject.degree_eq_ncard_neighborSet]
  exact Set.ncard_le_ncard_of_injOn f maps injective

private theorem shoulder_degree (baseline : 3 ≤ object.minDegree)
    (shoulder other : V)
    (shoulderAway : shoulder ≠ setup.endpoint)
    (otherAway : other ≠ setup.endpoint)
    (endpointAdjacent : object.graph.Adj shoulder setup.endpoint)
    (otherNotOld : ¬object.graph.Adj shoulder other)
    (newAdjacent : setup.graph.Adj
      (⟨shoulder, shoulderAway⟩ : setup.Vertex) ⟨other, otherAway⟩) :
    3 ≤ setup.suppressedObject.degree ⟨shoulder, shoulderAway⟩ := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : FinEnum setup.Vertex := setup.suppressedObject.input.vertices
  letI : DecidableRel setup.graph.Adj := setup.suppressedObject.input.decideAdj
  let vertex : setup.Vertex := ⟨shoulder, shoulderAway⟩
  let domain := insert other
    (object.graph.neighborSet shoulder \ {setup.endpoint})
  let f : V → setup.Vertex := setup.liftAway vertex
  have otherNotDomain : other ∉
      object.graph.neighborSet shoulder \ {setup.endpoint} := by
    intro member
    exact otherNotOld member.1
  have domainCard : 3 ≤ domain.ncard := by
    rw [Set.ncard_insert_of_notMem otherNotDomain]
    rw [Set.ncard_sdiff_singleton_of_mem (by simpa using endpointAdjacent)]
    rw [← object.degree_eq_ncard_neighborSet]
    have degreeThree : 3 ≤ object.degree shoulder :=
      baseline.trans (object.minDegree_le_degree shoulder)
    omega
  have maps : ∀ candidate ∈ domain,
      f candidate ∈ setup.graph.neighborSet vertex := by
    intro candidate member
    rcases member with rfl | old
    · simpa [f, liftAway_eq setup vertex otherAway] using newAdjacent
    · have away : candidate ≠ setup.endpoint := by simpa [domain] using old.2
      simpa [f, liftAway_eq setup vertex away] using (Or.inl old.1)
  have injective : Set.InjOn f domain := by
    intro left leftMem right rightMem equal
    have leftAway : left ≠ setup.endpoint := by
      rcases leftMem with rfl | old
      · exact otherAway
      · simpa using old.2
    have rightAway : right ≠ setup.endpoint := by
      rcases rightMem with rfl | old
      · exact otherAway
      · simpa using old.2
    simpa [f, liftAway_eq setup vertex leftAway,
      liftAway_eq setup vertex rightAway] using congrArg Subtype.val equal
  have cardLe : domain.ncard ≤ setup.suppressedObject.degree vertex := by
    rw [setup.suppressedObject.degree_eq_ncard_neighborSet]
    exact Set.ncard_le_ncard_of_injOn f maps injective
  exact domainCard.trans cardLe

private theorem pointwise_degree (vertex : setup.Vertex)
    (baseline : 3 ≤ object.minDegree) :
    3 ≤ setup.suppressedObject.degree vertex := by
  by_cases first : vertex.1 = setup.first
  · have vertexEq : vertex = setup.firstVertex := Subtype.ext first
    subst vertexEq
    apply setup.shoulder_degree baseline setup.first setup.second
      setup.endpoint_ne_first.symm setup.endpoint_ne_second.symm
    · exact ((setup.endpoint_neighbors setup.first).2 (Or.inr (Or.inl rfl))).symm
    · exact setup.open_shoulders
    · exact setup.first_second_adj
  by_cases second : vertex.1 = setup.second
  · have vertexEq : vertex = setup.secondVertex := Subtype.ext second
    subst vertexEq
    apply setup.shoulder_degree baseline setup.second setup.first
      setup.endpoint_ne_second.symm setup.endpoint_ne_first.symm
    · exact ((setup.endpoint_neighbors setup.second).2 (Or.inr (Or.inr rfl))).symm
    · exact fun adjacent => setup.open_shoulders adjacent.symm
    · exact setup.first_second_adj.symm
  have oldLower := setup.oldNeighborInjection vertex
  by_cases central : vertex.1 = setup.center
  · have degreeFour : 4 ≤ object.degree vertex.1 := by simpa [central] using setup.center_high
    have endpointMem : setup.endpoint ∈ object.graph.neighborSet vertex.1 := by
      simpa [central] using
        ((setup.endpoint_neighbors setup.center).2 (Or.inl rfl)).symm
    rw [Set.ncard_sdiff_singleton_of_mem endpointMem,
      ← object.degree_eq_ncard_neighborSet] at oldLower
    omega
  · have notAdjacent : ¬object.graph.Adj vertex.1 setup.endpoint := by
      intro adjacent
      have classified := (setup.endpoint_neighbors vertex.1).1 adjacent.symm
      rcases classified with equal | equal | equal
      · exact central equal
      · exact first equal
      · exact second equal
    have endpointNotMem : setup.endpoint ∉ object.graph.neighborSet vertex.1 := by
      simpa using notAdjacent
    rw [Set.sdiff_singleton_eq_self endpointNotMem,
      ← object.degree_eq_ncard_neighborSet] at oldLower
    exact baseline.trans (object.minDegree_le_degree vertex.1) |>.trans oldLower

/-- Suppressing one open cubic port preserves minimum degree three by a
pointwise local neighbour injection. -/
theorem minDegree_three (baseline : 3 ≤ object.minDegree) :
    3 ≤ setup.suppressedObject.minDegree := by
  letI : Nonempty setup.Vertex := ⟨setup.centerVertex⟩
  apply setup.suppressedObject.le_minDegree_of_forall_le_degree
  intro vertex
  exact pointwise_degree setup vertex baseline

/-! ## Local extraction from a cycle using the new shoulder edge -/

/-- A simple cycle containing a named edge can be oriented to start with that
edge.  This is a certificate transformation on one supplied Mathlib walk; it
does not search for a cycle or a path. -/
theorem orientCycleAtEdge {W : Type*} [DecidableEq W]
    {G : SimpleGraph W} {first second root : W}
    (cycle : G.Walk root root)
    (isCycle : cycle.IsCycle) (uses : s(first, second) ∈ cycle.edges) :
    ∃ oriented : G.Walk first first,
      oriented.IsCycle ∧ oriented.snd = second ∧
        oriented.length = cycle.length := by
  have firstMem : first ∈ cycle.support :=
    cycle.fst_mem_support_of_mem_edges uses
  let rotated := cycle.rotate first firstMem
  have rotatedCycle : rotated.IsCycle := isCycle.rotate firstMem
  have rotatedUses : s(first, second) ∈ rotated.edges := by
    exact (cycle.rotate_edges first firstMem).perm.mem_iff.mpr uses
  by_cases tailUses : s(first, second) ∈ rotated.tail.edges
  · refine ⟨rotated.reverse, rotatedCycle.reverse, ?_, ?_⟩
    · rw [SimpleGraph.Walk.snd_reverse]
      have atEnd : second = rotated.tail.penultimate :=
        rotatedCycle.isPath_tail.eq_penultimate_of_mem_edges tailUses
      change second = rotated.tail.getVert (rotated.tail.length - 1) at atEnd
      rw [SimpleGraph.Walk.getVert_tail] at atEnd
      have tailLength := rotated.length_tail_add_one rotatedCycle.not_nil
      have cycleLength : 3 ≤ rotated.length := rotatedCycle.three_le_length
      have indexEq : rotated.tail.length - 1 + 1 = rotated.length - 1 := by
        omega
      rw [indexEq] at atEnd
      exact atEnd.symm
    · simp [rotated]
  · have rotatedNonNil : ¬rotated.Nil := rotatedCycle.not_nil
    have edgeHeadOrTail :
        s(first, second) = s(first, rotated.snd) ∨
          s(first, second) ∈ rotated.tail.edges := by
      rw [← rotated.cons_tail_eq rotatedNonNil] at rotatedUses
      rw [SimpleGraph.Walk.edges_cons] at rotatedUses
      simpa only [List.mem_cons] using rotatedUses
    have edgeEq : s(first, second) = s(first, rotated.snd) :=
      edgeHeadOrTail.resolve_right tailUses
    have sndEq : rotated.snd = second := by
      exact (Sym2.congr_right.mp edgeEq).symm
    exact ⟨rotated, rotatedCycle, sndEq, by simp [rotated]⟩

/-- The old induced graph on the surviving vertices. -/
def oldGraph : SimpleGraph setup.Vertex :=
  object.graph.comap (fun vertex : setup.Vertex => vertex.1)

private theorem old_adj_of_suppressed_adj {left right : setup.Vertex}
    (adjacent : setup.graph.Adj left right)
    (notChord : s(left, right) ≠ s(setup.firstVertex, setup.secondVertex)) :
    setup.oldGraph.Adj left right := by
  rcases adjacent with old | added | added
  · exact old
  · have leftEq : left = setup.firstVertex := Subtype.ext added.1
    have rightEq : right = setup.secondVertex := Subtype.ext added.2
    subst leftEq; subst rightEq
    exact (notChord rfl).elim
  · have leftEq : left = setup.secondVertex := Subtype.ext added.1
    have rightEq : right = setup.firstVertex := Subtype.ext added.2
    subst leftEq; subst rightEq
    exact (notChord Sym2.eq_swap).elim

/-- Transfer a supplied suppressed walk which avoids the new chord into the
old induced graph. -/
def toOldWalk {left right : setup.Vertex}
    (walk : setup.graph.Walk left right)
    (avoids : s(setup.firstVertex, setup.secondVertex) ∉ walk.edges) :
    setup.oldGraph.Walk left right := by
  apply walk.transfer setup.oldGraph
  intro edge member
  induction edge using Sym2.inductionOn with
  | _ a b =>
      have adjacent : setup.graph.Adj a b := by
        simpa using walk.edges_subset_edgeSet member
      have notChord : s(a, b) ≠ s(setup.firstVertex, setup.secondVertex) := by
        intro equal
        exact avoids (equal ▸ member)
      simpa using setup.old_adj_of_suppressed_adj adjacent notChord

/-- Map an old induced walk back into the source graph. -/
def oldEmbedding : setup.oldGraph ↪g object.graph where
  toFun := fun vertex => vertex.1
  inj' := Subtype.val_injective
  map_rel_iff' := by
    intro left right
    rfl

def toSourceWalk {left right : setup.Vertex}
    (walk : setup.oldGraph.Walk left right) :
    object.graph.Walk left.1 right.1 :=
  (walk.map setup.oldEmbedding.toHom).copy rfl rfl

theorem endpoint_not_mem_toSourceWalk {left right : setup.Vertex}
    (walk : setup.oldGraph.Walk left right) :
    setup.endpoint ∉ (setup.toSourceWalk walk).support := by
  intro member
  have mappedMember : setup.endpoint ∈
      (walk.map setup.oldEmbedding.toHom).support := by
    simpa only [toSourceWalk, SimpleGraph.Walk.support_copy] using member
  rw [SimpleGraph.Walk.support_map] at mappedMember
  obtain ⟨vertex, _vertexMember, equal⟩ := List.mem_map.mp mappedMember
  exact vertex.2 equal

/-- Exact local path output of one open-port suppression. -/
structure SuppressionPath (LengthOK : Nat → Prop) where
  path : object.graph.Walk setup.first setup.second
  isPath : path.IsPath
  endpoint_not_mem : setup.endpoint ∉ path.support
  predecessor_length : LengthOK (path.length + 1)

def HasSuppressionPath (LengthOK : Nat → Prop) : Prop :=
  Nonempty (SuppressionPath setup LengthOK)

/-- The proof-carrying target cycle produced in the suppressed graph by
minimality.  Retaining it prevents later blocker stages from searching the
suppressed cycle universe again. -/
structure CriticalCycle (LengthOK : Nat → Prop) where
  cycle : CycleWithLength setup.graph LengthOK
  usesChord : s(setup.firstVertex, setup.secondVertex) ∈ cycle.walk.edges

/-- Remove the new chord from a supplied target cycle in the suppressed graph
and return its source-graph predecessor path. -/
theorem pathOfCycleUsingChord (LengthOK : Nat → Prop)
    (cycle : CycleWithLength setup.graph LengthOK)
    (uses : s(setup.firstVertex, setup.secondVertex) ∈ cycle.walk.edges) :
    HasSuppressionPath setup LengthOK := by
  letI : DecidableEq setup.Vertex := setup.suppressedObject.input.vertices.decEq
  obtain ⟨oriented, orientedCycle, sndEq, lengthEq⟩ :=
    orientCycleAtEdge cycle.walk cycle.isCycle uses
  let route := oriented.tail.reverse
  have routePath : route.IsPath := orientedCycle.isPath_tail.reverse
  let route' : setup.graph.Walk setup.firstVertex setup.secondVertex :=
    route.copy rfl sndEq
  have routePath' : route'.IsPath := by
    simpa [route'] using routePath
  have orientedNonNil : ¬oriented.Nil := orientedCycle.not_nil
  have rebuilt :
      (SimpleGraph.Walk.cons (oriented.adj_snd orientedNonNil)
        oriented.tail).IsCycle := by
    rw [oriented.cons_tail_eq orientedNonNil]
    exact orientedCycle
  have tailAvoids : s(setup.firstVertex, setup.secondVertex) ∉
      oriented.tail.edges := by
    have rootAvoids := ((SimpleGraph.Walk.cons_isCycle_iff oriented.tail
      (oriented.adj_snd orientedNonNil)).1 rebuilt).2
    simpa [sndEq] using rootAvoids
  have routeAvoids : s(setup.firstVertex, setup.secondVertex) ∉ route'.edges := by
    simpa [route', route] using tailAvoids
  let oldRoute := setup.toOldWalk route' routeAvoids
  let sourceRoute := setup.toSourceWalk oldRoute
  let finalPath : object.graph.Walk setup.first setup.second :=
    sourceRoute.copy rfl rfl
  refine ⟨{
    path := finalPath
    isPath := ?_
    endpoint_not_mem := ?_
    predecessor_length := ?_
  }⟩
  · apply SimpleGraph.Walk.map_isPath_of_injective
      setup.oldEmbedding.injective
    exact routePath'.transfer _
  · dsimp [finalPath]
    simpa only [SimpleGraph.Walk.support_copy] using
      setup.endpoint_not_mem_toSourceWalk oldRoute
  · dsimp [finalPath]
    rw [SimpleGraph.Walk.length_copy]
    have mappedLength : sourceRoute.length = oldRoute.length := by
      exact SimpleGraph.Walk.length_map _ _
    rw [mappedLength]
    change LengthOK (oldRoute.length + 1)
    have transferredLength : oldRoute.length = route'.length := by
      exact SimpleGraph.Walk.length_transfer _ _
    rw [transferredLength]
    change LengthOK (route'.length + 1)
    have copiedLength : route'.length = route.length := by
      exact SimpleGraph.Walk.length_copy _ _ _
    rw [copiedLength]
    have reverseLength : route.length = oriented.tail.length := by
      exact SimpleGraph.Walk.length_reverse _
    rw [reverseLength]
    rw [oriented.length_tail_add_one orientedNonNil]
    rw [lengthEq]
    exact cycle.length_ok

namespace CriticalCycle

/-- Extract the source-graph predecessor path from the retained critical
cycle.  This is one certificate transformation, not a path search. -/
noncomputable def predecessor (critical : CriticalCycle setup LengthOK) :
    SuppressionPath setup LengthOK :=
  Classical.choice
    (setup.pathOfCycleUsingChord LengthOK critical.cycle critical.usesChord)

end CriticalCycle

/-- A chord-avoiding suppressed cycle maps to a cycle of the same length in
the source graph. -/
theorem sourceCycleOfAvoidingChord (LengthOK : Nat → Prop)
    (cycle : CycleWithLength setup.graph LengthOK)
    (avoids : s(setup.firstVertex, setup.secondVertex) ∉ cycle.walk.edges) :
    HasCycleWithLength object.graph LengthOK := by
  let oldWalk := setup.toOldWalk cycle.walk avoids
  let sourceWalk := setup.toSourceWalk oldWalk
  refine ⟨{
    vertex := cycle.vertex.1
    walk := sourceWalk
    isCycle := (cycle.isCycle.transfer _).map
      setup.oldEmbedding.injective
    length_ok := by
      have mappedLength : sourceWalk.length = oldWalk.length := by
        exact SimpleGraph.Walk.length_map _ _
      rw [mappedLength]
      have transferredLength : oldWalk.length = cycle.walk.length := by
        exact SimpleGraph.Walk.length_transfer _ _
      rw [transferredLength]
      exact cycle.length_ok
  }⟩

/-- Minimality and target avoidance produce one target cycle in the
suppressed graph and prove that it uses the added shoulder chord. -/
theorem criticalCycleFromMinimality
    (input : PackedMinimumDegreeCycle.StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (setup : Setup ctx.G.object)
    (minimumDegree_three : input.minimumDegree = 3) :
    Nonempty (CriticalCycle setup input.LengthOK) := by
  have sourceBaseline : 3 ≤ ctx.G.object.minDegree := by
    have original := ctx.baseline
    change input.minimumDegree ≤ ctx.G.object.minDegree at original
    omega
  have baseline : input.problem.Baseline
      (PackedFiniteObject.pack setup.suppressedObject) :=
    by
      change input.minimumDegree ≤ setup.suppressedObject.minDegree
      rw [minimumDegree_three]
      exact setup.minDegree_three sourceBaseline
  have target : input.Target
      (PackedFiniteObject.pack setup.suppressedObject) :=
    ctx.minimal (PackedFiniteObject.pack setup.suppressedObject)
      setup.packedRank_lt baseline
  obtain ⟨cycle⟩ := target
  by_cases uses : s(setup.firstVertex, setup.secondVertex) ∈ cycle.walk.edges
  · exact ⟨⟨cycle, uses⟩⟩
  · exact (ctx.avoids (setup.sourceCycleOfAvoidingChord
      input.LengthOK cycle uses)).elim

/-- Minimality and target avoidance force the local predecessor path while
the stronger theorem above retains the originating suppression cycle. -/
theorem witnessFromMinimality
    (input : PackedMinimumDegreeCycle.StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (setup : Setup ctx.G.object)
    (minimumDegree_three : input.minimumDegree = 3) :
    HasSuppressionPath setup input.LengthOK := by
  let critical := Classical.choice
    (setup.criticalCycleFromMinimality input ctx minimumDegree_three)
  exact ⟨critical.predecessor⟩

end Setup

end StructuralExhaustion.Graph.OpenPortSuppression
