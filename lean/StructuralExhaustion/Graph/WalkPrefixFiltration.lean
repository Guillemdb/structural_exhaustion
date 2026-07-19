import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Graph.FiniteObject
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

namespace StructuralExhaustion.Graph.WalkPrefixFiltration

open StructuralExhaustion

universe u

variable {V : Type u} {G : SimpleGraph V} {start finish : V}

/-!
# Ordered initial-prefix filtration of one proof-carrying path

The stage type is exactly the finite set of positions in the supplied walk's
support.  A stage at position `i` retains `support.take (i+1)`.  The profile
does not select or enumerate walks; it only exposes prefixes of one path
already produced by a graph construction.
-/

structure Profile (path : G.Walk start finish) where
  isPath : path.IsPath

namespace Profile

variable {path : G.Walk start finish} (profile : Profile path)

abbrev Stage (_profile : Profile path) := Fin path.support.length

@[implicit_reducible] noncomputable def stageEnumeration :
    FinEnum profile.Stage := FinEnum.fin

noncomputable def stages : Core.OrderedCollection profile.Stage :=
  { values := List.finRange path.support.length
    nodup := List.nodup_finRange _
    decEq := inferInstance }

/-- The canonical stage schedule is the increasing `Fin` order. -/
theorem stages_values_eq_finRange :
    profile.stages.values = List.finRange path.support.length := rfl

/-- Canonical schedule of nonzero prefix positions.  The graph profile owns
the tail operation so applications never rewrite `drop` through a deeply
dependent path package. -/
noncomputable def positiveStages : Core.OrderedCollection profile.Stage where
  values := profile.stages.values.drop 1
  nodup := profile.stages.nodup.sublist (List.drop_sublist 1 _)
  decEq := profile.stages.decEq

theorem positiveStages_values_eq_finRange_drop :
    profile.positiveStages.values =
      (List.finRange path.support.length).drop 1 :=
  rfl

theorem positiveStages_mem_positive {stage : profile.Stage}
    (member : stage ∈ profile.positiveStages.values) : 0 < stage.val := by
  change stage ∈ (List.finRange path.support.length).drop 1 at member
  obtain ⟨index, inBounds, valueEq⟩ := List.mem_drop_iff_getElem.mp member
  have valEq := congrArg Fin.val valueEq
  rw [List.getElem_finRange] at valEq
  simp only [Fin.val_cast] at valEq
  omega

theorem positiveStages_getElem_val (index : Nat)
    (inBounds : index < profile.positiveStages.values.length) :
    profile.positiveStages.values[index].val = index + 1 := by
  change index < ((List.finRange path.support.length).drop 1).length at inBounds
  change ((List.finRange path.support.length).drop 1)[index].val = index + 1
  exact Core.Enumeration.finRange_drop_one_getElem_val _ index inBounds

theorem positiveStages_pairwise_val_lt :
    profile.positiveStages.values.Pairwise
      (fun earlier later => earlier.val < later.val) := by
  rw [List.pairwise_iff_getElem]
  intro first second firstBound secondBound ordered
  rw [profile.positiveStages_getElem_val first firstBound,
    profile.positiveStages_getElem_val second secondBound]
  omega

/-- Literal initial support through the indexed path vertex. -/
def prefixSupport (stage : profile.Stage) : List V :=
  path.support.take (stage.val + 1)

/-- Literal initial subwalk ending at the indexed support vertex. -/
def prefixWalk (stage : profile.Stage) :
    G.Walk start (path.getVert stage.val) :=
  path.take stage.val

theorem prefixWalk_isPath (stage : profile.Stage) :
    (profile.prefixWalk stage).IsPath :=
  profile.isPath.take stage.val

theorem prefixWalk_support (stage : profile.Stage) :
    (profile.prefixWalk stage).support = profile.prefixSupport stage := by
  exact path.support_take stage.val

theorem prefixWalk_length (stage : profile.Stage) :
    (profile.prefixWalk stage).length = stage.val := by
  rw [prefixWalk, SimpleGraph.Walk.take_length, Nat.min_eq_left]
  simpa [SimpleGraph.Walk.length_support] using stage.isLt

theorem stages_nodup : profile.stages.values.Nodup :=
  profile.stages.nodup

theorem stages_length : profile.stages.values.length = path.support.length := by
  simp [stages]

theorem prefixSupport_length (stage : profile.Stage) :
    (profile.prefixSupport stage).length = stage.val + 1 := by
  rw [prefixSupport, List.length_take, Nat.min_eq_left]
  omega

theorem prefixSupport_nonempty (stage : profile.Stage) :
    profile.prefixSupport stage ≠ [] := by
  intro empty
  have zero : (profile.prefixSupport stage).length = 0 := by simp [empty]
  rw [profile.prefixSupport_length] at zero
  omega

theorem prefixSupport_nodup (stage : profile.Stage) :
    (profile.prefixSupport stage).Nodup :=
  profile.isPath.support_nodup.take

theorem prefixSupport_subset_path (stage : profile.Stage) :
    profile.prefixSupport stage ⊆ path.support :=
  List.take_subset _ _

/-- Prefix supports are monotone in the inherited path-position order. -/
theorem prefixSupport_prefix {earlier later : profile.Stage}
    (ordered : earlier.val ≤ later.val) :
    profile.prefixSupport earlier <+: profile.prefixSupport later := by
  exact List.take_isPrefix_take.mpr (Or.inl (by omega))

theorem prefixSupport_subset {earlier later : profile.Stage}
    (ordered : earlier.val ≤ later.val) :
    profile.prefixSupport earlier ⊆ profile.prefixSupport later :=
  (profile.prefixSupport_prefix ordered).subset

/-- One constant-time prefix descriptor per stored support position. -/
def checks (_profile : Profile path) : Nat := path.support.length

theorem checks_eq_stages_length :
    profile.checks = profile.stages.values.length := by
  rw [profile.stages_length]
  rfl

/-- A simple path has at most one stage per host vertex. -/
theorem checks_le_vertices (vertices : FinEnum V) :
    profile.checks ≤ vertices.card := by
  letI : FinEnum V := vertices
  simpa [checks, FinEnum.card_eq_fintypeCard] using
    (profile.isPath.support_nodup).length_le_card

end Profile

end StructuralExhaustion.Graph.WalkPrefixFiltration
