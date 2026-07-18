import StructuralExhaustion.Graph.FiniteObject
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Lex

namespace StructuralExhaustion.Graph.FiniteLexFirstSimplePath

open StructuralExhaustion

universe u

variable {V : Type u}

/-!
# The first simple path in a supplied finite vertex order

This selector enumerates only simple paths in one supplied finite graph.  It
does not enumerate graphs, contexts, or ambient universes.  A path is compared
by the forward word of vertex positions in the `FiniteObject` enumeration.
-/

/-- Local input for the ordered simple-path selector. -/
structure Profile (object : FiniteObject V) where
  source : V
  target : V
  reachable : object.graph.Reachable source target

namespace Profile

variable {object : FiniteObject V} (profile : Profile object)

/-- The forward declared-order word of a path. -/
def code (path : object.graph.Path profile.source profile.target) : List Nat :=
  path.1.support.map fun vertex => (object.input.vertices.equiv vertex).1

/-- All simple paths between the supplied endpoints.  Mathlib constructs this
finite set from walks of length strictly below the supplied vertex count. -/
noncomputable def paths : Finset (object.graph.Path profile.source profile.target) := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact Finset.univ

theorem paths_nonempty : profile.paths.Nonempty := by
  obtain ⟨walk, isPath⟩ := profile.reachable.exists_isPath
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact ⟨⟨walk, isPath⟩, by simp [paths]⟩

/-- The finite set of forward declared-order path words. -/
noncomputable def codes : Finset (List Nat) :=
  profile.paths.image profile.code

theorem codes_nonempty : profile.codes.Nonempty :=
  profile.paths_nonempty.image _

/-- The lexicographically least forward vertex word among all simple paths. -/
noncomputable def firstCode : List Nat :=
  profile.codes.min' profile.codes_nonempty

theorem firstCode_mem : profile.firstCode ∈ profile.codes :=
  Finset.min'_mem _ _

theorem exists_path_with_firstCode :
    ∃ path ∈ profile.paths, profile.code path = profile.firstCode := by
  simpa [codes] using profile.firstCode_mem

/-- The unique path carrying the least word.  Choosing from the fibre is
harmless: `Walk.support` is injective and the vertex-position map is injective,
so two paths cannot carry the same word. -/
noncomputable def firstPath : object.graph.Path profile.source profile.target :=
  Classical.choose profile.exists_path_with_firstCode

theorem firstPath_mem : profile.firstPath ∈ profile.paths :=
  (Classical.choose_spec profile.exists_path_with_firstCode).1

@[simp]
theorem code_firstPath : profile.code profile.firstPath = profile.firstCode :=
  (Classical.choose_spec profile.exists_path_with_firstCode).2

/-- The selected walk is simple. -/
theorem firstPath_isPath : profile.firstPath.1.IsPath :=
  profile.firstPath.2

/-- The selected path starts at the supplied source. -/
theorem firstPath_head : profile.firstPath.1.support.head? = some profile.source := by
  rw [List.head?_eq_some_iff]
  exact ⟨profile.firstPath.1.support.tail,
    profile.firstPath.1.cons_tail_support.symm⟩

/-- The selected path ends at the supplied target. -/
theorem firstPath_getLast : profile.firstPath.1.support.getLast? = some profile.target := by
  rw [List.getLast?_eq_getLast_of_ne_nil profile.firstPath.1.support_ne_nil,
    profile.firstPath.1.getLast_support]

/-- Every simple endpoint path occurs in the local enumeration. -/
theorem mem_paths (path : object.graph.Path profile.source profile.target) :
    path ∈ profile.paths := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  simp [paths]

/-- The chosen word is no later than the word of any simple endpoint path. -/
theorem firstCode_le (path : object.graph.Path profile.source profile.target) :
    profile.code profile.firstPath ≤ profile.code path := by
  rw [profile.code_firstPath]
  exact Finset.min'_le _ _ (Finset.mem_image.2
    ⟨path, profile.mem_paths path, rfl⟩)

/-- No simple path between the endpoints is lexicographically earlier than
the selected path. -/
theorem no_earlier_path (path : object.graph.Path profile.source profile.target) :
    ¬ profile.code path < profile.code profile.firstPath :=
  not_lt_of_ge (profile.firstCode_le path)

/-- The selected simple path has the standard finite simple-path bound. -/
theorem firstPath_length_lt :
    profile.firstPath.1.length < object.input.vertices.card := by
  letI : FinEnum V := object.input.vertices
  simpa [FinEnum.card_eq_fintypeCard] using profile.firstPath.2.length_lt

end Profile

end StructuralExhaustion.Graph.FiniteLexFirstSimplePath
