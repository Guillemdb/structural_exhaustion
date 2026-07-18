import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic
import StructuralExhaustion.Graph.InducedPath

namespace StructuralExhaustion.Graph.InducedPathDiameter

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem not_adj_getVert_of_gap {start finish : V}
    (path : G.Walk start finish)
    (shortest : path.length = G.dist start finish)
    {first second : Nat} (gap : first + 1 < second)
    (secondBound : second ≤ path.length) :
    ¬G.Adj (path.getVert first) (path.getVert second) := by
  intro adjacent
  let shortcut := (path.take first).concat adjacent |>.append (path.drop second)
  have distanceLe : G.dist start finish ≤ shortcut.length := by
    exact SimpleGraph.dist_le shortcut
  have firstBound : first ≤ path.length := by omega
  simp [shortcut, firstBound, secondBound] at distanceLe
  omega

/-- A shortest path of length at least twelve contains the induced first
thirteen vertices required by the manuscript. -/
theorem hasInducedPath_thirteen_of_shortest_length_ge_twelve
    {start finish : V} (path : G.Walk start finish)
    (isPath : path.IsPath)
    (shortest : path.length = G.dist start finish)
    (long : 12 ≤ path.length) : Graph.HasInducedPath G 13 := by
  let vertex : Fin 13 → V := fun index => path.getVert index.val
  have bound (index : Fin 13) : index.val ≤ path.length := by
    omega
  have injective : Function.Injective vertex := by
    intro left right equal
    apply Fin.ext
    have supportNodup := isPath.support_nodup
    have leftBound := bound left
    have rightBound := bound right
    have indexEqual : left.val = right.val := by
      apply supportNodup.getElem_inj_iff.mp
      simpa [vertex, SimpleGraph.Walk.getVert_eq_support_getElem,
        leftBound, rightBound] using equal
    exact indexEqual
  refine ⟨{
    toFun := vertex
    inj' := injective
    map_rel_iff' := ?_
  }⟩
  intro left right
  constructor
  · intro adjacent
    have distinct : left.val ≠ right.val := by
      intro equal
      exact adjacent.ne (by simpa [vertex, equal])
    have noForwardGap : ¬left.val + 1 < right.val := by
      intro gap
      exact not_adj_getVert_of_gap path shortest gap (bound right) adjacent
    have noBackwardGap : ¬right.val + 1 < left.val := by
      intro gap
      exact not_adj_getVert_of_gap path shortest gap (bound left) adjacent.symm
    simp only [SimpleGraph.pathGraph_adj]
    omega
  · intro adjacent
    simp only [SimpleGraph.pathGraph_adj] at adjacent
    rcases adjacent with step | step
    · simpa [vertex, step] using
        path.adj_getVert_succ (i := left.val) (by omega)
    · simpa [vertex, step] using
        (path.adj_getVert_succ (i := right.val) (by omega)).symm

/-- In a connected induced-`P13`-free graph, every pair has a shortest simple
path of length at most eleven. -/
theorem diameterAtMostEleven_of_p13Free
    (preconnected : G.Preconnected) (free : Graph.InducedPathFree G 13)
    (left right : V) :
    ∃ path : G.Walk left right, path.IsPath ∧ path.length ≤ 11 := by
  obtain ⟨path, isPath, shortest⟩ :=
    (preconnected left right).exists_path_of_dist
  refine ⟨path, isPath, ?_⟩
  by_contra notLe
  have long : 12 ≤ path.length := by omega
  exact free
    (hasInducedPath_thirteen_of_shortest_length_ge_twelve
      path isPath shortest long)

end StructuralExhaustion.Graph.InducedPathDiameter
