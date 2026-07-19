import Erdos64EG.TypeANode63Support
import StructuralExhaustion.Core.ExactHandoff
import StructuralExhaustion.Graph.InducedPathDiameter
import StructuralExhaustion.Graph.SubcubicMooreBound

namespace Erdos64EG.Internal.TypeANodes86To88Thresholds

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

abbrev Node61 := TypeANode63Support.Node61 ctx
abbrev Node63 (node61 : Node61 (ctx := ctx)) :=
  TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61

/-- Exact original node `[86]` Type-A residual.  It retains the literal
negative support selected at node `[61]` and the no-high-center Type-A profile
produced at node `[63]`. -/
structure VerifiedNode86Residual
    (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61)
    extends Core.ExactHandoff node63 where
  highCenters_empty :
    Graph.NegativeSupportHandoff.highCenters ctx.G.object
      node61.support.core = ∅
  negativeNetQuarter :
    (Graph.NegativeSupportHandoff.chargeProfile ctx.G.object
      node61.support.core).netQuarterCharge < 0
  profile_support : previous.typeAProfile.support = node61.support.core

/-- Node `[86]` is a projection of the already verified node `[61]` negative
support and node `[63]` no-high branch; it performs no new search. -/
def node86 {node61 : Node61 (ctx := ctx)} (node63 : Node63 node61) :
    VerifiedNode86Residual node61 node63 where
  previous := node63
  previousExact := rfl
  highCenters_empty := node63.highCenters_empty
  negativeNetQuarter := node61.support.negative
  profile_support := node63.profile_support

namespace VerifiedNode86Residual

variable {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}

/-- `sigma(X)=0` in the manuscript's exact assigned-surplus ledger. -/
theorem assignedSurplus_eq_zero
    (node86 : VerifiedNode86Residual node61 node63) :
    (Graph.NegativeSupportHandoff.chargeProfile ctx.G.object
      node61.support.core).assignedSurplus = 0 := by
  unfold Graph.NegativeSupportHandoff.chargeProfile
  simp [node86.highCenters_empty,
    Graph.AssignedSupportCharge.Profile.assignedSurplus]

/-- Quarter-unit form of the node `[86]` conclusion
`def^+(X) < |X|/4`. -/
theorem four_deficiency_lt_card
    (node86 : VerifiedNode86Residual node61 node63) :
    4 * (Graph.NegativeSupportHandoff.chargeProfile ctx.G.object
      node61.support.core).positiveDeficiency < node61.support.core.card := by
  have negative := node86.negativeNetQuarter
  have surplus := node86.assignedSurplus_eq_zero
  unfold Graph.AssignedSupportCharge.Profile.netQuarterCharge at negative
  rw [surplus] at negative
  norm_num at negative
  have integerBound :
      (4 * ((Graph.NegativeSupportHandoff.chargeProfile ctx.G.object
        node61.support.core).positiveDeficiency : Int)) <
        (node61.support.core.card : Int) := by
    simpa [Graph.NegativeSupportHandoff.chargeProfile] using negative
  exact_mod_cast integerBound

end VerifiedNode86Residual

/-- Complete proof-carrying contract of original node `[87]`.  The last two
fields are deliberately explicit: they are precisely the unimplemented Moore
bound consequences and may not be inferred from node `[63]` by a later cell. -/
structure VerifiedNode87Residual
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    (node86 : VerifiedNode86Residual node61 node63)
    extends Core.ExactHandoff node86 where
  p13Free : Graph.InducedPathFree
    (TypeANode63Support.supportObject (ctx := ctx) node61).graph 13
  diameterAtMostEleven :
    ∀ left right : {vertex // vertex ∈ node61.support.core},
      ∃ path : (TypeANode63Support.supportObject (ctx := ctx) node61).graph.Walk
          left right,
        path.IsPath ∧ path.length ≤ 11
  supportCardAtMost6142 : node61.support.core.card ≤ 6142

/-- The dependency-ready portion of node `[87]`: exact predecessor and
`P13`-freeness on the identical induced support.  Its diameter and Moore-card
fields remain the audited producer obligations. -/
theorem node87_p13Free
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    (node86 : VerifiedNode86Residual node61 node63) :
    Graph.InducedPathFree
      (TypeANode63Support.supportObject (ctx := ctx) node61).graph 13 :=
  TypeANode63Support.support_p13Free (ctx := ctx) node61

/-- The manuscript's exact local Moore calculation, once its preceding
diameter-eleven conclusion has been established on the identical support. -/
theorem node87_supportCardAtMost6142_of_diameter
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    (node86 : VerifiedNode86Residual node61 node63)
    (diameterAtMostEleven :
      ∀ left right : {vertex // vertex ∈ node61.support.core},
        ∃ path : (TypeANode63Support.supportObject (ctx := ctx) node61).graph.Walk
            left right,
          path.IsPath ∧ path.length ≤ 11) :
    node61.support.core.card ≤ 6142 := by
  let object := TypeANode63Support.supportObject (ctx := ctx) node61
  let typeA := TypeANode63Support.profile (ctx := ctx) node61
    node86.highCenters_empty
  let root : {vertex // vertex ∈ node61.support.core} :=
    ⟨node61.support.core_nonempty.choose,
      node61.support.core_nonempty.choose_spec⟩
  let bfs : Graph.OrderedBFSTree.Profile object := { root := root }
  have degreeLe : ∀ vertex, object.degree vertex ≤ 3 :=
    typeA.degree_le_three
  have radius : ∀ vertex : {vertex // vertex ∈ node61.support.core},
      ∃ path : object.graph.Walk bfs.root vertex,
        path.IsPath ∧ path.length ≤ 11 := fun vertex =>
    diameterAtMostEleven root vertex
  have bound := bfs.card_vertices_le_6142_of_radius_eleven
    (typeA.preconnected ctx.G.object) degreeLe radius
  simpa [object, FinEnum.card_eq_fintypeCard] using bound

/-- The paper's shortest-path argument: a shortest path of length at least
twelve would expose an induced path on its first thirteen vertices. -/
theorem node87_diameterAtMostEleven
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    (node86 : VerifiedNode86Residual node61 node63) :
    ∀ left right : {vertex // vertex ∈ node61.support.core},
      ∃ path : (TypeANode63Support.supportObject (ctx := ctx) node61).graph.Walk
          left right,
        path.IsPath ∧ path.length ≤ 11 := by
  intro left right
  let typeA := TypeANode63Support.profile (ctx := ctx) node61
    node86.highCenters_empty
  exact Graph.InducedPathDiameter.diameterAtMostEleven_of_p13Free
    (typeA.preconnected ctx.G.object)
    (node87_p13Free (ctx := ctx) node86) left right

/-- Total exact producer for original node `[87]`. -/
noncomputable def node87
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    (node86 : VerifiedNode86Residual node61 node63) :
    VerifiedNode87Residual node86 where
  previous := node86
  previousExact := rfl
  p13Free := node87_p13Free (ctx := ctx) node86
  diameterAtMostEleven := node87_diameterAtMostEleven (ctx := ctx) node86
  supportCardAtMost6142 :=
    node87_supportCardAtMost6142_of_diameter (ctx := ctx) node86
      (node87_diameterAtMostEleven (ctx := ctx) node86)

/-- Primitive local-work envelope for node `[87]`: twelve BFS layer scans of
the support adjacency table, plus the constant thirteen-position induced-path
certificate. -/
noncomputable def node87Checks
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    (_node86 : VerifiedNode86Residual node61 node63) : Nat :=
  12 * node61.support.core.card ^ 2 + 13

theorem node87Checks_polynomial
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    (node86 : VerifiedNode86Residual node61 node63) :
    node87Checks node86 ≤ 13 * (ctx.G.object.input.vertices.card + 1) ^ 2 := by
  have supportLe : node61.support.core.card ≤
      ctx.G.object.input.vertices.card := by
    rw [← ctx.G.object.card_vertexFinset]
    exact Finset.card_le_card fun vertex _ => ctx.G.object.mem_vertexFinset vertex
  unfold node87Checks
  nlinarith

abbrev SupportVertex {node61 : Node61 (ctx := ctx)} :=
  {vertex // vertex ∈ node61.support.core}

/-- Missing-port count `q(w)=3-d_X(w)` from the original node `[88]`. -/
noncomputable def q {node61 : Node61 (ctx := ctx)}
    (vertex : SupportVertex (ctx := ctx) (node61 := node61)) : Nat :=
  3 - (TypeANode63Support.supportObject (ctx := ctx) node61).degree vertex

/-- The first saturated load at a receiver: `H(w)=4q(w)`. -/
noncomputable def threshold {node61 : Node61 (ctx := ctx)}
    (vertex : SupportVertex (ctx := ctx) (node61 := node61)) : Nat :=
  4 * q (ctx := ctx) vertex

/-- Exact original node `[88]` residual, indexed by the complete immediate
node-`[87]` predecessor. -/
structure VerifiedNode88Residual
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : VerifiedNode86Residual node61 node63}
    (node87 : VerifiedNode87Residual node86)
    extends Core.ExactHandoff node87 where
  classThreshold : ∀ (j : Fin 3)
      (receiver : SupportVertex (ctx := ctx) (node61 := node61)),
    (TypeANode63Support.supportObject (ctx := ctx) node61).degree receiver =
        2 - j.val →
      threshold (ctx := ctx) receiver = 4 * (j.val + 1)
  H0_le_four : 4 * (0 + 1) ≤ 4
  H1_le_eight : 4 * (1 + 1) ≤ 8
  H2_le_twelve : 4 * (2 + 1) ≤ 12

/-- Node `[88]` is only the paper's local integer threshold algebra; it scans
no graph family and introduces no outcome beyond the edge to `[89]`. -/
noncomputable def node88
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : VerifiedNode86Residual node61 node63}
    (node87 : VerifiedNode87Residual node86) : VerifiedNode88Residual node87 where
  previous := node87
  previousExact := rfl
  classThreshold := by
    intro j receiver degree
    unfold threshold q
    rw [degree]
    omega
  H0_le_four := by norm_num
  H1_le_eight := by norm_num
  H2_le_twelve := by norm_num

/-- Constant arithmetic work after the exact support degrees have already
been retained by node `[87]`. -/
def node88Checks : Nat := 3

theorem node88Checks_constant : node88Checks ≤ 3 := le_rfl

end Erdos64EG.Internal.TypeANodes86To88Thresholds
