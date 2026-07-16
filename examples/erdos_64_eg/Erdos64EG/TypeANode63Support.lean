import Erdos64EG.P13NegativeSupportLocalization
import StructuralExhaustion.Graph.TypeATraceIncidenceCoordinate

namespace Erdos64EG.Internal.TypeANode63Support

open StructuralExhaustion

universe u

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

abbrev Node61
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  TypeBEntryRouting.VerifiedNode61Residual ctx

/-- The literal induced graph on the node-`[61]` support. -/
noncomputable def supportObject (node61 : Node61 ctx) :=
  ctx.G.object.induceFinset node61.support.core

/-- Node `[61]` remainder provenance gives an induced embedding into the exact
maximum-packing remainder; no graph or support family is searched. -/
noncomputable def supportToP13Embedding (node61 : Node61 ctx) :
    (supportObject (ctx := ctx) node61).graph ↪g (p13Remainder ctx).graph where
  toFun vertex :=
    ⟨vertex.1, node61.core_subset_remainder vertex.2⟩
  inj' := by
    intro left right equal
    exact Subtype.ext
      (congrArg (fun vertex : P13RemainderVertex ctx => vertex.1) equal)
  map_rel_iff' := by
    intro left right
    rfl

theorem support_p13Free (node61 : Node61 ctx) :
    Graph.InducedPathFree (supportObject (ctx := ctx) node61).graph 13 := by
  intro realization
  rcases realization with ⟨window⟩
  exact p13Remainder_free ctx
    ⟨(supportToP13Embedding (ctx := ctx) node61).comp window⟩

theorem support_avoidsPowerOfTwoCycle (node61 : Node61 ctx) :
    ¬Graph.HasCycleWithLength (supportObject (ctx := ctx) node61).graph
      (fun length => ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent) := by
  intro supportCycle
  let embedding := ctx.G.object.induceFinsetEmbedding node61.support.core
  have ambientCycle := Graph.hasCycleWithLength_mapHom embedding.toHom
    embedding.injective supportCycle
  exact ctx.avoids
    (target_of_unboundedPowerOfTwoCycle ctx.G.object ambientCycle)

/-- The sole external HSS theorem is applied to the literal node-`[61]`
support, using its proved remainder inclusion and ambient target avoidance. -/
theorem support_internalThreeCore_free (node61 : Node61 ctx) :
    (supportObject (ctx := ctx) node61).InternalMinDegreeFree 3 :=
  Graph.External.HegdeSandeepShashank.internalMinDegreeThree_free_of_p13Free
    (supportObject (ctx := ctx) node61)
    (support_p13Free (ctx := ctx) node61)
    (support_avoidsPowerOfTwoCycle (ctx := ctx) node61)

theorem ambientDegree_eq_three_of_noHigh
    (node61 : Node61 ctx)
    (noHigh : Graph.NegativeSupportHandoff.highCenters ctx.G.object
      node61.support.core = ∅)
    (vertex : ctx.G.Vertex) (member : vertex ∈ node61.support.core) :
    ctx.G.object.degree vertex = 3 := by
  have notHigh : ¬4 ≤ ctx.G.object.degree vertex := by
    intro high
    have highMember : vertex ∈
        Graph.NegativeSupportHandoff.highCenters ctx.G.object
          node61.support.core := by
      letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
      simp [Graph.NegativeSupportHandoff.highCenters, member, high]
    rw [noHigh] at highMember
    simp at highMember
  have lower : 3 ≤ ctx.G.object.degree vertex :=
    ctx.baseline.trans (ctx.G.object.minDegree_le_degree vertex)
  omega

theorem support_degree_le_three_of_noHigh
    (node61 : Node61 ctx)
    (noHigh : Graph.NegativeSupportHandoff.highCenters ctx.G.object
      node61.support.core = ∅)
    (vertex : {value : ctx.G.Vertex // value ∈ node61.support.core}) :
    (supportObject (ctx := ctx) node61).degree vertex ≤ 3 := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableRel ctx.G.object.graph.Adj :=
    ctx.G.object.input.decideAdj
  have imageSubset :
      Subtype.val '' (supportObject (ctx := ctx) node61).graph.neighborSet vertex ⊆
        ctx.G.object.graph.neighborSet vertex.1 := by
    rintro neighbor ⟨subneighbor, adjacent, rfl⟩
    exact adjacent
  have degreeLe : (supportObject (ctx := ctx) node61).degree vertex ≤
      ctx.G.object.degree vertex.1 := by
    rw [(supportObject (ctx := ctx) node61).degree_eq_ncard_neighborSet,
      ctx.G.object.degree_eq_ncard_neighborSet]
    calc
      ((supportObject (ctx := ctx) node61).graph.neighborSet vertex).ncard =
          (Subtype.val ''
            (supportObject (ctx := ctx) node61).graph.neighborSet vertex).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ ≤ (ctx.G.object.graph.neighborSet vertex.1).ncard :=
        Set.ncard_le_ncard imageSubset
  rw [ambientDegree_eq_three_of_noHigh (ctx := ctx) node61 noHigh
    vertex.1 vertex.2]
    at degreeLe
  exact degreeLe

/-- Exact node `[63]` Type A structural profile, constructed only on the
no-high-center branch of the same provenance-carrying node-`[61]` support. -/
noncomputable def profile
    (node61 : Node61 ctx)
    (noHigh : Graph.NegativeSupportHandoff.highCenters ctx.G.object
      node61.support.core = ∅) :
    Graph.TypeACanonicalReceiverTrace.SupportProfile ctx.G.object where
  support := node61.support.core
  connected := node61.support.connected
  ambient_cubic := ambientDegree_eq_three_of_noHigh (ctx := ctx) node61 noHigh
  degree_le_three := support_degree_le_three_of_noHigh (ctx := ctx) node61 noHigh
  coreFree := support_internalThreeCore_free (ctx := ctx) node61

/-- Typed no-high result retaining nodes `[61]` and `[62]` and exposing the
graph-owned Type A profile consumed by the canonical-trace stage. -/
structure VerifiedNode63Residual (node61 : Node61 ctx) where
  highCenters_empty :
    Graph.NegativeSupportHandoff.highCenters ctx.G.object
      node61.support.core = ∅
  typeAProfile :
    Graph.TypeACanonicalReceiverTrace.SupportProfile ctx.G.object
  profile_support : typeAProfile.support = node61.support.core

noncomputable def node63
    (node61 : Node61 ctx)
    (noHigh : Graph.NegativeSupportHandoff.highCenters ctx.G.object
      node61.support.core = ∅) : VerifiedNode63Residual node61 where
  highCenters_empty := noHigh
  typeAProfile := profile (ctx := ctx) node61 noHigh
  profile_support := rfl

/-- Both outputs of the executable node-`[62]` scan consume the identical
node-`[61]` support and predecessor.  The high branch is the existing node
`[64]` Type B handoff; the empty branch is the node-`[63]` Type A profile. -/
inductive VerifiedNode62Routed (node61 : Node61 ctx) where
  | typeB (residual : TypeBEntryRouting.VerifiedNode64Residual ctx)
  | typeA (residual : VerifiedNode63Residual node61)

noncomputable def routeNode62 (node61 : Node61 ctx) :
    VerifiedNode62Routed node61 := by
  cases TypeBEntryRouting.node62 ctx node61 with
  | high witness =>
      exact .typeB
        (TypeBEntryRouting.node64 ctx node61 witness)
  | noHigh empty => exact .typeA (node63 node61 empty)

/-- Execute the complete canonical node-`[61]` localization and immediately
route its exact support through the exhaustive node-`[62]` split. -/
noncomputable def routeCanonicalNode61Node62
    (ledger : P13NegativeSupportLocalization.CanonicalQuarterLedger ctx) :
    VerifiedNode62Routed
      (P13NegativeSupportLocalization.canonicalNode61 ctx ledger) :=
  routeNode62 (P13NegativeSupportLocalization.canonicalNode61 ctx ledger)

/-- The exact finite trace-incidence coordinates available on the Type A
branch.  They are dependent positions of canonical traces and therefore scan
only the selected support and its stored traces. -/
abbrev TraceCoordinate (node61 : Node61 ctx)
    (noHigh : Graph.NegativeSupportHandoff.highCenters ctx.G.object
      node61.support.core = ∅) :=
  Graph.TypeATraceIncidenceCoordinate.Coordinate ctx.G.object
    (profile node61 noHigh)

@[implicit_reducible]
noncomputable def traceCoordinates (node61 : Node61 ctx)
    (noHigh : Graph.NegativeSupportHandoff.highCenters ctx.G.object
      node61.support.core = ∅) :
    FinEnum (TraceCoordinate node61 noHigh) :=
  Graph.TypeATraceIncidenceCoordinate.coordinates ctx.G.object
    (profile node61 noHigh)

theorem traceCoordinate_ambient_degree
    (node61 : Node61 ctx)
    (noHigh : Graph.NegativeSupportHandoff.highCenters ctx.G.object
      node61.support.core = ∅)
    (coordinate : TraceCoordinate node61 noHigh) :
    ctx.G.object.degree
      (coordinate.ambientVertex ctx.G.object (profile node61 noHigh)) = 3 :=
  coordinate.ambientVertex_degree_eq_three ctx.G.object (profile node61 noHigh)

theorem traceCoordinate_nonterminal_internal_degree
    (node61 : Node61 ctx)
    (noHigh : Graph.NegativeSupportHandoff.highCenters ctx.G.object
      node61.support.core = ∅)
    (coordinate : TraceCoordinate node61 noHigh)
    (notTerminal : ¬coordinate.IsTerminal ctx.G.object
      (profile node61 noHigh)) :
    coordinate.internalDegree ctx.G.object (profile node61 noHigh) = 3 :=
  coordinate.internalDegree_eq_three_of_not_terminal ctx.G.object
    (profile node61 noHigh) notTerminal

theorem traceCoordinate_terminal_internal_degree
    (node61 : Node61 ctx)
    (noHigh : Graph.NegativeSupportHandoff.highCenters ctx.G.object
      node61.support.core = ∅)
    (coordinate : TraceCoordinate node61 noHigh)
    (terminal : coordinate.IsTerminal ctx.G.object (profile node61 noHigh)) :
    coordinate.internalDegree ctx.G.object (profile node61 noHigh) ≤ 2 :=
  coordinate.internalDegree_le_two_of_terminal ctx.G.object
    (profile node61 noHigh) terminal

end Erdos64EG.Internal.TypeANode63Support
