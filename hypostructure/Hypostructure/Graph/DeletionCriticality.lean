import Hypostructure.Graph.Minimality

/-!
# Edge-deletion criticality

This module packages the graph-generic argument that an edge-minimal object
with minimum degree at least `k` cannot contain an edge whose two endpoints
both have one unit of degree slack.  The exact one-edge degree accounting,
baseline preservation, pointwise contradiction, and focused ledger extension
are all owned by Graph.

The abstract profile supports baselines with additional graph properties.  Its
concrete minimum-degree specialization requires only the threshold `k`; a
caller never supplies the endpoint conclusion or the one-edge accounting.
-/

namespace Hypostructure.Graph

open Finset

universe u v uPrevious

namespace FiniteObject

/-- The certified undirected edge underlying a Mathlib dart. -/
def edgeOfDart (object : FiniteObject.{u})
    (dart : object.graph.Dart) : object.graph.edgeSet :=
  ⟨dart.edge, dart.edge_mem⟩

@[simp]
theorem edgeOfDart_value (object : FiniteObject.{u})
    (dart : object.graph.Dart) :
    (object.edgeOfDart dart).1 = dart.edge :=
  rfl

end FiniteObject

private theorem mk_fst_eq_edge_iff {V : Type u} {G : SimpleGraph V}
    (dart : G.Dart) (vertex : V) :
    s(dart.fst, vertex) = dart.edge ↔ vertex = dart.snd := by
  rw [eq_comm, SimpleGraph.dart_edge_eq_mk'_iff']
  simp [eq_comm]

private theorem mk_snd_eq_edge_iff {V : Type u} {G : SimpleGraph V}
    (dart : G.Dart) (vertex : V) :
    s(dart.snd, vertex) = dart.edge ↔ vertex = dart.fst := by
  rw [eq_comm, SimpleGraph.dart_edge_eq_mk'_iff']
  simp [eq_comm]

private theorem mk_ne_edge_of_ne {V : Type u} {G : SimpleGraph V}
    (dart : G.Dart) {vertex other : V}
    (notFst : vertex ≠ dart.fst) (notSnd : vertex ≠ dart.snd) :
    s(vertex, other) ≠ dart.edge := by
  intro equal
  rw [eq_comm, SimpleGraph.dart_edge_eq_mk'_iff'] at equal
  rcases equal with equal | equal
  · exact notFst equal.1.symm
  · exact notSnd equal.2.symm

private theorem neighborFinset_deleteEdge_fst
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (dart : G.Dart) :
    (G.deleteEdges {dart.edge}).neighborFinset dart.fst =
      (G.neighborFinset dart.fst).erase dart.snd := by
  ext vertex
  simp [SimpleGraph.deleteEdges_adj, mk_fst_eq_edge_iff, and_comm]

private theorem neighborFinset_deleteEdge_snd
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (dart : G.Dart) :
    (G.deleteEdges {dart.edge}).neighborFinset dart.snd =
      (G.neighborFinset dart.snd).erase dart.fst := by
  ext vertex
  simp [SimpleGraph.deleteEdges_adj, mk_snd_eq_edge_iff, and_comm]

private theorem neighborFinset_deleteEdge_other
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (dart : G.Dart) (vertex : V)
    (notFst : vertex ≠ dart.fst) (notSnd : vertex ≠ dart.snd) :
    (G.deleteEdges {dart.edge}).neighborFinset vertex =
      G.neighborFinset vertex := by
  ext other
  simp [SimpleGraph.deleteEdges_adj,
    mk_ne_edge_of_ne dart notFst notSnd]

private theorem degree_deleteEdge_fst_add_one
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (dart : G.Dart) :
    (G.deleteEdges {dart.edge}).degree dart.fst + 1 =
      G.degree dart.fst := by
  change #((G.deleteEdges {dart.edge}).neighborFinset dart.fst) + 1 =
    #(G.neighborFinset dart.fst)
  rw [neighborFinset_deleteEdge_fst]
  exact Finset.card_erase_add_one
    ((G.mem_neighborFinset dart.fst dart.snd).2 dart.adj)

private theorem degree_deleteEdge_snd_add_one
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (dart : G.Dart) :
    (G.deleteEdges {dart.edge}).degree dart.snd + 1 =
      G.degree dart.snd := by
  change #((G.deleteEdges {dart.edge}).neighborFinset dart.snd) + 1 =
    #(G.neighborFinset dart.snd)
  rw [neighborFinset_deleteEdge_snd]
  exact Finset.card_erase_add_one
    ((G.mem_neighborFinset dart.snd dart.fst).2 dart.adj.symm)

private theorem degree_deleteEdge_other
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (dart : G.Dart) (vertex : V)
    (notFst : vertex ≠ dart.fst) (notSnd : vertex ≠ dart.snd) :
    (G.deleteEdges {dart.edge}).degree vertex = G.degree vertex := by
  change #((G.deleteEdges {dart.edge}).neighborFinset vertex) =
    #(G.neighborFinset vertex)
  rw [neighborFinset_deleteEdge_other dart vertex notFst notSnd]

private theorem deleteEdge_preserves_minDegree_aux
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    (dart : G.Dart) (bound : Nat)
    (baseline : bound ≤ G.minDegree)
    (fstSlack : bound + 1 ≤ G.degree dart.fst)
    (sndSlack : bound + 1 ≤ G.degree dart.snd) :
    bound ≤ (G.deleteEdges {dart.edge}).minDegree := by
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro vertex
  by_cases isFst : vertex = dart.fst
  · subst vertex
    have drop := degree_deleteEdge_fst_add_one dart
    omega
  · by_cases isSnd : vertex = dart.snd
    · subst vertex
      have drop := degree_deleteEdge_snd_add_one dart
      omega
    · rw [degree_deleteEdge_other dart vertex isFst isSnd]
      exact baseline.trans (G.minDegree_le_degree vertex)

namespace FiniteObject

/-- Deleting an actual edge lowers its first endpoint degree by exactly one. -/
theorem degree_deleteEdge_fst_add_one (object : FiniteObject.{u})
    (dart : object.graph.Dart) :
    (object.deleteEdge (object.edgeOfDart dart)).degree dart.fst + 1 =
      object.degree dart.fst := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  change (object.graph.deleteEdges {dart.edge}).degree dart.fst + 1 =
    object.graph.degree dart.fst
  exact _root_.Hypostructure.Graph.degree_deleteEdge_fst_add_one dart

/-- Deleting an actual edge lowers its second endpoint degree by exactly one. -/
theorem degree_deleteEdge_snd_add_one (object : FiniteObject.{u})
    (dart : object.graph.Dart) :
    (object.deleteEdge (object.edgeOfDart dart)).degree dart.snd + 1 =
      object.degree dart.snd := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  change (object.graph.deleteEdges {dart.edge}).degree dart.snd + 1 =
    object.graph.degree dart.snd
  exact _root_.Hypostructure.Graph.degree_deleteEdge_snd_add_one dart

/-- Every non-endpoint degree is unchanged by one-edge deletion. -/
theorem degree_deleteEdge_other (object : FiniteObject.{u})
    (dart : object.graph.Dart) (vertex : object.Vertex)
    (notFst : vertex ≠ dart.fst) (notSnd : vertex ≠ dart.snd) :
    (object.deleteEdge (object.edgeOfDart dart)).degree vertex =
      object.degree vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  change (object.graph.deleteEdges {dart.edge}).degree vertex =
    object.graph.degree vertex
  exact _root_.Hypostructure.Graph.degree_deleteEdge_other
    dart vertex notFst notSnd

/-- Endpoint slack is sufficient to preserve a minimum-degree lower bound
under deletion of the dart's undirected edge. -/
theorem deleteEdge_preserves_minDegree (object : FiniteObject.{u})
    (dart : object.graph.Dart) (bound : Nat)
    (baseline : bound ≤ object.minDegree)
    (fstSlack : bound + 1 ≤ object.degree dart.fst)
    (sndSlack : bound + 1 ≤ object.degree dart.snd) :
    bound ≤ (object.deleteEdge (object.edgeOfDart dart)).minDegree := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : Nonempty object.Vertex := ⟨dart.fst⟩
  change bound ≤ (object.graph.deleteEdges {dart.edge}).minDegree
  exact deleteEdge_preserves_minDegree_aux dart bound baseline
    fstSlack sndSlack

end FiniteObject

/-- Graph-specific inputs needed to turn no-proper-baseline minimality into
pointwise edge-deletion criticality.  The fields describe only the baseline;
they do not allow a caller to provide the endpoint conclusion. -/
structure DeletionCriticalityProfile
    (Baseline : FiniteObject.{u} → Prop) where
  threshold : Nat
  degreeLowerBound : ∀ {object : FiniteObject.{u}},
    Baseline object → threshold ≤ object.minDegree
  deleteEdgePreserves : ∀ {object : FiniteObject.{u}}
    (dart : object.graph.Dart),
    Baseline object →
    threshold + 1 ≤ object.degree dart.fst →
    threshold + 1 ≤ object.degree dart.snd →
    Baseline (object.deleteEdge (object.edgeOfDart dart))

/-- The canonical graph baseline at minimum-degree threshold `k`. -/
def MinimumDegreeAtLeast (k : Nat) (object : FiniteObject.{u}) : Prop :=
  k ≤ object.minDegree

/-- Fully graph-owned profile for the pure minimum-degree baseline. -/
def minimumDegreeDeletionCriticalityProfile (k : Nat) :
    DeletionCriticalityProfile (MinimumDegreeAtLeast k) where
  threshold := k
  degreeLowerBound := fun baseline => baseline
  deleteEdgePreserves := by
    intro object dart baseline fstSlack sndSlack
    exact object.deleteEdge_preserves_minDegree dart k baseline
      fstSlack sndSlack

/-- The new graph fact generated by deletion criticality. -/
structure DeletionCriticalityCertificate
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) : Prop where
  private mk ::
  tightEndpoint : ∀ dart : ctx.G.graph.Dart,
    ctx.G.degree dart.fst = profile.threshold ∨
      ctx.G.degree dart.snd = profile.threshold

namespace DeletionCriticalityCertificate

/-- Vertices with one unit of slack above the threshold form an independent
set, as a direct consequence of the generated endpoint certificate. -/
theorem slackVerticesIndependent
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)}
    (certificate : DeletionCriticalityCertificate profile ctx)
    {left right : ctx.G.Vertex}
    (leftSlack : profile.threshold + 1 ≤ ctx.G.degree left)
    (rightSlack : profile.threshold + 1 ≤ ctx.G.degree right) :
    Not (ctx.G.graph.Adj left right) := by
  intro adjacent
  have endpoint := certificate.tightEndpoint ⟨(left, right), adjacent⟩
  change ctx.G.degree left = profile.threshold ∨
    ctx.G.degree right = profile.threshold at endpoint
  rcases endpoint with leftTight | rightTight <;> omega

end DeletionCriticalityCertificate

/-- Derive pointwise deletion criticality from the inherited no-proper-baseline
certificate.  The proof never enumerates edges: an arbitrary Mathlib dart is
deleted and contradicted directly. -/
def deriveDeletionCriticality
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState))
    (noProper : NoProperBaselineCertificate ctx) :
    DeletionCriticalityCertificate profile ctx where
  tightEndpoint := by
    intro dart
    have fstLower : profile.threshold ≤ ctx.G.degree dart.fst :=
      (profile.degreeLowerBound ctx.baseline).trans
        (ctx.G.minDegree_le_degree dart.fst)
    have sndLower : profile.threshold ≤ ctx.G.degree dart.snd :=
      (profile.degreeLowerBound ctx.baseline).trans
        (ctx.G.minDegree_le_degree dart.snd)
    by_contra notTight
    have fstNe : ctx.G.degree dart.fst ≠ profile.threshold :=
      fun equal => notTight (Or.inl equal)
    have sndNe : ctx.G.degree dart.snd ≠ profile.threshold :=
      fun equal => notTight (Or.inr equal)
    have fstSlack : profile.threshold + 1 ≤ ctx.G.degree dart.fst := by
      omega
    have sndSlack : profile.threshold + 1 ≤ ctx.G.degree dart.snd := by
      omega
    exact (noProper.excludes
      (ProperSubgraph.deleteEdge ctx.G (ctx.G.edgeOfDart dart)))
      (profile.deleteEdgePreserves dart ctx.baseline fstSlack sndSlack)

/-! ## Focused accumulated execution -/

/-- Graph-owned output produced on one active accumulated branch. -/
abbrev FocusedDeletionCriticalityOutput
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (previous : Previous) (active : focus.Active previous) :=
  DeletionCriticalityCertificate profile (context.read previous active)

/-- Exact accumulated successor emitted by Graph's focused executor. -/
abbrev FocusedDeletionCriticalityStage
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :=
  Core.Residual.Focus.Stage focus
    (FocusedDeletionCriticalityOutput focus profile context)

/-- Execute deletion criticality on the active branch.  Both inherited inputs
are read through framework queries, and `Focus.run` owns the decision and
single ledger extension. -/
def executeFocusedDeletionCriticality
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (noProper : Core.Residual.Focus.ActiveQuery focus
      (fun previous active =>
        NoProperBaselineCertificate (context.read previous active)))
    (previous : Previous) :
    FocusedDeletionCriticalityStage focus profile context :=
  Core.Residual.Focus.run focus previous fun active =>
    deriveDeletionCriticality profile (context.read previous active)
      (noProper.read previous active)

/-- The active branch inherited after deletion criticality. -/
abbrev FocusedDeletionCriticalityProfile
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :=
  Core.Residual.Focus.successor focus
    (FocusedDeletionCriticalityOutput focus profile context)

/-- Query the exact certificate generated by the newest Graph extension. -/
def focusedDeletionCriticalityQuery
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :
    Core.Residual.Focus.ActiveQuery
      (FocusedDeletionCriticalityProfile focus profile context)
      (fun stage active =>
        FocusedDeletionCriticalityOutput focus profile context
          stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

/-! ## Pure minimum-degree convenience surface -/

/-- Exact focused successor for the canonical baseline `k ≤ minDegree`. -/
abbrev FocusedMinimumDegreeDeletionCriticalityStage
    {Previous : Type uPrevious} (k : Nat)
    (focus : Core.Residual.Focus.Profile Previous)
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem (MinimumDegreeAtLeast k) BranchState) Target
          (lexicographicProgress (MinimumDegreeAtLeast k) BranchState))) :=
  FocusedDeletionCriticalityStage focus
    (minimumDegreeDeletionCriticalityProfile k) context

/-- Execute the pure minimum-degree specialization from only `k`, inherited
queries, and the literal predecessor. -/
def executeFocusedMinimumDegreeDeletionCriticality
    {Previous : Type uPrevious} (k : Nat)
    (focus : Core.Residual.Focus.Profile Previous)
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem (MinimumDegreeAtLeast k) BranchState) Target
          (lexicographicProgress (MinimumDegreeAtLeast k) BranchState)))
    (noProper : Core.Residual.Focus.ActiveQuery focus
      (fun previous active =>
        NoProperBaselineCertificate (context.read previous active)))
    (previous : Previous) :
    FocusedMinimumDegreeDeletionCriticalityStage k focus context :=
  executeFocusedDeletionCriticality focus
    (minimumDegreeDeletionCriticalityProfile k) context noProper previous

/-- Active branch inherited after the pure minimum-degree executor. -/
abbrev FocusedMinimumDegreeDeletionCriticalityProfile
    {Previous : Type uPrevious} (k : Nat)
    (focus : Core.Residual.Focus.Profile Previous)
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem (MinimumDegreeAtLeast k) BranchState) Target
          (lexicographicProgress (MinimumDegreeAtLeast k) BranchState))) :=
  FocusedDeletionCriticalityProfile focus
    (minimumDegreeDeletionCriticalityProfile k) context

/-- Query the certificate generated by the pure minimum-degree executor. -/
def focusedMinimumDegreeDeletionCriticalityQuery
    {Previous : Type uPrevious} (k : Nat)
    (focus : Core.Residual.Focus.Profile Previous)
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem (MinimumDegreeAtLeast k) BranchState) Target
          (lexicographicProgress (MinimumDegreeAtLeast k) BranchState))) :
    Core.Residual.Focus.ActiveQuery
      (FocusedMinimumDegreeDeletionCriticalityProfile k focus context)
      (fun stage active =>
        DeletionCriticalityCertificate
          (minimumDegreeDeletionCriticalityProfile k)
          (context.read stage.previous active)) :=
  focusedDeletionCriticalityQuery focus
    (minimumDegreeDeletionCriticalityProfile k) context

/-! ## Registered high-degree independence consequence -/

/-- The graph-generic independence statement forced by endpoint criticality. -/
abbrev SlackVertexIndependence
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) : Prop :=
  ∀ {left right : ctx.G.Vertex},
    profile.threshold + 1 ≤ ctx.G.degree left →
    profile.threshold + 1 ≤ ctx.G.degree right →
    Not (ctx.G.graph.Adj left right)

/-- Register the independence consequence carried by a deletion-criticality
certificate. -/
def deriveSlackVertexIndependence
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)}
    (certificate : DeletionCriticalityCertificate profile ctx) :
    SlackVertexIndependence profile ctx := by
  intro left right leftSlack rightSlack
  exact certificate.slackVerticesIndependent leftSlack rightSlack

/-- Output generated on one active branch by the independence executor. -/
abbrev FocusedSlackVertexIndependenceOutput
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (previous : Previous) (active : focus.Active previous) :=
  SlackVertexIndependence profile (context.read previous active)

/-- Accumulated successor carrying the registered independence fact. -/
abbrev FocusedSlackVertexIndependenceStage
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :=
  Core.Residual.Focus.Stage focus
    (FocusedSlackVertexIndependenceOutput focus profile context)

/-- Derive and ledger the independence consequence on the active branch. -/
def executeFocusedSlackVertexIndependence
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (criticality : Core.Residual.Focus.ActiveQuery focus
      (fun previous active =>
        DeletionCriticalityCertificate profile
          (context.read previous active)))
    (previous : Previous) :
    FocusedSlackVertexIndependenceStage focus profile context :=
  Core.Residual.Focus.run focus previous fun active =>
    deriveSlackVertexIndependence (criticality.read previous active)

/-- Active branch inherited after registering high-degree independence. -/
abbrev FocusedSlackVertexIndependenceProfile
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :=
  Core.Residual.Focus.successor focus
    (FocusedSlackVertexIndependenceOutput focus profile context)

/-- Query the independence fact generated by the newest Graph extension. -/
def focusedSlackVertexIndependenceQuery
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (profile : DeletionCriticalityProfile Baseline)
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :
    Core.Residual.Focus.ActiveQuery
      (FocusedSlackVertexIndependenceProfile focus profile context)
      (fun stage active =>
        FocusedSlackVertexIndependenceOutput focus profile context
          stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

/-- Minimum-degree convenience executor for the independence consequence. -/
def executeFocusedMinimumDegreeSlackVertexIndependence
    {Previous : Type uPrevious} (k : Nat)
    (focus : Core.Residual.Focus.Profile Previous)
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem (MinimumDegreeAtLeast k) BranchState) Target
          (lexicographicProgress (MinimumDegreeAtLeast k) BranchState)))
    (criticality : Core.Residual.Focus.ActiveQuery focus
      (fun previous active =>
        DeletionCriticalityCertificate
          (minimumDegreeDeletionCriticalityProfile k)
          (context.read previous active)))
    (previous : Previous) :=
  executeFocusedSlackVertexIndependence focus
    (minimumDegreeDeletionCriticalityProfile k) context criticality previous

/-- Minimum-degree convenience query for the registered independence fact. -/
def focusedMinimumDegreeSlackVertexIndependenceQuery
    {Previous : Type uPrevious} (k : Nat)
    (focus : Core.Residual.Focus.Profile Previous)
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem (MinimumDegreeAtLeast k) BranchState) Target
          (lexicographicProgress (MinimumDegreeAtLeast k) BranchState))) :=
  focusedSlackVertexIndependenceQuery focus
    (minimumDegreeDeletionCriticalityProfile k) context

end Hypostructure.Graph
