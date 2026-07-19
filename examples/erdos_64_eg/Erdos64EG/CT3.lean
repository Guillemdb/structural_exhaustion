import Erdos64EG.CT2
import StructuralExhaustion.Graph.BoundariedRankDrop

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT3: boundaried replacement and hereditary uncompressibility

One CT3 stage realizes manuscript nodes [11]--[14].  It defines the labelled
boundary profile and obstruction profile, proves context universality and
boundary-fibre separation, and executes literal graph replacement for every
normalized decomposition with nonempty boundary.  Whole-graph decrease,
baseline preservation, and target transport are derived rather than supplied
as certificate fields.  The explicit nonempty-boundary scope is the current
formal boundary; the closed empty-boundary branch is not claimed here.
-/

abbrev PackedProblem :=
  Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u} packedStaticInput

abbrev PackedTarget :=
  Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u} packedStaticInput

/-! ## Airtight literal graph-gluing boundary -/

namespace ConcreteCT3

abbrev Piece (T : Type u) := Graph.PackedBoundariedGluing.Piece T
abbrev Context (T : Type u) := Graph.PackedBoundariedGluing.Context T

abbrev ProperAtom
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T] :=
  Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom
    packedStaticInput boundaries ctx

abbrev Compression
    {ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget}
    {T : Type u} {boundaries : FinEnum T} [Nonempty T]
    (atom : ProperAtom ctx boundaries) :=
  Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression
    packedStaticInput boundaries atom

abbrev VerifiedStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T] :=
  Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.VerifiedStage
    packedStaticInput boundaries ctx

abbrev RankDropCertificate
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (atom : ProperAtom ctx boundaries) (Enlarged : Type u) :=
  Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.Certificate
    packedStaticInput boundaries atom Enlarged

abbrev RankDropRouted
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (atom : ProperAtom ctx boundaries) (Enlarged : Type u) :=
  Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.Routed
    packedStaticInput boundaries atom Enlarged

abbrev RankDropVerifiedStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (atom : ProperAtom ctx boundaries) (Enlarged : Type u) :=
  Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.VerifiedStage
    packedStaticInput boundaries atom Enlarged

end ConcreteCT3

/-! ## Completed verified prefix -/

/-- Exact output of CT3 nodes `[11]`--`[14]`, retaining the preceding verified
minimal-counterexample prefix and only the airtight literal graph stage. -/
structure VerifiedBoundariedReplacementPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget) : Type (u + 1)
    extends Core.ExactHandoff
      (packedStaticInput.edgeRootedNoProperCorePrefix ctx) where
  concrete : ∀ {T : Type u} (boundaries : FinEnum T) [Nonempty T],
    ConcreteCT3.VerifiedStage ctx boundaries

instance verifiedBoundariedReplacementPrefix_subsingleton
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget) :
    Subsingleton (VerifiedBoundariedReplacementPrefix ctx) where
  allEq := by
    rintro ⟨handoff, concrete⟩ ⟨other, otherConcrete⟩
    have handoffEq : handoff = other := Subsingleton.elim _ _
    subst handoffEq
    rfl

/-- Extend the already verified prefix without replacing its selected graph
or branch context. -/
def verifiedBoundariedReplacementPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (previous : VerifiedNoProperCorePrefix ctx) :
    VerifiedBoundariedReplacementPrefix ctx where
  previous := previous
  previousExact := Subsingleton.elim _ _
  concrete := fun boundaries =>
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.verifiedStage
      packedStaticInput boundaries ctx

/-- Provenance: CT3 retains the exact node [8] and local-deletion CT2 output
that it consumes. -/
theorem boundariedReplacementPrefix_previous
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (verified : VerifiedBoundariedReplacementPrefix ctx) :
    VerifiedNoProperCorePrefix ctx :=
  verified.previous

/-- Authoritative concrete stage: literal normalized gluing, reconstruction by
graph isomorphism, derived global rank decrease, derived baseline preservation,
and derived target transport. -/
theorem boundariedReplacementPrefix_concrete
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (verified : VerifiedBoundariedReplacementPrefix ctx)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T] :
    ConcreteCT3.VerifiedStage ctx boundaries :=
  verified.concrete boundaries

/-- Authoritative node [14] consequence extracted from the composed prefix.
All global graph obligations are derived in the literal gluing layer. -/
theorem boundariedReplacementPrefix_uncompressible
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (verified : VerifiedBoundariedReplacementPrefix ctx)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (atom : ConcreteCT3.ProperAtom ctx boundaries)
    (compression : ConcreteCT3.Compression atom) : False :=
  (verified.concrete boundaries).compressionImpossible atom compression

/-! ## Rank-drop reuse at nodes `[36]`--`[39]` -/

/-- Exact context-audit dichotomy for the incoming node `[35]` determination
certificate. -/
theorem rankDrop_contextAudit
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (_previous : VerifiedBoundariedReplacementPrefix ctx)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    {atom : ConcreteCT3.ProperAtom ctx boundaries} {Enlarged : Type u}
    (certificate : ConcreteCT3.RankDropCertificate ctx boundaries atom Enlarged) :
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetDefective
        packedStaticInput boundaries certificate.realization atom.source ∨
      Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetComplete
        packedStaticInput boundaries certificate.realization atom.source :=
  certificate.contextAudit

/-- The at-atom, context-universal branch executes the literal CT3
compression and contradicts minimality. -/
theorem rankDrop_atAtom_impossible
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (_previous : VerifiedBoundariedReplacementPrefix ctx)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    {atom : ConcreteCT3.ProperAtom ctx boundaries}
    (realization : ConcreteCT3.Piece T)
    (internalTargetFree :
      ¬ PackedTarget (Graph.PackedBoundariedGluing.Piece.pack boundaries realization))
    (internalBaseline : realization.InternalBaseline boundaries 3)
    (locallySmaller : Graph.PackedBoundariedGluing.Piece.LexSmaller
      realization atom.source)
    (universal :
      Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetComplete
        packedStaticInput boundaries realization atom.source) : False :=
  Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.AtAtom.impossible
    realization internalTargetFree internalBaseline locallySmaller universal

theorem rankDrop_atAtom_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (_previous : VerifiedBoundariedReplacementPrefix ctx)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    {atom : ConcreteCT3.ProperAtom ctx boundaries}
    (realization : ConcreteCT3.Piece T)
    (internalTargetFree :
      ¬ PackedTarget (Graph.PackedBoundariedGluing.Piece.pack boundaries realization))
    (internalBaseline : realization.InternalBaseline boundaries 3)
    (locallySmaller : Graph.PackedBoundariedGluing.Piece.LexSmaller
      realization atom.source)
    (universal :
      Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetComplete
        packedStaticInput boundaries realization atom.source) :
    (Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run
      (Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.AtAtom.compression
        realization internalTargetFree internalBaseline locallySmaller universal)).terminal =
      .compression := rfl

theorem rankDrop_atAtom_trace
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (_previous : VerifiedBoundariedReplacementPrefix ctx)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    {atom : ConcreteCT3.ProperAtom ctx boundaries}
    (realization : ConcreteCT3.Piece T)
    (internalTargetFree :
      ¬ PackedTarget (Graph.PackedBoundariedGluing.Piece.pack boundaries realization))
    (internalBaseline : realization.InternalBaseline boundaries 3)
    (locallySmaller : Graph.PackedBoundariedGluing.Piece.LexSmaller
      realization atom.source)
    (universal :
      Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetComplete
        packedStaticInput boundaries realization atom.source) :
    (Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run
      (Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.AtAtom.compression
        realization internalTargetFree internalBaseline locallySmaller universal)).trace =
      [.entry, .vectorComputation, .compressionSearch, .compressionTerminal] := rfl

/-- The only surviving local outputs are the concrete defect witness for node
`[37]` or the unchanged enlarged-support residual consumed by white node
`[40]`. -/
theorem rankDrop_routed
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (_previous : VerifiedBoundariedReplacementPrefix ctx)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    {atom : ConcreteCT3.ProperAtom ctx boundaries} {Enlarged : Type u}
    (certificate : ConcreteCT3.RankDropCertificate ctx boundaries atom Enlarged) :
    ConcreteCT3.RankDropRouted ctx boundaries atom Enlarged :=
  Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.route
    packedStaticInput boundaries certificate

structure VerifiedRankDropRoutingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (prior : VerifiedBoundariedReplacementPrefix ctx)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (atom : ConcreteCT3.ProperAtom ctx boundaries) (Enlarged : Type u) : Type (u + 1)
    extends Core.ExactHandoff prior where
  stage : ConcreteCT3.RankDropVerifiedStage ctx boundaries atom Enlarged

/-- Complete node `[36]`--`[39]` stage, indexed by the exact selected graph and
proper atom retained by the verified replacement prefix. -/
noncomputable def verifiedRankDropRoutingStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (previous : VerifiedBoundariedReplacementPrefix ctx)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (atom : ConcreteCT3.ProperAtom ctx boundaries) (Enlarged : Type u) :
    VerifiedRankDropRoutingPrefix ctx previous boundaries atom Enlarged where
  previous := previous
  previousExact := rfl
  stage :=
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.verifiedStage
      packedStaticInput boundaries atom Enlarged

def rankDropRoutingPrefix_previous
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    {atom : ConcreteCT3.ProperAtom ctx boundaries} {Enlarged : Type u}
    {prior : VerifiedBoundariedReplacementPrefix ctx}
    (verified : VerifiedRankDropRoutingPrefix ctx prior boundaries atom Enlarged) :
    VerifiedBoundariedReplacementPrefix ctx :=
  verified.previous

theorem rankDropRoutingPrefix_stage
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    {atom : ConcreteCT3.ProperAtom ctx boundaries} {Enlarged : Type u}
    {prior : VerifiedBoundariedReplacementPrefix ctx}
    (verified : VerifiedRankDropRoutingPrefix ctx prior boundaries atom Enlarged) :
    ConcreteCT3.RankDropVerifiedStage ctx boundaries atom Enlarged :=
  verified.stage

/-- Starting with only the official internal counterexample data, select the
same packed lexicographic minimum used by the preceding prefix and extend that
verified output through the complete boundaried-replacement CT3 stage. -/
theorem exists_verifiedBoundariedReplacementPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬ Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext
        (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
          packedStaticInput)
        (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u}
          packedStaticInput),
      ∃ _ : VerifiedBoundariedReplacementPrefix ctx,
        (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
          packedStaticInput).rank ctx.G ≤
          (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
            packedStaticInput).rank
            (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedNoProperCorePrefix object baseline avoids
  exact ⟨ctx, {
    previous := previous
    previousExact := Subsingleton.elim _ _
    concrete := fun boundaries =>
      Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.verifiedStage
        packedStaticInput boundaries ctx
  }, rankLe⟩

end Erdos64EG.Internal
