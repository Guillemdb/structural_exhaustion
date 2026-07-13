import Erdos64EG.CT2
import StructuralExhaustion.Graph.PackedBoundariedGluing

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

end ConcreteCT3

/-! ## Completed verified prefix -/

/-- Exact output of CT3 nodes `[11]`--`[14]`, retaining the preceding verified
minimal-counterexample prefix and only the airtight literal graph stage. -/
structure VerifiedBoundariedReplacementPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget) : Prop where
  previous : VerifiedNoProperCorePrefix ctx
  concrete : ∀ {T : Type u} (boundaries : FinEnum T) [Nonempty T],
    ConcreteCT3.VerifiedStage ctx boundaries

/-- Extend the already verified prefix without replacing its selected graph
or branch context. -/
def verifiedBoundariedReplacementPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (previous : VerifiedNoProperCorePrefix ctx) :
    VerifiedBoundariedReplacementPrefix ctx where
  previous := previous
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
      (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
        packedStaticInput).rank ctx.G ≤
          (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
            packedStaticInput).rank
            (Graph.PackedFiniteObject.pack object) ∧
        VerifiedBoundariedReplacementPrefix ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedNoProperCorePrefix object baseline avoids
  exact ⟨ctx, rankLe, {
    previous := previous
    concrete := fun boundaries =>
      Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.verifiedStage
        packedStaticInput boundaries ctx
  }⟩

end Erdos64EG.Internal
