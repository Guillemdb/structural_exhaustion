import Erdos64EG.CT5PortShoulderLedger
import StructuralExhaustion.Graph.OpenPortCompatibility

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT7: fan-compatible interpretation of the overload pair

The framework graph profile interprets the exact pair already routed from CT9
to CT7.  The bounded fibre branch is retained.  In the overload branch,
four-cycle avoidance proves that a nonadjacent endpoint pair has disjoint
shoulders and hence is fan-compatible; endpoint adjacency remains an explicit
alternative for the subsequent heavy-centre dichotomy.
-/

abbrev OpenPortCompatibilityState
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.OpenPortCompatibility.StateSpace
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

theorem openPortCompatibility_stateSpace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    OpenPortCompatibilityState ctx :=
  Graph.OpenPortCompatibility.stateSpace
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (fourCycleFree ctx)

structure VerifiedOpenPortCompatibilityPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedPortShoulderLedgerPrefix ctx
  stateSpace : OpenPortCompatibilityState ctx

def verifiedOpenPortCompatibilityPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedPortShoulderLedgerPrefix ctx) :
    VerifiedOpenPortCompatibilityPrefix ctx where
  previous := previous
  stateSpace := openPortCompatibility_stateSpace ctx

theorem exists_verifiedOpenPortCompatibilityPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedOpenPortCompatibilityPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedPortShoulderLedgerPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedOpenPortCompatibilityPrefix ctx previous⟩

end Erdos64EG.Internal
