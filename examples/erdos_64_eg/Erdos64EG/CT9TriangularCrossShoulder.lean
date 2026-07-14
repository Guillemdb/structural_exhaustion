import Erdos64EG.CT10TriangularFirstLanding
import StructuralExhaustion.Graph.TriangularCrossShoulder

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT9: cross-shoulder multiplicity

The graph layer owns the four-candidate shoulder-pair universe, CT9
partition, high-shoulder/four-cycle proof, bounded survivor, typed trace, and
constant work certificate.  This application retains node `[80]` and
instantiates the generic stage on the selected Erdős graph.
-/

abbrev TriangularCrossShoulderStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (first second : Graph.TriangularCrossShoulder.TriPort
      (triangularShoulderSetup ctx center centerHigh))
    (portsNe : first ≠ second) :=
  Graph.TriangularCrossShoulder.VerifiedStage first second portsNe

def triangularCrossShoulderStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (first second : Graph.TriangularCrossShoulder.TriPort
      (triangularShoulderSetup ctx center centerHigh))
    (portsNe : first ≠ second) :
    TriangularCrossShoulderStage ctx center centerHigh first second portsNe :=
  Graph.TriangularCrossShoulder.verifiedStage first second portsNe

/-- Exact manuscript state stratification: the high-shoulder branch is
explicit; if it does not occur, at most one cross edge survives. -/
theorem triangularCrossShoulder_stateSpace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (first second : Graph.TriangularCrossShoulder.TriPort
      (triangularShoulderSetup ctx center centerHigh))
    (portsNe : first ≠ second) :
    Graph.TriangularCrossShoulder.HighShoulder first second ∨
      CT9.fibreCount (Graph.TriangularCrossShoulder.capability first second)
        (Graph.TriangularCrossShoulder.input first second) () ≤ 1 :=
  (triangularCrossShoulderStage ctx center centerHigh first second portsNe).stateSpace

structure VerifiedTriangularCrossShoulderPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedTriangularFirstLandingPrefix ctx
  localStage : ∀ center (centerHigh : 4 ≤ ctx.G.object.degree center)
    (first second : Graph.TriangularCrossShoulder.TriPort
      (triangularShoulderSetup ctx center centerHigh))
    (portsNe : first ≠ second),
    TriangularCrossShoulderStage ctx center centerHigh first second portsNe

def verifiedTriangularCrossShoulderPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTriangularFirstLandingPrefix ctx) :
    VerifiedTriangularCrossShoulderPrefix ctx where
  previous := previous
  localStage := triangularCrossShoulderStage ctx

theorem exists_verifiedTriangularCrossShoulderPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedTriangularCrossShoulderPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedTriangularFirstLandingPrefix object baseline avoids
  exact ⟨ctx, rankLe,
    verifiedTriangularCrossShoulderPrefix ctx previous⟩

end Erdos64EG.Internal
