import Erdos64EG.CT1TriangularPortReturn
import StructuralExhaustion.Graph.TriangularFirstLanding

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT10: first landing exhaustion for triangular shoulders

All finite classification, graph semantics, CT1-to-CT10 theorem composition,
trace validity, totality, and the quadratic work certificate are framework
owned.  This module only instantiates that API on the already selected Erdős
graph and retains the exact preceding return prefix.
-/

abbrev TriangularFirstLandingStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center) :=
  Graph.TriangularFirstLanding.VerifiedStage
    (triangularShoulderSetup ctx center centerHigh)

noncomputable def triangularFirstLandingStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center) :
    TriangularFirstLandingStage ctx center centerHigh :=
  Graph.TriangularFirstLanding.verifiedStage
    (triangularShoulderSetup ctx center centerHigh)

/-- The actual CT1 return from node `[79]` is consumed by the generic graph
composition and its noncentral first completion receives the CT10 class from
node `[80]`. -/
theorem triangularPortReturn_classified
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : ctx.G.Vertex) (centerHigh : 4 ≤ ctx.G.object.degree center)
    (port : Graph.TriangularPortReturn.TriPort
      (triangularShoulderSetup ctx center centerHigh)) :
    Graph.TriangularFirstLanding.ClassifiedReturnAlternative
      (Graph.TriangularPortReturn.certificate
        (triangularShoulderSetup ctx center centerHigh) port
        (triangularPortRoot ctx center centerHigh port)) :=
  Graph.TriangularFirstLanding.classifyReturn
    (triangularPortReturnStage ctx center centerHigh port)
    (triangularFirstLandingStage ctx center centerHigh)

structure VerifiedTriangularFirstLandingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedTriangularPortReturnPrefix ctx
  localStage : ∀ center (centerHigh : 4 ≤ ctx.G.object.degree center),
    TriangularFirstLandingStage ctx center centerHigh
  classifiedReturn : ∀ center (centerHigh : 4 ≤ ctx.G.object.degree center)
    (port : Graph.TriangularPortReturn.TriPort
      (triangularShoulderSetup ctx center centerHigh)),
    Graph.TriangularFirstLanding.ClassifiedReturnAlternative
      (Graph.TriangularPortReturn.certificate
        (triangularShoulderSetup ctx center centerHigh) port
        (triangularPortRoot ctx center centerHigh port))

noncomputable def verifiedTriangularFirstLandingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTriangularPortReturnPrefix ctx) :
    VerifiedTriangularFirstLandingPrefix ctx where
  previous := previous
  localStage := triangularFirstLandingStage ctx
  classifiedReturn := triangularPortReturn_classified ctx

theorem exists_verifiedTriangularFirstLandingPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedTriangularFirstLandingPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedTriangularPortReturnPrefix object baseline avoids
  exact ⟨ctx, rankLe,
    verifiedTriangularFirstLandingPrefix ctx previous⟩

end Erdos64EG.Internal
