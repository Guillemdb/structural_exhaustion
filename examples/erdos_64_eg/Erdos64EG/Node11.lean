import Erdos64EG.Node10
import StructuralExhaustion.Graph.PackedBoundariedGluing

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [11]: boundaried atoms and boundary-degree profiles

The literal node-[10] stage determines the one live graph.  This node adds only
the proper boundaried atoms of that graph and each atom's uncapped boundary
degree profile.
-/

abbrev Node11ProperAtom
    (ctx : Core.MinimalCounterexampleContext
      (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u} packedStaticInput)
      (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u} packedStaticInput))
    {T : Type u} (boundaries : FinEnum T) [Nonempty T] :=
  Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom
    packedStaticInput boundaries ctx

structure Node11AtomProfile
    (ctx : Core.MinimalCounterexampleContext
      (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u} packedStaticInput)
      (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u} packedStaticInput))
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (atom : Node11ProperAtom ctx boundaries) where
  boundaryDegreeProfile : T → Nat
  profile_eq : boundaryDegreeProfile =
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.BoundaryDegreeProfile
      boundaries atom.source

abbrev Node11BoundariedAtomFamily
    (ctx : Core.MinimalCounterexampleContext
      (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u} packedStaticInput)
      (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u} packedStaticInput)) :=
  ∀ {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (atom : Node11ProperAtom ctx boundaries), Node11AtomProfile ctx boundaries atom

abbrev Node11Output {V : Type u} {residual : InitialResidual V}
    (node10 : Node10Stage residual) :=
  Node11BoundariedAtomFamily (Node10Context node10)

abbrev Node11Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor (@Node10Stage V)
    (fun _current node10 => Node11Output node10) residual

abbrev Node11Context {V : Type u} {residual : InitialResidual V}
    (node11 : Node11Stage residual) :=
  Node10Context node11.previous

private noncomputable def node11Output {V : Type u}
    {residual : InitialResidual V} (node10 : Node10Stage residual) :
    Node11Output node10 := by
  intro T boundaries nonempty atom
  exact {
    boundaryDegreeProfile :=
      Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.BoundaryDegreeProfile
        boundaries atom.source
    profile_eq := rfl
  }

noncomputable def node11BoundariedAtoms {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node10Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) (@Node11Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (fun _residual node10 => node11Output node10)

noncomputable def runInitialThroughNode11 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode10 residual).mapYesStage node11BoundariedAtoms

def node11_boundaryDegreeProfile {V : Type u}
    {residual : InitialResidual V} (stage : Node11Stage residual) :
    Node11Output stage.previous :=
  stage.output

def node11LocalChecks : Nat := 0

theorem node11LocalChecks_eq_zero : node11LocalChecks = 0 := rfl

#print axioms runInitialThroughNode11
#print axioms node11_boundaryDegreeProfile

end Erdos64EG.Internal
