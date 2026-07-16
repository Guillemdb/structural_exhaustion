import StructuralExhaustion.Graph.CubicStar
import StructuralExhaustion.Graph.DeletedEdgeReturnThirdIncidence

namespace StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar

open StructuralExhaustion

universe u

variable {V : Type u} {object : FiniteObject V}
variable {dart : object.graph.Dart}

/-!
# The outside third incidence as an oriented cubic boundary star

This module consumes the exact `outsideBoundary` result of
`DeletedEdgeReturnThirdIncidence.run`.  It packages only the one oriented
incidence certified by that result: the return root lies in the supplied
return support, while the selected third neighbour lies outside it.  The
already-certified three incidences at the cubic root also determine a
`CubicStar.Data` and its finite ownership shape.

No support-wide scan is performed here.  In particular, this module does not
construct an induced-path boundary stub, a component or successor relation,
D4--D7 coordinates, a response vector, a density estimate, or a CT3 input.
-/

/-- Exact incoming branch, including the equality to the computed local run.
The proof `outside` is not accepted independently of that run. -/
structure OutsideRun
    (setup : DeletedEdgeReturnThirdIncidence.Setup object dart) where
  outside : setup.third.hit.value ∉ setup.returnPath.path.support
  runExact : DeletedEdgeReturnThirdIncidence.run setup =
    .outsideBoundary outside

namespace OutsideRun

variable {setup : DeletedEdgeReturnThirdIncidence.Setup object dart}

/-- The orientation is from the return support at `dart.snd` to the selected
third neighbour outside that same literal support. -/
structure OrientedReturnBoundary (branch : OutsideRun setup) where
  computed_outside_branch : DeletedEdgeReturnThirdIncidence.run setup =
    .outsideBoundary branch.outside
  root_mem_support : dart.snd ∈ setup.returnPath.path.support
  selected_not_mem_support :
    setup.third.hit.value ∉ setup.returnPath.path.support
  selected_adjacent : object.graph.Adj dart.snd setup.third.hit.value
  selected_ne_first_return : setup.third.hit.value ≠ setup.firstNext
  selected_ne_restored_endpoint : setup.third.hit.value ≠ dart.fst

/-- Package the single certified support-crossing incidence. -/
def orientedBoundary (branch : OutsideRun setup) :
    OrientedReturnBoundary branch where
  computed_outside_branch := branch.runExact
  root_mem_support := setup.returnPath.path.start_mem_support
  selected_not_mem_support := branch.outside
  selected_adjacent := setup.third_adjacent
  selected_ne_first_return := setup.third_ne_firstNext
  selected_ne_restored_endpoint := setup.third_ne_dart_fst

/-- The exact cubic star whose ordered leaves are the first return step, the
restored dart endpoint, and the selected outside endpoint. -/
def cubicStar (_branch : OutsideRun setup) : CubicStar.Data object dart.snd :=
  CubicStar.ofRootDivergence object setup.divergence setup.third
    setup.degree_eq_three

@[simp] theorem cubicStar_first (branch : OutsideRun setup) :
    branch.cubicStar.first = setup.firstNext := rfl

@[simp] theorem cubicStar_second (branch : OutsideRun setup) :
    branch.cubicStar.second = dart.fst := rfl

@[simp] theorem cubicStar_third (branch : OutsideRun setup) :
    branch.cubicStar.third = setup.third.hit.value := rfl

/-- The finite one-internal/three-boundary ownership shape supplied by the
exact cubic star. -/
def switchBoundaryShape (branch : OutsideRun setup) :
    (branch.cubicStar).SwitchBoundaryShape :=
  CubicStar.Data.switchBoundaryShape object branch.cubicStar

/-- Cubicity proves that the three displayed leaves own every incidence at
the return root. -/
theorem ownsAllRootIncidences (branch : OutsideRun setup) :
    ∀ vertex, object.graph.Adj dart.snd vertex →
      ∃ index, branch.switchBoundaryShape.boundaryVertex index = vertex :=
  branch.switchBoundaryShape.ownsAllInternalIncidences

/-- This post-processing only projects proof-carrying node data. -/
def additionalChecks (_branch : OutsideRun setup) : Nat := 0

theorem additionalChecks_eq_zero (branch : OutsideRun setup) :
    branch.additionalChecks = 0 := rfl

end OutsideRun

end StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar
