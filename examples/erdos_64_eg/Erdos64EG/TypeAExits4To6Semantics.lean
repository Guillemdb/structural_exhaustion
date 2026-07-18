import Erdos64EG.TypeAExit2CommonPort
import Erdos64EG.CT15RemainderCurvature
import StructuralExhaustion.Graph.FiniteContextResponseComparison
import StructuralExhaustion.Routes.TargetDefectHandoff

namespace Erdos64EG.Internal.TypeAExits4To6Semantics

open StructuralExhaustion
open Graph.PackedBoundariedGluing
open Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement

universe u

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  {T : Type u} (boundaries : FinEnum T) [Nonempty T]

/-- Original exit (4): the literal finite-code comparison found an actual
outside context distinguishing two concrete boundaried pieces. -/
structure Exit4 where
  source : Routes.TargetDefectHandoff.Source packedStaticInput boundaries ctx

/-- Original exit (5): a concrete target-complete smaller replacement of one
proper atom.  This is exactly the existing CT3 compression input. -/
structure Exit5 where
  atom : ProperAtom packedStaticInput boundaries ctx
  compression : Compression packedStaticInput boundaries atom

/-- Original exit (6): the equality is carried by an enlarged support whose
location is classified by the existing proper-versus-whole delocalization
route. -/
structure Exit6 where
  original : ProperDelocalizationAtom ctx boundaries
  Whole : Type u
  location : ProperDelocalizationLocation ctx boundaries original Whole

namespace Exit4

def routed (exit4 : Exit4 (ctx := ctx) boundaries) :
    Routes.TargetDefectHandoff.Residual packedStaticInput boundaries ctx :=
  Routes.TargetDefectHandoff.route packedStaticInput boundaries ctx exit4.source

end Exit4

namespace Exit5

theorem closes (exit5 : Exit5 (ctx := ctx) boundaries) : False :=
  exit5.compression.impossible

end Exit5

namespace Exit6

def routed (exit6 : Exit6 (ctx := ctx) boundaries) :
    ProperDelocalizationRouted ctx boundaries exit6.original exit6.Whole :=
  routeProperDelocalization ctx boundaries exit6.original exit6.Whole exit6.location

end Exit6

/-- Concrete finite response comparison for two boundaried pieces.  Coverage
is symbolic; no outside-context universe is enumerated. -/
structure Comparison where
  codes : FinEnum T
  left : Piece T
  right : Piece T
  response : Piece T → T → Bool
  decode : T → Context T
  response_reflect : ∀ piece code,
    response piece code = true ↔
      PackedTarget (glue boundaries piece (decode code))
  pairCoverage : ∀ outside : Context T, ∃ code,
    (PackedTarget (glue boundaries left outside) ↔ response left code = true) ∧
    (PackedTarget (glue boundaries right outside) ↔ response right code = true)
  boundaryDegree_eq : BoundaryDegreeProfile boundaries left =
    BoundaryDegreeProfile boundaries right

namespace Comparison

def profile (comparison : Comparison boundaries) :
    Graph.FiniteContextResponseComparison.Profile PackedProblem
      ctx.toBranchContext where
  Object := Piece T
  Outside := Context T
  Code := T
  codes := comparison.codes
  left := comparison.left
  right := comparison.right
  response := comparison.response
  targetResponse := fun piece outside => PackedTarget (glue boundaries piece outside)
  decode := comparison.decode
  response_reflect := comparison.response_reflect
  pairCoverage := comparison.pairCoverage

/-- Where a universally neutral comparison lives.  These are precisely the
paper's local-compression and enlarged-support alternatives. -/
inductive NeutralLocation (comparison : Comparison boundaries) where
  | atAtom
      (atom : ProperAtom packedStaticInput boundaries ctx)
      (right_eq : comparison.right = atom.source)
      (internalTargetFree : ¬PackedTarget (Piece.pack boundaries comparison.left))
      (internalBaseline : comparison.left.InternalBaseline boundaries 3)
      (locallySmaller : Piece.LexSmaller comparison.left atom.source)
  | delocalized (payload : Exit6 (ctx := ctx) boundaries)

inductive Outcome where
  | exit4 (data : Exit4 (ctx := ctx) boundaries)
  | exit5 (data : Exit5 (ctx := ctx) boundaries)
  | exit6 (data : Exit6 (ctx := ctx) boundaries)

private def exit4OfDistinction (comparison : Comparison boundaries)
    (distinction : (profile (ctx := ctx) boundaries comparison).Distinction) :
    Exit4 (ctx := ctx) boundaries where
  source := {
    branch := ctx.toBranchContext
    branch_eq := rfl
    left := comparison.left
    right := comparison.right
    outside := distinction.outside
    differs := distinction.differs }

private noncomputable def exit5OfNeutral
    (comparison : Comparison boundaries)
    (neutral : (profile (ctx := ctx) boundaries comparison).Neutrality)
    (atom : ProperAtom packedStaticInput boundaries ctx)
    (right_eq : comparison.right = atom.source)
    (internalTargetFree : ¬PackedTarget (Piece.pack boundaries comparison.left))
    (internalBaseline : comparison.left.InternalBaseline boundaries 3)
    (locallySmaller : Piece.LexSmaller comparison.left atom.source) :
    Exit5 (ctx := ctx) boundaries := by
  have complete : TargetComplete packedStaticInput boundaries
      comparison.left atom.source := by
    refine ⟨by simpa [right_eq] using comparison.boundaryDegree_eq, ?_⟩
    intro outside
    have universal := neutral.universal outside
    change PackedTarget (glue boundaries comparison.left outside) ↔
      PackedTarget (glue boundaries comparison.right outside) at universal
    simpa [right_eq] using universal
  exact {
    atom := atom
    compression := Compression.ofTargetComplete packedStaticInput boundaries
      comparison.left complete internalTargetFree internalBaseline locallySmaller }

/-- Original nodes `[101]`, `[103]`, `[105]`: execute the finite declared-code
comparison and return exactly exit (4), (5), or (6). -/
noncomputable def run (comparison : Comparison boundaries)
    (location : NeutralLocation (ctx := ctx) boundaries comparison) :
    Outcome (ctx := ctx) boundaries := by
  match (profile (ctx := ctx) boundaries comparison).run with
  | .distinction data => exact .exit4 (exit4OfDistinction (ctx := ctx) boundaries comparison data)
  | .neutral data =>
      match location with
      | .atAtom atom rightEq targetFree baseline smaller =>
          exact .exit5 (exit5OfNeutral (ctx := ctx) boundaries comparison data atom rightEq
            targetFree baseline smaller)
      | .delocalized payload => exact .exit6 payload

theorem run_total (comparison : Comparison boundaries)
    (location : NeutralLocation (ctx := ctx) boundaries comparison) :
    (∃ data, run (ctx := ctx) boundaries comparison location = .exit4 data) ∨
    (∃ data, run (ctx := ctx) boundaries comparison location = .exit5 data) ∨
    (∃ data, run (ctx := ctx) boundaries comparison location = .exit6 data) := by
  unfold run
  split <;> rename_i response
  · exact Or.inl ⟨_, rfl⟩
  · cases location with
    | atAtom atom rightEq targetFree baseline smaller =>
        exact Or.inr (Or.inl ⟨_, rfl⟩)
    | delocalized payload => exact Or.inr (Or.inr ⟨_, rfl⟩)

def checks (comparison : Comparison boundaries) : Nat :=
  (profile (ctx := ctx) boundaries comparison).checks

theorem checks_eq (comparison : Comparison boundaries) :
    checks (ctx := ctx) boundaries comparison = 2 * comparison.codes.card :=
  (profile (ctx := ctx) boundaries comparison).checks_eq

end Comparison

end Erdos64EG.Internal.TypeAExits4To6Semantics
