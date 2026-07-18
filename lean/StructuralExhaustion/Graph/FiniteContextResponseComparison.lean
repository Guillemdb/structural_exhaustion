import StructuralExhaustion.CT7.Automation

namespace StructuralExhaustion.Graph.FiniteContextResponseComparison

open StructuralExhaustion

universe uAmbient uBranch uObject uOutside uCode

/-!
# Finite response codes for universal outside-context comparison

The runner inspects only the proof-declared finite code alphabet.  A symbolic
coverage theorem, rather than an enumeration of outside contexts, transports
the result to every compatible outside context.
-/

structure Profile (P : Core.Problem.{uAmbient, uBranch})
    (branch : Core.BranchContext P) where
  Object : Type uObject
  Outside : Type uOutside
  Code : Type uCode
  codes : FinEnum Code
  left : Object
  right : Object
  response : Object → Code → Bool
  targetResponse : Object → Outside → Prop
  decode : Code → Outside
  response_reflect : ∀ object code,
    response object code = true ↔ targetResponse object (decode code)
  pairCoverage : ∀ outside, ∃ code,
    (targetResponse left outside ↔ response left code = true) ∧
    (targetResponse right outside ↔ response right code = true)

namespace Profile

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {branch : Core.BranchContext P}
variable (profile : Profile P branch)

def spec : CT7.Spec P where
  Object := profile.Object
  Context := profile.Code
  Realizes := fun _ _ _ ↦ False
  response := fun _ object code ↦ profile.response object code

def capability : CT7.Capability profile.spec where
  contexts := fun _ _ _ ↦ profile.codes
  realizesDecidable := fun _ _ _ ↦ .isFalse id

def input : CT7.Input profile.spec branch where
  left := profile.left
  right := profile.right

noncomputable def ct7Run := CT7.run profile.spec profile.capability branch profile.input

structure Distinction where
  code : profile.Code
  outside : profile.Outside
  outside_eq : outside = profile.decode code
  differs : ¬ (profile.targetResponse profile.left outside ↔
    profile.targetResponse profile.right outside)

structure Neutrality : Prop where
  codeEqual : ∀ code,
    profile.response profile.left code = profile.response profile.right code
  universal : ∀ outside,
    profile.targetResponse profile.left outside ↔
      profile.targetResponse profile.right outside

inductive Outcome where
  | distinction (data : profile.Distinction)
  | neutral (data : profile.Neutrality)

private theorem bool_true_iff_of_eq {left right : Bool} (equal : left = right) :
    (left = true ↔ right = true) := by simp [equal]

private def distinctionOfResidual
    (residual : CT7.DistinguishingResidual profile.spec profile.capability
      branch profile.input) : profile.Distinction := by
  refine ⟨residual.context, profile.decode residual.context, rfl, ?_⟩
  intro targetIff
  have responseIff : profile.response profile.left residual.context = true ↔
      profile.response profile.right residual.context = true :=
    (profile.response_reflect profile.left residual.context).trans
      (targetIff.trans
        (profile.response_reflect profile.right residual.context).symm)
  have responseEqual : profile.response profile.left residual.context =
      profile.response profile.right residual.context := by
    cases leftEq : profile.response profile.left residual.context <;>
      cases rightEq : profile.response profile.right residual.context <;>
      simp [leftEq, rightEq] at responseIff ⊢
  exact residual.differs responseEqual

private def neutralityOfCertificate
    (certificate : CT7.NeutralityCertificate profile.spec profile.capability
      branch profile.input) : profile.Neutrality := by
  refine ⟨certificate.allEqual, ?_⟩
  intro outside
  rcases profile.pairCoverage outside with ⟨code, leftIff, rightIff⟩
  exact leftIff.trans
    ((bool_true_iff_of_eq (certificate.allEqual code)).trans rightIff.symm)

/-- Public CT7 execution.  The realization constructor is impossible because
`Realizes` is definitionally false; the remaining constructors are exactly a
literal outside-context distinction or universal neutrality. -/
noncomputable def run : profile.Outcome := by
  match first : CT7.analyzeRealization profile.spec profile.capability
      branch profile.input with
  | .realizing certificate => exact False.elim certificate.realizes
  | .unrealized unrealized =>
      match CT7.analyzeDistinction profile.spec profile.capability
          branch profile.input unrealized with
      | .distinguishing residual =>
          exact .distinction (profile.distinctionOfResidual residual)
      | .neutral certificate =>
          exact .neutral (profile.neutralityOfCertificate certificate)

theorem ct7Run_verified : profile.ct7Run.outcome.Valid :=
  profile.ct7Run.verified

theorem ct7Run_traceValid :
    CT7.Graph.ValidTrace profile.spec profile.capability branch profile.input
      profile.ct7Run.trace :=
  profile.ct7Run.traceValid

theorem ct7Run_total : ∃ result : CT7.ExecutionResult profile.spec
    profile.capability branch profile.input,
    result.outcome.Valid ∧
      CT7.Graph.ValidTrace profile.spec profile.capability branch profile.input
        result.trace :=
  CT7.run_total profile.spec profile.capability branch profile.input

/-- Exactly two finite passes are visible: realization (vacuously false) and
response distinction. -/
def checks : Nat := 2 * profile.codes.orderedValues.length

theorem checks_eq : profile.checks = 2 * profile.codes.card := by
  simp [checks, FinEnum.orderedValues_length]

end Profile

end StructuralExhaustion.Graph.FiniteContextResponseComparison
