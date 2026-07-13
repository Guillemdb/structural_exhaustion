import StructuralExhaustion.CT7.State

namespace StructuralExhaustion.CT7

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (ctx : Core.BranchContext P) (input : Input S ctx)

/-- First node decision: either the first realizing context or exhaustive
absence.  It does not inspect response equality. -/
inductive RealizationDecision where
  | realizing (certificate : RealizationCertificate S capability ctx input)
  | unrealized (state : UnrealizedState S capability ctx input)

def analyzeRealization : RealizationDecision S capability ctx input :=
  let contexts := capability.contexts ctx input.left input.right
  match Core.FiniteSearch.search contexts (S.Realizes ctx input.left)
      (capability.realizesDecidable ctx input.left) with
  | .found context realizes => .realizing
      ⟨context, contexts.mem_orderedValues context, realizes⟩
  | .absent noRealization => .unrealized
      ⟨contexts.mem_orderedValues, noRealization⟩

/-- Second node decision, indexed by the exact unrealized predecessor. -/
inductive DistinctionDecision
    (unrealized : UnrealizedState S capability ctx input) where
  | distinguishing (residual : DistinguishingResidual S capability ctx input)
  | neutral (certificate : NeutralityCertificate S capability ctx input)

def analyzeDistinction
    (unrealized : UnrealizedState S capability ctx input) :
    DistinctionDecision S capability ctx input unrealized :=
  let contexts := capability.contexts ctx input.left input.right
  match Core.FiniteSearch.search contexts
      (fun context => S.response ctx input.left context ≠
        S.response ctx input.right context)
      (fun _ => inferInstance) with
  | .found context differs => .distinguishing
      ⟨unrealized, context, differs⟩
  | .absent noDifference => .neutral {
      unrealized := unrealized
      allEqual := fun context =>
        match decEq (S.response ctx input.left context)
            (S.response ctx input.right context) with
        | .isTrue same => same
        | .isFalse differs => (noDifference context differs).elim
    }

theorem analyzeRealization_sound :
    match analyzeRealization S capability ctx input with
    | .realizing certificate => S.Realizes ctx input.left certificate.context
    | .unrealized _ => ∀ context, ¬ S.Realizes ctx input.left context := by
  cases analyzeRealization S capability ctx input with
  | realizing certificate => exact certificate.realizes
  | unrealized state => exact state.noRealization

theorem analyzeDistinction_sound
    (unrealized : UnrealizedState S capability ctx input) :
    match analyzeDistinction S capability ctx input unrealized with
    | .distinguishing residual =>
        S.response ctx input.left residual.context ≠
          S.response ctx input.right residual.context
    | .neutral _ =>
        ∀ context, S.response ctx input.left context =
          S.response ctx input.right context := by
  cases analyzeDistinction S capability ctx input unrealized with
  | distinguishing residual => exact residual.differs
  | neutral certificate => exact certificate.allEqual

end StructuralExhaustion.CT7
