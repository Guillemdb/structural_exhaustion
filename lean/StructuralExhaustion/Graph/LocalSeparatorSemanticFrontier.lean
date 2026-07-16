import StructuralExhaustion.Graph.LocalSeparatorProjection

namespace StructuralExhaustion.Graph.LocalSeparatorSemanticFrontier

open StructuralExhaustion

universe u uPayload

/-!
# Pending semantics for a literal local separator

These tags name obligations still to be proved.  In particular, possessing a
`Pending` value supplies no sparse-exit, response, CT3, Type-B, capacity, or
target theorem.
-/

inductive Obligation
  | sparseExit
  | ct3
  | typeB
  | fixedCaps
  deriving DecidableEq, Repr

/-- Retain one exact local payload while recording its next semantic
obligation.  The obligation is a routing tag, not evidence that it holds. -/
structure Pending (Payload : Type uPayload) (payload : Payload)
    (required : Obligation) where
  retained : Payload
  retainedExact : retained = payload
  obligation : Obligation
  obligationExact : obligation = required

def pending (payload : Payload) (required : Obligation) :
    Pending Payload payload required where
  retained := payload
  retainedExact := rfl
  obligation := required
  obligationExact := rfl

variable {V : Type u} (object : FiniteObject V)

def cubicPending {center : V} {data : CubicStar.Data object center}
    (projection : LocalSeparatorProjection.Cubic object data) :
    Pending _ projection .ct3 :=
  pending projection .ct3

def highPending {center : V} {degree_ge : 4 ≤ object.degree center}
    (projection : LocalSeparatorProjection.High object center degree_ge) :
    Pending _ projection .typeB :=
  pending projection .typeB

/-- Only one already-computed constructor tag is inspected. -/
def visibleChecks : Nat := 1

theorem visibleChecks_constant : visibleChecks ≤ 1 := le_rfl

end StructuralExhaustion.Graph.LocalSeparatorSemanticFrontier
