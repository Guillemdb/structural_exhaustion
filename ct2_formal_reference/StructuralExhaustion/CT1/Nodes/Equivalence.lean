import StructuralExhaustion.CT1.Types

namespace StructuralExhaustion.CT1.Nodes.Equivalence

abbrev Contract (F : Framework) (input : Input F) :=
  EquivalenceState F input

/-- The equivalence node is a certification boundary.  A plan for an admitted
run must produce the certificate; failure to do so is a design-time repair,
not an untyped runtime branch. -/
structure Plan (F : Framework) (input : Input F) where
  certify : ScopedState F input → EquivalenceState F input

def run {F : Framework} {input : Input F}
    (plan : Plan F input) (state : ScopedState F input) :
    Contract F input :=
  plan.certify state

@[simp] theorem run_eq_certify {F : Framework} {input : Input F}
    (plan : Plan F input) (state : ScopedState F input) :
    run plan state = plan.certify state := rfl

end StructuralExhaustion.CT1.Nodes.Equivalence
