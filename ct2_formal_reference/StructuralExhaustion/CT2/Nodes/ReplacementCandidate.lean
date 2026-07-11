import StructuralExhaustion.CT2.Types

namespace StructuralExhaustion.CT2.Nodes.ReplacementCandidate

inductive Decision (F : Framework) (input : Input F)
    (_critical : DeletionCriticalState F input) where
  | found (state : CandidateState F input)
  | absent (state : SurvivorState F input)

abbrev Contract (F : Framework) (input : Input F)
    (critical : DeletionCriticalState F input) :=
  Decision F input critical

structure Plan (F : Framework) (input : Input F) where
  search : ∀ critical : DeletionCriticalState F input,
    Decision F input critical

def run {F : Framework} {input : Input F}
    (plan : Plan F input) (critical : DeletionCriticalState F input) :
    Contract F input critical :=
  plan.search critical

@[simp] theorem run_eq_search {F : Framework} {input : Input F}
    (plan : Plan F input) (critical : DeletionCriticalState F input) :
    run plan critical = plan.search critical := rfl

theorem found_absent_disjoint {F : Framework} {input : Input F}
    (found : CandidateState F input) (absent : SurvivorState F input) : False :=
  absent.targetUncompressible found.candidate

end StructuralExhaustion.CT2.Nodes.ReplacementCandidate
