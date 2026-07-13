import Mathlib.Tactic
import StructuralExhaustion.CT12.DisjointPacking

namespace StructuralExhaustion.Examples.CT12DisjointPacking

open StructuralExhaustion

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def context : Core.BranchContext problem := ⟨(), trivial, ()⟩

/-- Empty item types produce the zero-step exhausted execution. -/
noncomputable def emptyProfile :
    CT12.DisjointPacking.Profile (Fin 1) Empty where
  vertices := inferInstance
  finiteItems := inferInstance
  support := Empty.elim
  representative := Empty.elim
  representative_mem := by
    intro item
    exact item.elim

noncomputable def emptyRun := emptyProfile.run context

example : emptyRun.terminal = .exhausted :=
  emptyProfile.run_terminal_exhausted context

example : emptyRun.iterations = 0 := by
  have valuesEmpty : emptyProfile.values = [] := by
    cases valuesEq : emptyProfile.values with
    | nil => rfl
    | cons head tail => exact head.elim
  change (emptyProfile.run context).iterations = 0
  rw [emptyProfile.run_iterations_eq_values context, valuesEmpty]
  simp

/-- Three singleton supports force a three-item maximum packing and exercise
multiple CT12 continuation steps. -/
noncomputable def singletonProfile :
    CT12.DisjointPacking.Profile (Fin 3) (Fin 3) where
  vertices := inferInstance
  finiteItems := inferInstance
  support := fun item => {item}
  representative := id
  representative_mem := by simp

private def allItemsPacking : singletonProfile.Packing := by
  refine ⟨Finset.univ, ?_⟩
  intro left _ right _ different
  change Disjoint ({left} : Finset (Fin 3)) {right}
  simpa [Finset.disjoint_singleton] using different

theorem singleton_values_length : singletonProfile.values.length = 3 := by
  have lower : 3 ≤ singletonProfile.values.length := by
    have maximum := singletonProfile.maximum_spec allItemsPacking
    rw [← singletonProfile.values_length] at maximum
    simpa [allItemsPacking] using maximum
  have upper := singletonProfile.values_length_le_vertices
  norm_num at upper
  omega

noncomputable def singletonRun := singletonProfile.run context

example : singletonRun.terminal = .exhausted :=
  singletonProfile.run_terminal_exhausted context

example : singletonRun.iterations = 3 := by
  change (singletonProfile.run context).iterations = 3
  rw [singletonProfile.run_iterations_eq_values context,
    singleton_values_length]

example : singletonRun.trace.length ≤ 4 * 3 + 3 :=
  singletonProfile.run_trace_le_vertices context

end StructuralExhaustion.Examples.CT12DisjointPacking
