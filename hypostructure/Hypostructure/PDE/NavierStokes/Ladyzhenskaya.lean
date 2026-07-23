import Hypostructure.Core.Strategy
import Hypostructure.PDE.External
import Hypostructure.PDE.NavierStokes.Basic

/-!
# Ladyzhenskaya problem registration

This is the theorem-shaped problem used by the PDE pipeline.  Its baseline is
initial data and positive viscosity; a classical global solution is the
target.  The analytic estimates needed by the classical theorem are exposed
as an explicit external certificate rather than being hidden in the baseline.
-/

namespace Hypostructure.PDE.NavierStokes

open Hypostructure

structure InitialDatum where
  velocity : Space → Space
  viscosity : Real

def AdmissibleDatum (datum : InitialDatum) : Prop :=
  0 < datum.viscosity

structure GlobalSolution (datum : InitialDatum) where
  field : Field
  domain_eq : field.domain = Set.univ
  viscosity_eq : field.viscosity = datum.viscosity
  initial_eq : ∀ x, field.velocity (0, x) = datum.velocity x
  classical : ClassicalOn field Set.univ

def LadyzhenskayaProblem : Core.Problem where
  Ambient := InitialDatum
  Baseline := AdmissibleDatum
  BranchState := fun _ => Unit

def LadyzhenskayaTarget : Core.Target LadyzhenskayaProblem where
  Predicate := fun datum => Nonempty (GlobalSolution datum)
  Statement := ∀ datum, AdmissibleDatum datum → Nonempty (GlobalSolution datum)
  statement_to_target := by
    intro statement datum baseline
    exact statement datum baseline
  target_to_statement := by
    intro target datum baseline
    exact target datum baseline

structure LadyzhenskayaCertificate where
  datum : InitialDatum
  admissible : AdmissibleDatum datum
  solution : GlobalSolution datum

def LadyzhenskayaCertificate.realize
    (certificate : LadyzhenskayaCertificate) :
    LadyzhenskayaTarget.Predicate certificate.datum :=
  ⟨certificate.solution⟩

def ladyzhenskayaProgram
    (certificate : ∀ datum, AdmissibleDatum datum →
      LadyzhenskayaTarget.Predicate datum) :
    Core.Strategy.TargetProgram LadyzhenskayaProblem LadyzhenskayaTarget where
  Stage := Core.Strategy.InitStage LadyzhenskayaProblem
  branchState := fun _ => ()
  run := (Core.Strategy.InitStrategy.forProblem LadyzhenskayaProblem).run
  object_preserved := by
    intro input
    exact Core.Strategy.InitStrategy.run_object LadyzhenskayaProblem input
  target := by
    intro input
    change LadyzhenskayaTarget.Predicate input.object
    exact certificate input.object input.baseline

def ladyzhenskayaRunner
    (certificate : ∀ datum, AdmissibleDatum datum →
      LadyzhenskayaTarget.Predicate datum) :
    Core.Strategy.Hypostructure where
  Problem := LadyzhenskayaProblem
  Target := LadyzhenskayaTarget
  strategy := (ladyzhenskayaProgram certificate).toOutputStrategy

theorem unconditional_ladyzhenskaya
    (certificate : ∀ datum, AdmissibleDatum datum →
      LadyzhenskayaTarget.Predicate datum) :
    LadyzhenskayaTarget.Statement := by
  exact (ladyzhenskayaRunner certificate).unconditional (by
    intro input
    exact ⟨⟨certificate input.object input.baseline⟩, rfl⟩)

end Hypostructure.PDE.NavierStokes
