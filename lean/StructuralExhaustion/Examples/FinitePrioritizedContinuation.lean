import StructuralExhaustion.Core.FinitePrioritizedContinuation

namespace StructuralExhaustion.Examples.FinitePrioritizedContinuation

open StructuralExhaustion

abbrev Stage := Fin 2

noncomputable def stages : Core.OrderedCollection Stage :=
  (inferInstance : FinEnum Stage).toOrderedCollection

def F1 (stage : Stage) : Prop := stage = 0

def f1Decidable (stage : Stage) : Decidable (F1 stage) := by
  unfold F1
  infer_instance

def later : Core.FinitePrioritizedContinuation.LaterSemantics Stage F1 where
  F2 := fun stage => stage = 1
  F3 := fun _ => False
  F4 := fun _ => False
  f2Decidable := fun _ => inferInstance
  f3Decidable := fun _ => instDecidableFalse
  f4Decidable := fun _ => instDecidableFalse
  F2Data := Unit
  F3Data := Empty
  F4Data := Empty
  f2Data := fun _ _ => ()
  f3Data := fun _ impossible => False.elim impossible
  f4Data := fun _ impossible => False.elim impossible
  Germ := Unit
  germOfClear := fun _ _ => ()

noncomputable def transferProfile :=
  Core.FinitePrioritizedContinuation.profile stages F1 f1Decidable Unit
    (fun _ _ => ()) later

/-- A non-Erdős consumer executes the same public first-failure runner. -/
theorem transfer_total :
    (∃ hit data, transferProfile.run () = .first hit data) ∨
      (∃ noEvent data, transferProfile.run () = .germ noEvent data) :=
  transferProfile.run_total ()

theorem transfer_checks : transferProfile.checks () = 2 := by
  rfl

/-! The F5 constructor receives the negative F1 evidence as well as the three
later negatives.  This separate all-quiet fixture prevents an adapter from
silently dropping the first component again. -/

def QuietF1 (_stage : Stage) : Prop := False

structure QuietGerm : Type where
  schedule : List Stage
  f1Absent : ∀ stage, stage ∈ schedule → ¬QuietF1 stage

def quietLater :
    Core.FinitePrioritizedContinuation.LaterSemantics Stage QuietF1 where
  F2 := fun _ => False
  F3 := fun _ => False
  F4 := fun _ => False
  f2Decidable := fun _ => instDecidableFalse
  f3Decidable := fun _ => instDecidableFalse
  f4Decidable := fun _ => instDecidableFalse
  F2Data := Empty
  F3Data := Empty
  F4Data := Empty
  f2Data := fun _ impossible => False.elim impossible
  f3Data := fun _ impossible => False.elim impossible
  f4Data := fun _ impossible => False.elim impossible
  Germ := QuietGerm
  germOfClear := fun schedule clear =>
    ⟨schedule, fun stage member => (clear stage member).1⟩

noncomputable def quietProfile :=
  Core.FinitePrioritizedContinuation.profile stages QuietF1
    (fun _ => instDecidableFalse) Empty
    (fun _ impossible => False.elim impossible) quietLater

theorem quiet_germ_retains_f1_absence :
    ∃ noEvent data, quietProfile.run () = .germ noEvent data := by
  rcases quietProfile.run_total () with first | germ
  · rcases first with ⟨hit, data, exactRun⟩
    cases data with
    | f1 proof _ => exact False.elim proof
    | f2 _ proof _ => exact False.elim proof
    | f3 _ _ proof _ => exact False.elim proof
    | f4 _ _ _ proof _ => exact False.elim proof
  · exact germ

end StructuralExhaustion.Examples.FinitePrioritizedContinuation
