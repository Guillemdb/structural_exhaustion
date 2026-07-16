import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Core.FiniteSequentialFiltration

universe u

/-!
# Exact finite sequential filtrations

This profile performs an ordered sequence of Boolean tests on one explicit
finite state universe.  At a barrier with declared safe and flat weights, the
retention inequality is

`safe * after.length ≤ flat * before.length`.

The reference runner decides that inequality itself.  It either returns the
first conditional fibre where it fails, together with successful evidence for
every earlier barrier, or a complete ledger.  A complete ledger telescopes to
the corresponding product inequality.  No realization, independence, or
caller-selected branch is part of this interface.
-/

/-- One ordered test and its declared retention weights. -/
structure Barrier (State : Type u) where
  accepts : State → Bool
  safe : Nat
  flat : Nat

/-- The states retained by one barrier. -/
def retain {State : Type u} (states : List State) (barrier : Barrier State) :
    List State :=
  states.filter barrier.accepts

/-- The exact weak inequality required for a successful filtration step. -/
def Pays {State : Type u} (states : List State) (barrier : Barrier State) : Prop :=
  barrier.safe * (retain states barrier).length ≤ barrier.flat * states.length

instance {State : Type u} (states : List State) (barrier : Barrier State) :
    Decidable (Pays states barrier) :=
  decidable_of_iff
    (barrier.safe * (retain states barrier).length ≤
      barrier.flat * states.length) (by rfl)

/-- The complementary strict inequality, used as the executable failure
predicate. -/
def Fails {State : Type u} (states : List State) (barrier : Barrier State) : Prop :=
  barrier.flat * states.length < barrier.safe * (retain states barrier).length

instance {State : Type u} (states : List State) (barrier : Barrier State) :
    Decidable (Fails states barrier) :=
  decidable_of_iff
    (barrier.flat * states.length <
      barrier.safe * (retain states barrier).length) (by rfl)

/-- A complete proof-carrying run through all remaining barriers. -/
inductive CompleteLedger {State : Type u} :
    (states : List State) → (barriers : List (Barrier State)) → Type u
  | nil (states : List State) : CompleteLedger states []
  | cons {states : List State} {barrier : Barrier State}
      {barriers : List (Barrier State)}
      (pays : Pays states barrier)
      (tail : CompleteLedger (retain states barrier) barriers) :
      CompleteLedger states (barrier :: barriers)

/-- The first failing fibre.  Every `later` constructor records that the
preceding barrier paid before the recursive first failure was reached. -/
inductive FirstFailure {State : Type u} :
    (states : List State) → (barriers : List (Barrier State)) → Type u
  | here {states : List State} {barrier : Barrier State}
      {barriers : List (Barrier State)}
      (fails : Fails states barrier) :
      FirstFailure states (barrier :: barriers)
  | later {states : List State} {barrier : Barrier State}
      {barriers : List (Barrier State)}
      (pays : Pays states barrier)
      (failure : FirstFailure (retain states barrier) barriers) :
      FirstFailure states (barrier :: barriers)

/-- Exhaustive output of the reference filtration. -/
inductive Outcome {State : Type u}
    (states : List State) (barriers : List (Barrier State)) : Type u
  | firstFailure (failure : FirstFailure states barriers) :
      Outcome states barriers
  | complete (ledger : CompleteLedger states barriers) :
      Outcome states barriers

/-- Pure reference interpreter.  Its recursive structure makes the failure
index canonical: recursion can proceed past a barrier only with a proof that
the barrier paid. -/
def runFrom {State : Type u} (states : List State) :
    (barriers : List (Barrier State)) → Outcome states barriers
  | [] => .complete (.nil states)
  | barrier :: barriers =>
      if fails : Fails states barrier then
        .firstFailure (.here fails)
      else
        have pays : Pays states barrier := Nat.le_of_not_gt fails
        match runFrom (retain states barrier) barriers with
        | .firstFailure failure => .firstFailure (.later pays failure)
        | .complete ledger => .complete (.cons pays ledger)

/-- A reusable profile starts from an exact `FinEnum`; the observable state
order is inherited from that enumeration. -/
structure Profile where
  State : Type u
  states : FinEnum State
  barriers : List (Barrier State)

namespace Profile

/-- Execute the exact ordered filtration. -/
def run (profile : Profile.{u}) :
    Outcome profile.states.orderedValues profile.barriers :=
  runFrom profile.states.orderedValues profile.barriers

def safeProduct (profile : Profile.{u}) : Nat :=
  (profile.barriers.map Barrier.safe).prod

def flatProduct (profile : Profile.{u}) : Nat :=
  (profile.barriers.map Barrier.flat).prod

end Profile

namespace CompleteLedger

/-- Exact terminal state list of a successful run. -/
def finalStates {State : Type u} {states : List State} :
    {barriers : List (Barrier State)} →
      CompleteLedger states barriers → List State
  | [], .nil _ => states
  | _ :: _, .cons _ tail => tail.finalStates

/-- Every successful run telescopes its stepwise retention inequalities. -/
theorem product_le {State : Type u} {states : List State}
    {barriers : List (Barrier State)}
    (ledger : CompleteLedger states barriers) :
    (barriers.map Barrier.safe).prod * ledger.finalStates.length ≤
      (barriers.map Barrier.flat).prod * states.length := by
  induction ledger with
  | nil states => simp [finalStates]
  | @cons states barrier barriers pays tail ih =>
      simp only [List.map_cons, List.prod_cons, finalStates]
      have first := Nat.mul_le_mul_left barrier.safe ih
      have second := Nat.mul_le_mul_right
        (barriers.map Barrier.flat).prod pays
      exact le_trans
        (by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using first)
        (by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using second)

/-- Every terminal list remains a literal sublist of the initial finite state
list. -/
theorem finalStates_sublist {State : Type u} {states : List State}
    {barriers : List (Barrier State)}
    (ledger : CompleteLedger states barriers) :
    List.Sublist ledger.finalStates states := by
  induction ledger with
  | nil states => exact List.Sublist.refl _
  | @cons states barrier barriers pays tail ih =>
      exact ih.trans (List.filter_sublist)

end CompleteLedger

namespace FirstFailure

/-- Zero-based position of the first failing barrier. -/
def index {State : Type u} {states : List State}
    {barriers : List (Barrier State)}
    (failure : FirstFailure states barriers) : Nat :=
  match failure with
  | .here _ => 0
  | .later _ tail => tail.index + 1

/-- The explicit conditional fibre immediately before the first failure. -/
def beforeStates {State : Type u} {states : List State}
    {barriers : List (Barrier State)}
    (failure : FirstFailure states barriers) : List State :=
  match failure with
  | .here _ => states
  | .later _ tail => tail.beforeStates

/-- The first barrier that fails. -/
def barrier {State : Type u} {states : List State}
    {barriers : List (Barrier State)}
    (failure : FirstFailure states barriers) : Barrier State :=
  match failure with
  | .here (barrier := barrier) _ => barrier
  | .later _ tail => tail.barrier

/-- The explicit conditional fibre after the first failing test. -/
def afterStates {State : Type u} {states : List State}
    {barriers : List (Barrier State)}
    (failure : FirstFailure states barriers) : List State :=
  retain failure.beforeStates failure.barrier

theorem fails {State : Type u} {states : List State}
    {barriers : List (Barrier State)}
    (failure : FirstFailure states barriers) :
    Fails failure.beforeStates failure.barrier := by
  induction failure with
  | here fails => exact fails
  | later _ failure ih => exact ih

/-- The failed fibre is genuinely a subset of its exact conditioning fibre. -/
theorem afterStates_sublist_beforeStates {State : Type u}
    {states : List State} {barriers : List (Barrier State)}
    (failure : FirstFailure states barriers) :
    List.Sublist failure.afterStates failure.beforeStates := by
  exact List.filter_sublist

end FirstFailure

/-- The executable runner has exactly the two advertised terminals. -/
theorem runFrom_exhaustive {State : Type u} (states : List State)
    (barriers : List (Barrier State)) :
    (∃ failure, runFrom states barriers = Outcome.firstFailure failure) ∨
      (∃ ledger, runFrom states barriers = Outcome.complete ledger) := by
  cases result : runFrom states barriers with
  | firstFailure failure => exact Or.inl ⟨failure, rfl⟩
  | complete ledger => exact Or.inr ⟨ledger, rfl⟩

end StructuralExhaustion.Core.FiniteSequentialFiltration
