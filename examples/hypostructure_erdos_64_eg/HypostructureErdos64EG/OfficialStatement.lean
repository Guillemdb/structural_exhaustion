import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace HypostructureErdos64EG

/-!
Exact right-hand side of `Erdos64.erdos_64` from Google DeepMind's
`formal-conjectures`, pinned at commit
`bcaee6031a085e19432540650e1039b7fd1cea36`.

The pinned source file has SHA-256
`8c06a914de2b5904420a1aff861dd0a6db4abef7a52e6a6a3fcbd8b1784265b2`.

The pinned statement remains in Mathlib's `SimpleGraph` vocabulary. The
Hypostructure application bridges its packed finite graph to this declaration
instead of replacing the public proposition with an application-specific one.
-/

/-- Official mathematical proposition for Erdős Problem 64. -/
def OfficialStatement : Prop :=
  ∀ (V : Type*) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.minDegree ≥ 3 →
      ∃ (k : Nat) (v : V) (c : G.Walk v v),
        k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k

end HypostructureErdos64EG
