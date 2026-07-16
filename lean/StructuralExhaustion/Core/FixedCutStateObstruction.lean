import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace StructuralExhaustion.Core.FixedCutStateObstruction

/-!
# Obstructions to an ambient-independent cut-state universe

These elementary facts isolate two representation errors which must be ruled
out before a finite-state corridor pigeonhole is sound.

* Actual endpoint identities cannot be fields of the state code: two endpoint
  identities already give `|V|^2` states.
* An unrestricted connector length cannot be a field of a finite state code:
  it contains an injective copy of `Nat`.

They do not say that a fixed cut-state quotient is impossible.  They say that
the quotient, its bounded fields, and its response-completeness theorem have
to be constructed explicitly; raw ambient data are not such a quotient.
-/

/-- The representation obtained by storing the two actual active interface
vertices.  This is deliberately an abbreviation: its exact cardinality is
the ordinary product cardinality. -/
abbrev RawTwoInterface (V : Type*) := V × V

theorem rawTwoInterface_card (V : Type*) [Fintype V] :
    Fintype.card (RawTwoInterface V) = Fintype.card V * Fintype.card V := by
  exact Fintype.card_prod V V

/-- There is no ambient-independent cardinal bound for a representation
which stores two actual vertex identities. -/
theorem rawTwoInterface_exceeds (bound : Nat) :
    bound < Fintype.card (RawTwoInterface (Fin (bound + 1))) := by
  rw [rawTwoInterface_card]
  simp only [Fintype.card_fin]
  nlinarith

/-- The raw D2 field obtained by retaining an unrestricted connector length. -/
structure RawConnectorLength where
  connectorLength : Nat
  deriving DecidableEq

/-- Every natural connector length is represented by a distinct raw state. -/
def connectorLengthEmbedding : Nat ↪ RawConnectorLength where
  toFun length := ⟨length⟩
  inj' := by
    intro left right equal
    exact congrArg RawConnectorLength.connectorLength equal

instance : Infinite RawConnectorLength :=
  Infinite.of_injective connectorLengthEmbedding
    connectorLengthEmbedding.injective

/-- In particular, the raw connector-length representation admits no finite
enumeration at all. -/
theorem rawConnectorLength_not_fintype :
    ¬Nonempty (Fintype RawConnectorLength) := by
  intro alleged
  letI : Fintype RawConnectorLength := alleged.some
  exact not_finite RawConnectorLength

theorem connectorLengthEmbedding_apply (length : Nat) :
    (connectorLengthEmbedding length).connectorLength = length := rfl

/-- Any proposed numerical bound is exceeded by a raw connector-length
state.  Thus this field must be capped or quotient-coded before the state
type can have a fixed finite cardinality. -/
theorem rawConnectorLength_exceeds (bound : Nat) :
    ∃ state : RawConnectorLength, bound < state.connectorLength := by
  refine ⟨connectorLengthEmbedding (bound + 1), ?_⟩
  change bound < bound + 1
  omega

/-- Combining the two raw fields does not repair either obstruction. -/
structure RawD1D2State (V : Type*) where
  active : RawTwoInterface V
  connectorLength : Nat

def d1d2LengthEmbedding (V : Type*) (active : RawTwoInterface V) :
    Nat ↪ RawD1D2State V where
  toFun length := ⟨active, length⟩
  inj' := by
    intro left right equal
    exact congrArg RawD1D2State.connectorLength equal

theorem rawD1D2_infinite (V : Type*) (active : RawTwoInterface V) :
    Infinite (RawD1D2State V) :=
  Infinite.of_injective (d1d2LengthEmbedding V active)
    (d1d2LengthEmbedding V active).injective

theorem rawD1D2_exceeds (V : Type*) (active : RawTwoInterface V)
    (bound : Nat) :
    ∃ state : RawD1D2State V, bound < state.connectorLength := by
  refine ⟨d1d2LengthEmbedding V active (bound + 1), ?_⟩
  change bound < bound + 1
  omega

end StructuralExhaustion.Core.FixedCutStateObstruction
