namespace StructuralExhaustion.Core

universe u

/-!
# Opaque witnesses for expensive certified constructions

Downstream CTs should consume an already-certified finite construction
symbolically.  This helper prevents the elaborator from normalizing that
construction again; it changes neither its type nor its proof provenance.
-/

/-- Select a witness from an established nonempty type without exposing the
producer's implementation to downstream normalization. -/
noncomputable opaque cachedNonemptyWitness {α : Sort u} (available : Nonempty α) : α :=
  Classical.choice available

/-- Cache one exact expensive value without changing its identity. -/
@[irreducible] noncomputable def cachedValue {α : Sort u} (value : α) : α := value

/-- The cache is propositionally the exact supplied value. -/
theorem cachedValue_eq {α : Sort u} (value : α) : cachedValue value = value := by
  unfold cachedValue
  rfl

end StructuralExhaustion.Core
