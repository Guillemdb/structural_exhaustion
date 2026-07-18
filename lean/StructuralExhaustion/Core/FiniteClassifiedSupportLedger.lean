import StructuralExhaustion.Core.FiniteDeclaredSupportLedger
import StructuralExhaustion.Core.EnumerationCombinators

namespace StructuralExhaustion.Core.FiniteClassifiedSupportLedger

universe uKey uVertex uToken

/-!
# Charged-or-absent declared support ledgers

This is the branch-state object required before a later local corridor may
recognize an already declared handoff.  Every declared key is classified once:
it either carries its exact earlier charge token or its declared support is
proved empty.  The later recognizer scans only the charged subtype.
-/

structure Profile (Key : Type uKey) (Vertex : Type uVertex)
    (Token : Type uToken) where
  keys : FinEnum Key
  vertexDecEq : DecidableEq Vertex
  tokenDecEq : DecidableEq Token
  support : Key → Finset Vertex
  charge : Key → Option Token
  absent_support_empty : ∀ key, charge key = none → support key = ∅

namespace Profile

variable {Key : Type uKey} {Vertex : Type uVertex} {Token : Type uToken}
variable (profile : Profile Key Vertex Token)

def Carried (key : Key) : Prop := profile.charge key ≠ none

noncomputable def carriedDecidable (key : Key) : Decidable (profile.Carried key) := by
  unfold Carried
  letI : DecidableEq Token := profile.tokenDecEq
  infer_instance

abbrev CarriedKey := {key : Key // profile.Carried key}

@[implicit_reducible] noncomputable def carriedKeys : FinEnum profile.CarriedKey :=
  Core.Enumeration.subtype profile.keys profile.Carried profile.carriedDecidable

noncomputable def carriedToken (key : profile.CarriedKey) : Token := by
  exact Classical.choose (Option.ne_none_iff_exists.mp key.2)

theorem charge_carriedToken (key : profile.CarriedKey) :
    profile.charge key.1 = some (profile.carriedToken key) := by
  exact (Classical.choose_spec (Option.ne_none_iff_exists.mp key.2)).symm

/-- The exact declared-support recognizer restricted to keys already paid by
an earlier branch. -/
noncomputable def declaredProfile :
    Core.FiniteDeclaredSupportLedger.Profile profile.CarriedKey Vertex where
  keys := profile.carriedKeys
  vertexDecEq := profile.vertexDecEq
  support key := profile.support key.1

abbrev Hit (vertex : Vertex) := profile.declaredProfile.Hit vertex

noncomputable def recognize (vertex : Vertex) : Option (profile.Hit vertex) :=
  profile.declaredProfile.recognize vertex

theorem Hit.exact_key_mem (vertex : Vertex) (hit : profile.Hit vertex) :
    hit.first.value.1 ∈ profile.keys.orderedValues := by
  exact hit.first.value.2 |> fun _ =>
    profile.keys.mem_orderedValues hit.first.value.1

theorem Hit.endpoint_mem_exact_support (vertex : Vertex)
    (hit : profile.Hit vertex) :
    vertex ∈ profile.support hit.first.value.1 :=
  hit.endpoint_mem_support

theorem Hit.has_exact_charge_token (vertex : Vertex)
    (hit : profile.Hit vertex) :
    profile.charge hit.first.value.1 =
      some (profile.carriedToken hit.first.value) :=
  profile.charge_carriedToken hit.first.value

/-- An absent key can never be recognized: its support is literally empty,
not merely omitted from the charged scan. -/
theorem absent_key_support_empty (key : Key)
    (absent : profile.charge key = none) :
    profile.support key = ∅ :=
  profile.absent_support_empty key absent

theorem absent_key_endpoint_not_mem (key : Key) (vertex : Vertex)
    (absent : profile.charge key = none) :
    vertex ∉ profile.support key := by
  rw [profile.absent_key_support_empty key absent]
  simp

noncomputable def checks : Nat := profile.carriedKeys.card

theorem checks_le_declared : profile.checks ≤ profile.keys.card := by
  exact Core.Enumeration.subtype_card_le profile.keys profile.Carried
    profile.carriedDecidable

end Profile

end StructuralExhaustion.Core.FiniteClassifiedSupportLedger
