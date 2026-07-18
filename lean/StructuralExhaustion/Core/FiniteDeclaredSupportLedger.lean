import StructuralExhaustion.Core.FiniteSearch

namespace StructuralExhaustion.Core.FiniteDeclaredSupportLedger

universe uKey uVertex

/-!
# Exact declared-support ledger recognition

This is the reusable local operation behind a named-handoff test.  It scans
only the finite key schedule already carried by the branch state and returns
the exact existing key whose support contains the current endpoint.
-/

structure Profile (Key : Type uKey) (Vertex : Type uVertex) where
  keys : FinEnum Key
  vertexDecEq : DecidableEq Vertex
  support : Key → Finset Vertex

namespace Profile

variable {Key : Type uKey} {Vertex : Type uVertex}
variable (profile : Profile Key Vertex)

def Meets (vertex : Vertex) (key : Key) : Prop :=
  vertex ∈ profile.support key

noncomputable def meetsDecidable (vertex : Vertex) (key : Key) :
    Decidable (profile.Meets vertex key) := by
  letI : DecidableEq Vertex := profile.vertexDecEq
  unfold Meets
  exact profile.support key |>.decidableMem vertex

noncomputable def scan (vertex : Vertex) :=
  Core.FiniteSearch.first profile.keys (profile.Meets vertex)
    (profile.meetsDecidable vertex)

/-- A positive result retains the exact pre-existing key, its membership
proof, and absence of every earlier key in the declared ledger order. -/
structure Hit (vertex : Vertex) where
  first : Core.FiniteSearch.FirstHit profile.keys.orderedValues
    (profile.Meets vertex)

noncomputable def recognize (vertex : Vertex) : Option (profile.Hit vertex) :=
  match profile.scan vertex with
  | .found first => some ⟨first⟩
  | .absent _ => none

theorem Hit.key_mem (vertex : Vertex) (hit : profile.Hit vertex) :
    hit.first.value ∈ profile.keys.orderedValues :=
  hit.first.member

theorem Hit.endpoint_mem_support (vertex : Vertex)
    (hit : profile.Hit vertex) :
    vertex ∈ profile.support hit.first.value :=
  hit.first.holds

theorem Hit.no_earlier_key (vertex : Vertex) (hit : profile.Hit vertex) :
    ∀ key ∈ hit.first.before, vertex ∉ profile.support key :=
  hit.first.beforeAbsent

theorem recognize_some_exact (vertex : Vertex) (hit : profile.Hit vertex)
    (_equation : profile.recognize vertex = some hit) :
    vertex ∈ profile.support hit.first.value := by
  exact hit.endpoint_mem_support

noncomputable def checks : Nat := profile.keys.card

theorem checks_eq_key_card : profile.checks = profile.keys.card := rfl

end Profile

end StructuralExhaustion.Core.FiniteDeclaredSupportLedger
