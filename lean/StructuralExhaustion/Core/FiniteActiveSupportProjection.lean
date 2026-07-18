import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Core.FiniteDeclaredSupportLedger

namespace StructuralExhaustion.Core.FiniteActiveSupportProjection

universe uEntry uVertex

/-!
# Finite active-interface projections of produced supports

The profile indexes an already produced list rather than enumerating an
ambient family.  For one finite active interface it exposes exactly the list
entries whose declared supports are contained in that interface.  Endpoint
recognition still scans the complete produced list: entering any previously
declared support is a handoff, even when the remainder of that support lies
outside the current interface.
-/

structure Profile (Entry : Type uEntry) (Vertex : Type uVertex) where
  entries : List Entry
  vertexDecEq : DecidableEq Vertex
  support : Entry → Finset Vertex

namespace Profile

variable {Entry : Type uEntry} {Vertex : Type uVertex}
variable (profile : Profile Entry Vertex)

abbrev Key := Fin profile.entries.length

def entry (key : profile.Key) : Entry := profile.entries.get key

@[implicit_reducible] noncomputable def keys : FinEnum profile.Key :=
  FinEnum.fin

def SupportedIn (active : Finset Vertex) (key : profile.Key) : Prop :=
  profile.support (profile.entry key) ⊆ active

noncomputable def supportedInDecidable (active : Finset Vertex)
    (key : profile.Key) : Decidable (profile.SupportedIn active key) := by
  letI : DecidableEq Vertex := profile.vertexDecEq
  unfold SupportedIn
  infer_instance

abbrev ActiveKey (active : Finset Vertex) :=
  {key : profile.Key // profile.SupportedIn active key}

/-- Exactly the produced keys whose complete support lies in `active`. -/
@[implicit_reducible] noncomputable def activeKeys (active : Finset Vertex) :
    FinEnum (profile.ActiveKey active) :=
  Core.Enumeration.subtype profile.keys (profile.SupportedIn active)
    (profile.supportedInDecidable active)

theorem mem_activeKeys_iff (active : Finset Vertex) (key : profile.Key) :
    profile.SupportedIn active key ↔
      ∃ activeKey : profile.ActiveKey active, activeKey.1 = key := by
  constructor
  · intro contained
    exact ⟨⟨key, contained⟩, rfl⟩
  · rintro ⟨activeKey, rfl⟩
    exact activeKey.2

theorem activeKey_support_subset (active : Finset Vertex)
    (key : profile.ActiveKey active) :
    profile.support (profile.entry key.1) ⊆ active :=
  key.2

/-- The declared-support recognizer over the literal produced-entry order. -/
noncomputable def declaredProfile :
    Core.FiniteDeclaredSupportLedger.Profile profile.Key Vertex where
  keys := profile.keys
  vertexDecEq := profile.vertexDecEq
  support key := profile.support (profile.entry key)

abbrev Hit (vertex : Vertex) := profile.declaredProfile.Hit vertex

structure CompleteAt (vertex : Vertex) : Prop where
  endpointOutside : ∀ key : profile.Key,
    vertex ∉ profile.support (profile.entry key)

inductive EndpointResult (vertex : Vertex) where
  | hit (result : profile.Hit vertex)
  | complete (result : profile.CompleteAt vertex)

/-- First produced support containing `vertex`, or a proof that none does. -/
noncomputable def classifyEndpoint (vertex : Vertex) :
    profile.EndpointResult vertex := by
  cases result : Core.FiniteSearch.first profile.keys
      (fun key => vertex ∈ profile.support (profile.entry key))
      (fun key => by
        letI : DecidableEq Vertex := profile.vertexDecEq
        infer_instance) with
  | found first => exact .hit ⟨first⟩
  | absent none =>
      exact .complete ⟨fun key =>
        none key (profile.keys.mem_orderedValues key)⟩

theorem classifyEndpoint_total (vertex : Vertex) :
    (∃ hit, profile.classifyEndpoint vertex = .hit hit) ∨
      (∃ complete, profile.classifyEndpoint vertex = .complete complete) := by
  cases equation : profile.classifyEndpoint vertex with
  | hit result => exact Or.inl ⟨result, rfl⟩
  | complete result => exact Or.inr ⟨result, rfl⟩

theorem Hit.key_mem (vertex : Vertex) (hit : profile.Hit vertex) :
    hit.first.value ∈ profile.keys.orderedValues :=
  hit.first.member

theorem Hit.endpoint_mem_support (vertex : Vertex)
    (hit : profile.Hit vertex) :
    vertex ∈ profile.support (profile.entry hit.first.value) :=
  hit.first.holds

theorem Hit.no_earlier_support (vertex : Vertex)
    (hit : profile.Hit vertex) :
    ∀ key ∈ hit.first.before,
      vertex ∉ profile.support (profile.entry key) :=
  hit.first.beforeAbsent

def checks : Nat := profile.entries.length

theorem activeKeys_card_le_entries (active : Finset Vertex) :
    (profile.activeKeys active).card ≤ profile.entries.length := by
  have bound := Core.Enumeration.subtype_card_le profile.keys
    (profile.SupportedIn active) (profile.supportedInDecidable active)
  simpa [keys, FinEnum.card_eq_fintypeCard] using bound

end Profile

end StructuralExhaustion.Core.FiniteActiveSupportProjection
