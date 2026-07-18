import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Graph.FiniteActiveInterfaceD7Response

namespace StructuralExhaustion.Graph.FiniteActiveInterfaceD7Signature

open StructuralExhaustion

universe u

/-!
# The complete declared D7 signature on one finite active interface

This is clause (D7) of the manuscript, without an ambient-context search.
The five summands retain their labels even when their embedded values happen
to coincide.  The final subtype performs the manuscript's sole restriction:
the complete declared support must lie in the supplied active interface.
-/

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

abbrev Slot := SurplusPortActivation.Slot setup

/-- An activated slot whose stored response is literally the open branch. -/
def IsOpen (slot : Slot (setup := setup)) : Prop :=
  ∃ (isOpen : SurplusPortActivity.portType ctx.G.object
      setup.deletionCritical slot = .open)
    (response : SurplusPortActivation.OpenResponse setup slot isOpen),
    (stage.demand slot).response = .open isOpen response

/-- An activated slot whose stored response is literally the triangular branch. -/
def IsTriangular (slot : Slot (setup := setup)) : Prop :=
  ∃ (isTriangular : SurplusPortActivity.portType ctx.G.object
      setup.deletionCritical slot = .triangular)
    (returnStage : TriangularPortReturn.VerifiedStage
      (SurplusPortActivation.triangularSetup setup slot)
      (SurplusPortActivation.triangularPort setup slot isTriangular)
      (SurplusPortActivation.rootReturn setup slot)
      (input.fixedContext ctx).avoids),
    (stage.demand slot).response = .triangular isTriangular returnStage

noncomputable def isOpenDecidable (slot : Slot (setup := setup)) :
    Decidable (IsOpen stage slot) := Classical.propDecidable _

noncomputable def isTriangularDecidable (slot : Slot (setup := setup)) :
    Decidable (IsTriangular stage slot) := Classical.propDecidable _

abbrev OpenSlot := {slot : Slot (setup := setup) // IsOpen stage slot}
abbrev TriangularSlot :=
  {slot : Slot (setup := setup) // IsTriangular stage slot}

@[implicit_reducible]
noncomputable def openSlots : FinEnum (OpenSlot stage) :=
  Core.Enumeration.subtype
    (SurplusPairResponse.slotEnumeration (setup := setup))
    (IsOpen stage) (isOpenDecidable stage)

@[implicit_reducible]
noncomputable def triangularSlots : FinEnum (TriangularSlot stage) :=
  Core.Enumeration.subtype
    (SurplusPairResponse.slotEnumeration (setup := setup))
    (IsTriangular stage) (isTriangularDecidable stage)

/-- Five disjoint labels, in the order in which clause (D7) declares them.
The triangular coordinate's value retains both its literal triangle and its
proof-carrying return stage; the stage is evidence, not an extra D7 label. -/
abbrev RawCoordinate :=
  Slot (setup := setup) ⊕
  (Slot (setup := setup) ⊕
  (OpenSlot stage ⊕
  (TriangularSlot stage ⊕ SurplusPairResponse.FreePair stage)))

@[implicit_reducible]
noncomputable def rawCoordinates : FinEnum (RawCoordinate stage) := by
  letI : FinEnum (Slot (setup := setup)) :=
    SurplusPairResponse.slotEnumeration (setup := setup)
  letI : FinEnum (OpenSlot stage) := openSlots stage
  letI : FinEnum (TriangularSlot stage) := triangularSlots stage
  letI : FinEnum (SurplusPairResponse.FreePair stage) :=
    SurplusPairResponse.freePairEnumeration stage
  exact inferInstance

noncomputable def openIsOpen (slot : OpenSlot stage) :=
  Classical.choose slot.2

noncomputable def openResponse (slot : OpenSlot stage) :=
  Classical.choose (Classical.choose_spec slot.2)

theorem openResponse_exact (slot : OpenSlot stage) :
    (stage.demand slot.1).response =
      .open (openIsOpen stage slot) (openResponse stage slot) :=
  Classical.choose_spec (Classical.choose_spec slot.2)

noncomputable def triangularIsTriangular
    (slot : TriangularSlot stage) :=
  Classical.choose slot.2

noncomputable def triangularReturnStage
    (slot : TriangularSlot stage) :=
  Classical.choose (Classical.choose_spec slot.2)

theorem triangularReturnStage_exact (slot : TriangularSlot stage) :
    (stage.demand slot.1).response = .triangular
      (triangularIsTriangular stage slot)
      (triangularReturnStage stage slot) :=
  Classical.choose_spec (Classical.choose_spec slot.2)

/-- Exact vertex support attached to each declared D7 label. -/
noncomputable def support (coordinate : RawCoordinate stage) :
    Finset ctx.G.Vertex := by
  classical
  exact match coordinate with
  | .inl slot => SurplusPortActivation.PortSupport setup slot
  | .inr (.inl slot) =>
      SurplusPortActivation.PortSupport setup slot ∪
        (SurplusPortActivation.rootReturn setup slot).path.support.toFinset
  | .inr (.inr (.inl slot)) =>
      SurplusPortActivation.PortSupport setup slot.1 ∪
        (openResponse stage slot).path.support.toFinset
  | .inr (.inr (.inr (.inl slot))) =>
      SurplusPortActivation.PortSupport setup slot.1 ∪
        (SurplusPortActivation.triangle setup slot.1
          (triangularIsTriangular stage slot)).support.toFinset
  | .inr (.inr (.inr (.inr pair))) => pair.support stage

/- A supplied finite interface restricts all six families in exactly the
same support-containment sense. -/
variable (interface : FiniteActiveInterfaceD7Response.Interface (ctx := ctx))

def SupportContained (coordinate : RawCoordinate stage) : Prop :=
  support stage coordinate ⊆ interface.support

noncomputable def supportContainedDecidable (coordinate : RawCoordinate stage) :
    Decidable (SupportContained stage interface coordinate) := by
  classical
  unfold SupportContained
  infer_instance

abbrev Coordinate :=
  {coordinate : RawCoordinate stage // SupportContained stage interface coordinate}

@[implicit_reducible]
noncomputable def coordinates : FinEnum (Coordinate stage interface) :=
  Core.Enumeration.subtype (rawCoordinates stage)
    (SupportContained stage interface)
    (supportContainedDecidable stage interface)

theorem coordinate_support_subset (coordinate : Coordinate stage interface) :
    support stage coordinate.1 ⊆ interface.support := coordinate.2

theorem coordinate_support_card_le (coordinate : Coordinate stage interface) :
    (support stage coordinate.1).card ≤ interface.bound :=
  (Finset.card_le_card coordinate.2).trans interface.card_le

/-- Heterogeneous exact values stored by clause (D7).  Constructors retain
the source label as well as the complete proof-carrying object; hence equal
numerical observations from different labels are never identified. -/
inductive ExactValue where
  | selectedPort (slot : Slot (setup := setup))
      (support : Finset ctx.G.Vertex)
  | rootReturn (slot : Slot (setup := setup))
      (root : DartReturn ctx.G.object.graph
        (SurplusPortActivation.rootDart setup slot))
      (edges : Finset (Sym2 ctx.G.Vertex))
  | openSuppression (slot : OpenSlot stage)
      (path : ctx.G.object.graph.Walk
        (SurplusPortActivity.firstShoulder ctx.G.object slot.1
          setup.deletionCritical)
        (SurplusPortActivity.secondShoulder ctx.G.object slot.1
          setup.deletionCritical))
  | triangularResponse (slot : TriangularSlot stage)
      (triangle : ctx.G.object.graph.Walk
        (SurplusPortActivity.portEndpoint ctx.G.object slot.1)
        (SurplusPortActivity.portEndpoint ctx.G.object slot.1))
      (returnStage : TriangularPortReturn.VerifiedStage
        (SurplusPortActivation.triangularSetup setup slot.1)
        (SurplusPortActivation.triangularPort setup slot.1
          (triangularIsTriangular stage slot))
        (SurplusPortActivation.rootReturn setup slot.1)
        (input.fixedContext ctx).avoids)
  | sparsePairResponse (pair : SurplusPairResponse.FreePair stage)
      (response : Bool)

/-- Exact D7 value for one labelled coordinate and one supplied context.
No family of contexts and no Boolean cube is enumerated. -/
noncomputable def exactValue (coordinate : RawCoordinate stage)
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex) :
    ExactValue stage :=
  match coordinate with
  | .inl slot => .selectedPort slot
      (SurplusPortActivation.PortSupport setup slot)
  | .inr (.inl slot) => .rootReturn slot
      (SurplusPortActivation.rootReturn setup slot)
      (SurplusPortActivation.ActiveDemand.rootReturnEdges setup slot)
  | .inr (.inr (.inl slot)) => .openSuppression slot
      (openResponse stage slot).path
  | .inr (.inr (.inr (.inl slot))) =>
      .triangularResponse slot
        (SurplusPortActivation.triangle setup slot.1
          (triangularIsTriangular stage slot))
        (triangularReturnStage stage slot)
  | .inr (.inr (.inr (.inr pair))) =>
      .sparsePairResponse pair
        ((SurplusPairResponse.responseProfile stage).responseSystem.response
          pair outside)

/-- Exhaustiveness is inherited from the exact source enumeration and the
single support filter. -/
theorem mem_coordinates_iff (coordinate : RawCoordinate stage) :
    (∃ proof, (⟨coordinate, proof⟩ : Coordinate stage interface) ∈
      (coordinates stage interface).orderedValues) ↔
      SupportContained stage interface coordinate := by
  constructor
  · rintro ⟨proof, _⟩
    exact proof
  · intro contained
    exact ⟨contained, FinEnum.mem_orderedValues
      (coordinates stage interface) _⟩

/-- The executable work is one containment test per declared coordinate. -/
noncomputable def checks : Nat := (rawCoordinates stage).card

theorem coordinates_card_le_checks :
    (coordinates stage interface).card ≤ checks stage :=
  Core.Enumeration.subtype_card_le (rawCoordinates stage)
    (SupportContained stage interface)
    (supportContainedDecidable stage interface)

theorem openSlots_card_le_slots :
    (openSlots stage).card ≤
      (SurplusPairResponse.slotEnumeration (setup := setup)).card :=
  Core.Enumeration.subtype_card_le
    (SurplusPairResponse.slotEnumeration (setup := setup))
    (IsOpen stage) (isOpenDecidable stage)

theorem triangularSlots_card_le_slots :
    (triangularSlots stage).card ≤
      (SurplusPairResponse.slotEnumeration (setup := setup)).card :=
  Core.Enumeration.subtype_card_le
    (SurplusPairResponse.slotEnumeration (setup := setup))
    (IsTriangular stage) (isTriangularDecidable stage)

theorem rawCoordinates_card :
    (rawCoordinates stage).card =
      (SurplusPairResponse.slotEnumeration (setup := setup)).card +
      ((SurplusPairResponse.slotEnumeration (setup := setup)).card +
      ((openSlots stage).card + ((triangularSlots stage).card +
      (SurplusPairResponse.freePairEnumeration stage).card))) := by
  let slotEnum := SurplusPairResponse.slotEnumeration (setup := setup)
  let openEnum := openSlots stage
  let triangularEnum := triangularSlots stage
  let pairEnum := SurplusPairResponse.freePairEnumeration stage
  letI : FinEnum (Slot (setup := setup)) := slotEnum
  letI : FinEnum (OpenSlot stage) := openEnum
  letI : FinEnum (TriangularSlot stage) := triangularEnum
  letI : FinEnum (SurplusPairResponse.FreePair stage) := pairEnum
  let sumEnum : FinEnum (RawCoordinate stage) := inferInstance
  calc
    (rawCoordinates stage).card = sumEnum.card :=
      FinEnum.card_unique (rawCoordinates stage) sumEnum
    _ = Fintype.card (RawCoordinate stage) :=
      @FinEnum.card_eq_fintypeCard _ sumEnum inferInstance
    _ = Fintype.card (Slot (setup := setup)) +
        (Fintype.card (Slot (setup := setup)) +
        (Fintype.card (OpenSlot stage) +
        (Fintype.card (TriangularSlot stage) +
        Fintype.card (SurplusPairResponse.FreePair stage)))) := by
      simp only [Fintype.card_sum]
    _ = _ := by
      rw [← @FinEnum.card_eq_fintypeCard _ slotEnum inferInstance,
        ← @FinEnum.card_eq_fintypeCard _ openEnum inferInstance,
        ← @FinEnum.card_eq_fintypeCard _ triangularEnum inferInstance,
        ← @FinEnum.card_eq_fintypeCard _ pairEnum inferInstance]

/-- Four slot-indexed passes (two unconditional, one open, one triangular)
and one pass over the already produced sparse-pair schedule suffice. -/
theorem checks_le_four_slots_add_pairs :
    checks stage ≤
      4 * (SurplusPairResponse.slotEnumeration (setup := setup)).card +
      (SurplusPairResponse.freePairEnumeration stage).card := by
  rw [checks, rawCoordinates_card stage]
  have openLe := openSlots_card_le_slots stage
  have triangularLe := triangularSlots_card_le_slots stage
  omega

theorem freePairs_card_le_pairs :
    (SurplusPairResponse.freePairEnumeration stage).card ≤
      (SurplusPairResponse.pairEnumeration (setup := setup)).card := by
  have partition := SurplusPairResponse.blocked_card_add_free_card stage
  omega

/-- Polynomial audit for the complete D7 scan.  It combines the five local
slot passes with the already verified quartic sparse-pair schedule. -/
theorem checks_le_polynomial :
    checks stage ≤ 4 * ctx.G.object.input.vertices.card ^ 2 +
      ctx.G.object.input.vertices.card ^ 4 := by
  calc
    checks stage ≤
        4 * (SurplusPairResponse.slotEnumeration (setup := setup)).card +
          (SurplusPairResponse.freePairEnumeration stage).card :=
      checks_le_four_slots_add_pairs stage
    _ ≤ 4 * ctx.G.object.input.vertices.card ^ 2 +
          (SurplusPairResponse.pairEnumeration (setup := setup)).card := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_left 4
          (SurplusPortActivity.portSlots_card_le_square ctx.G.object))
        (freePairs_card_le_pairs stage)
    _ ≤ 4 * ctx.G.object.input.vertices.card ^ 2 +
          ctx.G.object.input.vertices.card ^ 4 :=
      Nat.add_le_add_left
        (SurplusPairResponse.pairEnumeration_card_le_fourthPower
          (input := input) (ctx := ctx) (setup := setup)) _

end StructuralExhaustion.Graph.FiniteActiveInterfaceD7Signature
