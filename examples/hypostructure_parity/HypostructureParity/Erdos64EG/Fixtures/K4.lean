import HypostructureParity.Erdos64EG.TargetAlgebra
import HypostructureErdos64EG.Fixtures.K4

namespace HypostructureParity.Erdos64EG.Fixtures.K4

namespace Legacy

open StructuralExhaustion.Graph

abbrev Vertex := Fin 4

/-- The legacy finite wrapper around the same Mathlib complete graph. -/
def object : _root_.Erdos64EG.Internal.Object Vertex where
  graph := ⊤
  input := {
    vertices := inferInstance
    decideAdj := inferInstance
  }

/-- The literal legacy-side closed walk `0-1-2-3-0`. -/
def fourCycle : object.graph.Walk (0 : Vertex) 0 :=
  .cons (v := 1) (by simp [object])
    (.cons (v := 2) (by simp [object])
      (.cons (v := 3) (by simp [object])
        (.cons (v := 0) (by simp [object]) .nil)))

theorem fourCycle_length : fourCycle.length = 4 :=
  rfl

theorem fourCycle_isCycle : fourCycle.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
  decide

def fourCycleIsCycleDecidable : Decidable fourCycle.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
  infer_instance

theorem baseline : _root_.Erdos64EG.Internal.Baseline object := by
  change 3 ≤ (⊤ : SimpleGraph Vertex).minDegree
  simp

theorem vertexCount : object.input.vertices.card = 4 := by
  simp [FinEnum.card_eq_fintypeCard]

theorem edgeCount : object.edgeCount = 6 := by
  change (⊤ : SimpleGraph Vertex).edgeFinset.card = 6
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  decide

theorem minimumDegree : object.minDegree = 3 := by
  change (⊤ : SimpleGraph Vertex).minDegree = 3
  simp

def certificate :
    CycleWithLength object.graph
      _root_.Erdos64EG.Internal.PowerOfTwoLength where
  vertex := 0
  walk := fourCycle
  isCycle := fourCycle_isCycle
  length_ok := by
    simpa only [fourCycle_length] using
      _root_.Erdos64EG.Internal.powerOfTwoLength_four

theorem target : _root_.Erdos64EG.Internal.Target object :=
  ⟨certificate⟩

theorem powerOfTwoAccepted :
    _root_.Erdos64EG.Internal.PowerOfTwoLength fourCycle.length :=
  certificate.length_ok

theorem mersenneReturnAccepted :
    _root_.Erdos64EG.Internal.MersenneLength (fourCycle.length - 1) := by
  simpa [_root_.Erdos64EG.Internal.MersenneLength, fourCycle_length] using
    _root_.Erdos64EG.Internal.powerOfTwoLength_four

end Legacy

namespace Modern

abbrev fixture := HypostructureErdos64EG.Fixtures.K4.object

theorem vertexCount : fixture.vertexCount = 4 := by
  change (inferInstance : FinEnum (Fin 4)).card = 4
  simp [FinEnum.card_eq_fintypeCard]

theorem edgeCount : fixture.edgeCount = 6 := by
  change (⊤ : SimpleGraph (Fin 4)).edgeFinset.card = 6
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  decide

theorem minimumDegree : fixture.minDegree = 3 := by
  change (⊤ : SimpleGraph (Fin 4)).minDegree = 3
  simp

theorem powerOfTwoAccepted :
    HypostructureErdos64EG.PowerOfTwoLength
      HypostructureErdos64EG.Fixtures.K4.fourCycle.length :=
  HypostructureErdos64EG.Fixtures.K4.k4Certificate.length_ok

theorem mersenneReturnAccepted :
    HypostructureErdos64EG.MersenneLength
      (HypostructureErdos64EG.Fixtures.K4.fourCycle.length - 1) := by
  simpa [HypostructureErdos64EG.MersenneLength,
    HypostructureErdos64EG.Fixtures.K4.fourCycle_length] using
      HypostructureErdos64EG.powerOfTwoLength_four

end Modern

/-- A test-only relation saying that old and new wrappers represent the same
Mathlib graph. It deliberately does not convert either production object. -/
def RepresentsSameGraph
    (legacy : StructuralExhaustion.Graph.FiniteObject Legacy.Vertex)
    (modern : Hypostructure.Graph.FiniteObject) : Prop :=
  Nonempty (legacy.graph ≃g modern.graph)

theorem k4_representsSameGraph :
    RepresentsSameGraph Legacy.object Modern.fixture := by
  refine ⟨?_⟩
  change (⊤ : SimpleGraph (Fin 4)) ≃g (⊤ : SimpleGraph (Fin 4))
  exact SimpleGraph.Iso.refl

/-!
The observation contains only paper-visible finite data and executable target
codes. It contains neither implementation record, residual, ledger, nor proof
term.
-/

/-- Normal form used to compare the concrete K4 target witness. -/
structure Observation where
  vertexCount : Nat
  edgeCount : Nat
  minimumDegree : Nat
  witnessExponent : Nat
  witnessLength : Nat
  witnessIsCycle : Bool
  powerOfTwoAccepted : Bool
  mersenneReturnAccepted : Bool
  deriving DecidableEq, Repr

namespace Observation

@[ext]
theorem ext {left right : Observation}
    (vertexCount : left.vertexCount = right.vertexCount)
    (edgeCount : left.edgeCount = right.edgeCount)
    (minimumDegree : left.minimumDegree = right.minimumDegree)
    (witnessExponent : left.witnessExponent = right.witnessExponent)
    (witnessLength : left.witnessLength = right.witnessLength)
    (witnessIsCycle : left.witnessIsCycle = right.witnessIsCycle)
    (powerOfTwoAccepted :
      left.powerOfTwoAccepted = right.powerOfTwoAccepted)
    (mersenneReturnAccepted :
      left.mersenneReturnAccepted = right.mersenneReturnAccepted) :
    left = right := by
  cases left
  cases right
  simp_all

end Observation

/-- Legacy public data normalized to representation-independent values. -/
def legacyObservation : Observation where
  vertexCount := Legacy.object.input.vertices.card
  edgeCount := Legacy.object.edgeCount
  minimumDegree := Legacy.object.minDegree
  witnessExponent := 2
  witnessLength := Legacy.fourCycle.length
  witnessIsCycle := @decide Legacy.fourCycle.IsCycle
    Legacy.fourCycleIsCycleDecidable
  powerOfTwoAccepted := decide
    (_root_.Erdos64EG.Internal.PowerOfTwoLength Legacy.fourCycle.length)
  mersenneReturnAccepted := decide
    (_root_.Erdos64EG.Internal.MersenneLength (Legacy.fourCycle.length - 1))

/-- Hypostructure public data normalized to the same values. -/
def modernObservation : Observation where
  vertexCount := Modern.fixture.vertexCount
  edgeCount := Modern.fixture.edgeCount
  minimumDegree := Modern.fixture.minDegree
  witnessExponent := 2
  witnessLength :=
    HypostructureErdos64EG.Fixtures.K4.fourCycle.length
  witnessIsCycle := @decide
    HypostructureErdos64EG.Fixtures.K4.fourCycle.IsCycle
    (Hypostructure.Graph.isCycleDecidable
      (object := Modern.fixture)
      HypostructureErdos64EG.Fixtures.K4.fourCycle)
  powerOfTwoAccepted := decide
    (HypostructureErdos64EG.PowerOfTwoLength
      HypostructureErdos64EG.Fixtures.K4.fourCycle.length)
  mersenneReturnAccepted := decide
    (HypostructureErdos64EG.MersenneLength
      (HypostructureErdos64EG.Fixtures.K4.fourCycle.length - 1))

/-- The common paper-visible result of validating the K4 witness. -/
def expectedObservation : Observation where
  vertexCount := 4
  edgeCount := 6
  minimumDegree := 3
  witnessExponent := 2
  witnessLength := 4
  witnessIsCycle := true
  powerOfTwoAccepted := true
  mersenneReturnAccepted := true

theorem legacyObservation_eq_expected :
    legacyObservation = expectedObservation := by
  apply Observation.ext
  · exact Legacy.vertexCount
  · exact Legacy.edgeCount
  · exact Legacy.minimumDegree
  · rfl
  · exact Legacy.fourCycle_length
  · change @decide Legacy.fourCycle.IsCycle
      Legacy.fourCycleIsCycleDecidable = true
    exact (@decide_eq_true_iff Legacy.fourCycle.IsCycle
      Legacy.fourCycleIsCycleDecidable).mpr Legacy.fourCycle_isCycle
  · exact decide_eq_true Legacy.powerOfTwoAccepted
  · exact decide_eq_true Legacy.mersenneReturnAccepted

theorem modernObservation_eq_expected :
    modernObservation = expectedObservation := by
  apply Observation.ext
  · exact Modern.vertexCount
  · exact Modern.edgeCount
  · exact Modern.minimumDegree
  · rfl
  · exact HypostructureErdos64EG.Fixtures.K4.fourCycle_length
  · change @decide
      HypostructureErdos64EG.Fixtures.K4.fourCycle.IsCycle
      (Hypostructure.Graph.isCycleDecidable
        (object := Modern.fixture)
        HypostructureErdos64EG.Fixtures.K4.fourCycle) = true
    exact (@decide_eq_true_iff
      HypostructureErdos64EG.Fixtures.K4.fourCycle.IsCycle
      (Hypostructure.Graph.isCycleDecidable
        (object := Modern.fixture)
        HypostructureErdos64EG.Fixtures.K4.fourCycle)).mpr
          HypostructureErdos64EG.Fixtures.K4.fourCycle_isCycle
  · exact decide_eq_true Modern.powerOfTwoAccepted
  · exact decide_eq_true Modern.mersenneReturnAccepted

/-- The independently constructed K4 certificates have identical normalized
public behavior, including the dyadic cycle and Mersenne-return decisions. -/
theorem normalizedObservation_eq : legacyObservation = modernObservation := by
  exact legacyObservation_eq_expected.trans
    modernObservation_eq_expected.symm

#print axioms Legacy.fourCycle_isCycle
#print axioms Legacy.baseline
#print axioms Legacy.target
#print axioms k4_representsSameGraph
#print axioms legacyObservation_eq_expected
#print axioms modernObservation_eq_expected
#print axioms normalizedObservation_eq

end HypostructureParity.Erdos64EG.Fixtures.K4
