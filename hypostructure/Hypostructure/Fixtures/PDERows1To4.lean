import Hypostructure.Core.Budget.Transcript
import Hypostructure.PDE.NavierStokes
import Hypostructure.PDE.Quotient

/-!
# Axiom-audited fixtures for PDE rows 1-4

The finite-dimensional ladder exercises both form-closure constructors, two
resource monoids, and both sides of the quotient-geometry decision.  The
Navier--Stokes registration uses only definitions and the already proved
pressure-gauge semantics; it asserts no new analytic theorem.
-/

namespace Hypostructure.Fixtures.PDERows1To4

open Hypostructure.PDE

universe uPrevious

namespace FiniteScalar

def problem : Core.Problem where
  Ambient := Real
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def atlas : LocalAtlas problem where
  Point := Unit
  Window := Unit
  contains := fun _ _ => True
  nested := fun _ _ => True
  nested_refl := fun _ => trivial
  nested_trans := fun _ _ => trivial
  core := id
  core_nested := fun _ => trivial
  LocalObject := fun _ => Real
  restrict := fun value _ => value
  restrictLocal := fun _ value => value
  restrict_refl := fun _ _ => rfl
  restrict_trans := fun _ _ _ => rfl
  restrict_global := by
    intro value small large nested
    rfl

def equation : RepresentedEquation problem atlas where
  EquationData := fun _ _ => Unit
  satisfies := fun _ => True
  restrictEquation := fun _ _ data => data
  restrict_satisfies := fun _ _ _ valid => valid

def model : LocalModel where
  problem := problem
  atlas := atlas
  equation := equation

def observables : ObservableInterface model where
  Index := Unit
  Value := fun _ => Real
  observe := fun value _ => value
  visible := fun _ _ => True
  localObserve := fun _ value _ => value
  localReflect := by
    intro value window index visible
    rfl

def target (value : Real) : Prop := value = 0

def targetInterface : TargetInterface model target observables where
  accepts := fun values => values () = (0 : Real)
  target_iff := fun _ => Iff.rfl

def signature : PDE.FastTrack.Signature model target where
  semantics := RepresentationSemantics.equality problem
  observables := observables
  observableInvariant := ObservableInvariant.equality model observables
  targetInterface := targetInterface

def root : Core.Residual.Ledger Unit := Core.Residual.Ledger.initial ()

def signatureStage := signature.register root

theorem signature_stage_retains_root : signatureStage.previous = root := rfl

theorem target_transport {left right : Real}
    (equivalent : signature.semantics.equivalent left right) :
    target left <-> target right :=
  signature.targetInvariant.target_iff equivalent

end FiniteScalar

namespace NavierStokes2D

open PDE.NavierStokes

def origin : Spacetime := (0, 0)

def observables : ObservableInterface model where
  Index := Unit
  Value := fun _ => Space
  observe := fun field _ => field.velocity origin
  visible := fun _ _ => True
  localObserve := fun _ field _ => field.velocity origin
  localReflect := by
    intro field window index visible
    rfl

def observableInvariant :
    ObservableInvariant model representationSemantics observables where
  observe_eq := by
    intro left right equivalent index
    rcases equivalent with ⟨domain, velocity, viscosity, gauge⟩
    change left.velocity origin = right.velocity origin
    rw [velocity]

def target (field : Field) : Prop := field.velocity origin = 0

def targetInterface : TargetInterface model target observables where
  accepts := fun values => values () = (0 : Space)
  target_iff := fun _ => Iff.rfl

def signature : PDE.FastTrack.Signature model target where
  semantics := representationSemantics
  observables := observables
  observableInvariant := observableInvariant
  targetInterface := targetInterface

noncomputable def signatureStage := signature.register FiniteScalar.root

theorem zero_field_is_registered_target : target (zeroField 1) := by
  rfl

theorem pressure_gauge_preserves_registered_target
    (gauge : Real -> Real) :
    target ((pressureGauge.coordinate gauge {
      center := origin
      radius := 1
      radius_pos := by norm_num
    }).realize (zeroField 1)) <-> target (zeroField 1) :=
  signature.targetInvariant.target_iff
    (pressureGauge.equivalent_realize gauge _ (zeroField 1))

end NavierStokes2D

namespace FiniteForm

def productForm : BilinearForm Real := LinearMap.mul Real Real

def discreteTopology : FormTopology Real where
  converges := fun sequence limit => sequence 0 = limit
  scalarCauchy := fun _ => True
  scalarConverges := fun sequence limit => sequence 0 = limit

def closedLaw : ClosedFormLaw Real (⊤ : Submodule Real Real)
    productForm discreteTopology where
  closed := by
    intro sequence limit inDomain converges cauchy
    refine ⟨Submodule.mem_top, ?_⟩
    change productForm (sequence 0) (sequence 0) = productForm limit limit
    rw [converges]

def closableLaw : ClosableFormLaw Real (⊤ : Submodule Real Real)
    productForm discreteTopology where
  closesAtZero := by
    intro sequence inDomain converges cauchy
    change productForm (sequence 0) (sequence 0) = 0
    rw [converges]
    simp [productForm]

def closedGeneratorForm : GeneratorForm FiniteScalar.model Real where
  domain := ⊤
  generator := LinearMap.id
  pairing := productForm
  form := productForm
  symmetricPart := productForm
  skewPart := 0
  boundaryPart := 0
  topology := discreteTopology
  closure := .closed closedLaw
  generator_representation := by
    intro x hx y hy
    rfl
  decomposition := by
    intro x y
    simp
  symmetric := by
    intro x y
    change x * y = y * x
    ring
  skew := by simp
  symmetric_nonnegative := by
    intro x hx
    change 0 <= x * x
    exact mul_self_nonneg x
  sectorConstant := 0
  sectorConstant_nonnegative := le_rfl
  sector := by simp

def closableGeneratorForm : GeneratorForm FiniteScalar.model Real := {
  closedGeneratorForm with
  closure := .closable closableLaw
}

def closedStage := closedGeneratorForm.register FiniteScalar.signatureStage
def closableStage := closableGeneratorForm.register FiniteScalar.signatureStage

theorem closed_stage_retains_signature :
    closedStage.previous = FiniteScalar.signatureStage := rfl

theorem closable_stage_retains_signature :
    closableStage.previous = FiniteScalar.signatureStage := rfl

end FiniteForm

namespace Budgets

abbrev natBudget : Core.ResourceBudget where
  Resource := Nat
  le := (· <= ·)
  leRefl := Nat.le_refl
  leTrans := Nat.le_trans
  zero := 0
  add := (· + ·)
  ceiling := id
  zeroLe := Nat.zero_le
  addMono := Nat.add_le_add
  addAssoc := Nat.add_assoc
  zeroAdd := Nat.zero_add
  addZero := Nat.add_zero

def natOrder : Core.ResourceOrderLaws natBudget where
  decideLE := fun _ _ => inferInstance
  ceiling_monotone := fun h => h
  add_comm := Nat.add_comm

def natRepresentation :
    Core.ResourceRepresentationInvariant natBudget Nat Eq where
  cost := id
  cost_eq := by
    intro left right equal
    cases equal
    rfl

def natComposition :
    Core.BoundedResourceComposition natBudget Nat Eq natRepresentation where
  compose := (· + ·)
  overhead := 0
  enlarge := fun size => 2 * size
  classMultiplier := 2
  classOffset := 0
  enlarge_bound := by omega
  cost_compose_le := by
    intro left right
    simp [natBudget, natRepresentation]
  ceiling_absorbs := by
    intro size left right leftAffordable rightAffordable
    simp only [natBudget, natRepresentation, id_eq] at leftAffordable rightAffordable ⊢
    omega

def natStaticDynamic :
    Core.StaticDynamicComparison natBudget Nat Nat where
  staticCost := id
  dynamicCost := id
  comparable := fun static dynamic => dynamic <= static
  transfer := fun related => related

def natInput : Core.ResourceTranscript.Input natBudget Nat Eq Nat Nat where
  order := natOrder
  representation := natRepresentation
  composition := natComposition
  staticDynamic := natStaticDynamic

def natTranscript := Core.ResourceTranscript.derive natInput
def natStage := Core.ResourceTranscript.register natInput FiniteForm.closedStage

theorem nat_stage_retains_form :
    natStage.previous = FiniteForm.closedStage := rfl

theorem nat_b2_example :
    Core.ResourceTranscript.Affordable natRepresentation 3 2 ->
    Core.ResourceTranscript.Affordable natRepresentation 3 3 ->
      Core.ResourceTranscript.Affordable natRepresentation 6
        (natComposition.compose 2 3) :=
  natTranscript.b2Composition

theorem nat_b3_example {left right : Nat} (equal : left = right) :
    Core.ResourceTranscript.Affordable natRepresentation 8 left <->
      Core.ResourceTranscript.Affordable natRepresentation 8 right :=
  natTranscript.b3Representation equal

theorem nat_b4_example {static dynamic : Nat}
    (related : dynamic <= static)
    (affordable : static <= 10) : dynamic <= 10 :=
  natTranscript.b4StaticDynamic related affordable

abbrev realEnergyBudget : Core.ResourceBudget where
  Resource := NNReal
  le := (· <= ·)
  leRefl := fun _ => le_rfl
  leTrans := fun first second => le_trans first second
  zero := 0
  add := (· + ·)
  ceiling := fun size => size
  zeroLe := fun _ => zero_le
  addMono := fun first second => add_le_add first second
  addAssoc := fun first second third => add_assoc first second third
  zeroAdd := fun value => zero_add value
  addZero := fun value => add_zero value

noncomputable def realEnergyOrder : Core.ResourceOrderLaws realEnergyBudget where
  decideLE := by
    intro left right
    change Decidable (left <= right)
    infer_instance
  ceiling_monotone := by
    intro small large less
    change (small : NNReal) <= (large : NNReal)
    exact_mod_cast less
  add_comm := by
    intro left right
    change left + right = right + left
    exact add_comm left right

def realEnergyRepresentation :
    Core.ResourceRepresentationInvariant realEnergyBudget NNReal Eq where
  cost := fun value => value
  cost_eq := by
    intro left right equal
    cases equal
    rfl

def realEnergyComposition :
    Core.BoundedResourceComposition realEnergyBudget NNReal Eq
      realEnergyRepresentation where
  compose := (· + ·)
  overhead := realEnergyBudget.zero
  enlarge := fun size => size + size
  classMultiplier := 2
  classOffset := 0
  enlarge_bound := by omega
  cost_compose_le := by
    intro left right
    change left + right <= left + right + 0
    simp
  ceiling_absorbs := by
    intro size left right leftAffordable rightAffordable
    change left + right + 0 <= (size + size : Nat)
    calc
      left + right + 0 = left + right := by simp
      _ <= (size : NNReal) + (size : NNReal) :=
        add_le_add leftAffordable rightAffordable
      _ = (size + size : Nat) := by norm_num

def realEnergyStaticDynamic :
    Core.StaticDynamicComparison realEnergyBudget NNReal NNReal where
  staticCost := fun value => value
  dynamicCost := fun value => value
  comparable := fun static dynamic => dynamic <= static
  transfer := by
    intro static dynamic related
    exact related

noncomputable def realEnergyInput :
    Core.ResourceTranscript.Input realEnergyBudget NNReal Eq NNReal NNReal where
  order := realEnergyOrder
  representation := realEnergyRepresentation
  composition := realEnergyComposition
  staticDynamic := realEnergyStaticDynamic

noncomputable def realEnergyTranscript :=
  Core.ResourceTranscript.derive realEnergyInput
noncomputable def realEnergyStage :=
  Core.ResourceTranscript.register realEnergyInput FiniteForm.closableStage

theorem real_energy_b2_example {left right : NNReal}
    (leftAffordable : left <= 4) (rightAffordable : right <= 4) :
    left + right <= 8 :=
  realEnergyTranscript.b2Composition leftAffordable rightAffordable

end Budgets

namespace QuotientDefect

def representedQuotient : RepresentedQuotient FiniteScalar.model
    FiniteScalar.signature.semantics Real Real where
  represent := id
  project := LinearMap.id
  lift := LinearMap.id
  project_lift := by
    apply LinearMap.ext
    intro value
    rfl
  equivalent_project := by
    intro left right equivalent
    cases equivalent
    rfl

def matchingGenerator :
    QuotientGenerator FiniteForm.closedGeneratorForm representedQuotient where
  generator := LinearMap.id

def zeroQuotientGenerator :
    QuotientGenerator FiniteForm.closedGeneratorForm representedQuotient where
  generator := 0

def zeroDefectStage := registerDefect FiniteForm.closedGeneratorForm
  representedQuotient matchingGenerator Budgets.natStage

def nonzeroDefectStage := registerDefect FiniteForm.closedGeneratorForm
  representedQuotient zeroQuotientGenerator Budgets.natStage

theorem zero_defect_retains_budget :
    zeroDefectStage.previous = Budgets.natStage := rfl

theorem zero_defect_is_zero : zeroDefectStage.added = 0 := by
  apply LinearMap.ext
  intro value
  change intertwiningDefect FiniteForm.closedGeneratorForm
    representedQuotient matchingGenerator value = 0
  simp [intertwiningDefect, matchingGenerator, representedQuotient,
    FiniteForm.closedGeneratorForm]

theorem nonzero_defect_at_one : nonzeroDefectStage.added 1 = 1 := by
  change intertwiningDefect FiniteForm.closedGeneratorForm
    representedQuotient zeroQuotientGenerator 1 = 1
  simp [intertwiningDefect, zeroQuotientGenerator, representedQuotient,
    FiniteForm.closedGeneratorForm]

def topGeometry : DefectGeometry Real where
  domain := ⊤
  carrier := ⊤
  carrier_le_domain := le_rfl
  pairing := FiniteForm.productForm
  positiveOperator := LinearMap.id
  positive_on_domain := by
    intro state inDomain
    change 0 <= state * state
    exact mul_self_nonneg state
  preserves_carrier := by simp

def bottomGeometry : DefectGeometry Real where
  domain := ⊤
  carrier := ⊥
  carrier_le_domain := bot_le
  pairing := FiniteForm.productForm
  positiveOperator := LinearMap.id
  positive_on_domain := by
    intro state inDomain
    change 0 <= state * state
    exact mul_self_nonneg state
  preserves_carrier := by
    intro state inCarrier
    simpa using inCarrier

def topDecidable {Previous : Sort uPrevious} : forall stage :
    DefectStage Previous Real Real,
    Decidable (topGeometry.Contains stage.added) := by
  intro stage
  exact isTrue fun value => Submodule.mem_top

noncomputable def bottomDecidable {Previous : Sort uPrevious} : forall stage :
    DefectStage Previous Real Real,
    Decidable (bottomGeometry.Contains stage.added) := by
  intro stage
  classical
  infer_instance

def containedDecision := decideGeometry topGeometry topDecidable zeroDefectStage

noncomputable def outsideDecision :=
  decideGeometry bottomGeometry bottomDecidable nonzeroDefectStage

theorem nonzero_defect_outside :
    Not (bottomGeometry.Contains nonzeroDefectStage.added) := by
  intro contained
  have atOne := contained 1
  have isZero : nonzeroDefectStage.added 1 = 0 := by
    simpa [bottomGeometry] using atOne
  rw [nonzero_defect_at_one] at isZero
  norm_num at isZero

theorem contained_decision_uses_yes_branch :
    match containedDecision.added with
    | .yesBranch _ => True
    | .noBranch _ => False := by
  cases h : containedDecision.added with
  | yesBranch proof => trivial
  | noBranch absent =>
      exact (absent fun value => Submodule.mem_top).elim

theorem outside_decision_uses_no_branch :
    match outsideDecision.added with
    | .yesBranch _ => False
    | .noBranch _ => True := by
  cases h : outsideDecision.added with
  | yesBranch contained => exact (nonzero_defect_outside contained).elim
  | noBranch absent => trivial

theorem outside_decision_retains_computed_defect :
    outsideDecision.previous = nonzeroDefectStage := rfl

end QuotientDefect

#print axioms FiniteScalar.target_transport
#print axioms NavierStokes2D.pressure_gauge_preserves_registered_target
#print axioms FiniteForm.closed_stage_retains_signature
#print axioms FiniteForm.closable_stage_retains_signature
#print axioms Budgets.nat_b2_example
#print axioms Budgets.real_energy_b2_example
#print axioms QuotientDefect.zero_defect_is_zero
#print axioms QuotientDefect.contained_decision_uses_yes_branch
#print axioms QuotientDefect.outside_decision_uses_no_branch

end Hypostructure.Fixtures.PDERows1To4
