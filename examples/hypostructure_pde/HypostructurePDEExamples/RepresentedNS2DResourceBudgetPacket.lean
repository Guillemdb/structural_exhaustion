import Hypostructure.Core.Budget.Transcript
import HypostructurePDEExamples.RepresentedNS2DGeneratorFormPacket

/-!
# Represented 2D Navier--Stokes resource-budget packet

This row-3 packet registers a finite algebraic resource model on the literal
row-2 represented zero-state stage.  Natural numbers are bookkeeping units,
and every represented zero state has declared cost zero.  Core derives the
B1--B4 transcript and owns the ledger extension.

The resulting affordability predicates concern only this declared algebraic
model.  This packet proves no Navier--Stokes energy estimate and imports no
analytic affordability theorem.
-/

namespace HypostructurePDEExamples.RepresentedNS2DResourceBudgetPacket

open Hypostructure
open Hypostructure.PDE
open Hypostructure.PDE.NavierStokes
open HypostructurePDEExamples.RepresentedNS2DLocalTailPacket
open HypostructurePDEExamples.RepresentedNS2DGeneratorFormPacket

noncomputable section

/-! ## Finite algebraic resource primitives -/

/-- Natural bookkeeping units for the represented zero-state packet. -/
abbrev algebraicBudget : Core.ResourceBudget where
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

/-- The additional ordered-monoid laws required for B1. -/
def algebraicOrder : Core.ResourceOrderLaws algebraicBudget where
  decideLE := fun _ _ => inferInstance
  ceiling_monotone := fun bound => bound
  add_comm := Nat.add_comm

/-- A represented row-2 zero state consumes no declared algebraic resource. -/
def zeroStateRepresentation :
    Core.ResourceRepresentationInvariant algebraicBudget GeneratorState Eq where
  cost := fun _ => 0
  cost_eq := by
    intro left right equivalent
    rfl

/-- Algebraic composition of represented zero states. -/
def zeroStateComposition :
    Core.BoundedResourceComposition algebraicBudget GeneratorState Eq
      zeroStateRepresentation where
  compose := (· + ·)
  overhead := 0
  enlarge := fun size => size
  classMultiplier := 1
  classOffset := 0
  enlarge_bound := by simp
  cost_compose_le := by
    intro left right
    simp [algebraicBudget, zeroStateRepresentation]
  ceiling_absorbs := by
    intro size left right leftAffordable rightAffordable
    simp [algebraicBudget, zeroStateRepresentation]

/-- Static and dynamic quantities are finite natural accounting values. -/
def algebraicStaticDynamic :
    Core.StaticDynamicComparison algebraicBudget Nat Nat where
  staticCost := id
  dynamicCost := id
  comparable := fun static dynamic => dynamic <= static
  transfer := fun related => related

/-- Primitive row-3 input; all B1--B4 consequences are derived by Core. -/
def resourceInput :
    Core.ResourceTranscript.Input algebraicBudget GeneratorState Eq Nat Nat where
  order := algebraicOrder
  representation := zeroStateRepresentation
  composition := zeroStateComposition
  staticDynamic := algebraicStaticDynamic

/-- The framework-derived B1--B4 transcript. -/
def resourceTranscript := Core.ResourceTranscript.derive resourceInput

/-! ## Literal row-3 registration -/

/-- The exact row-3 ledger shape. -/
abbrev ResourceBudgetStage :=
  Core.Residual.Ledger.Extension GeneratorFormStage
    (fun _ => Core.ResourceTranscript.Transcript resourceInput)

/-- Framework-owned row-3 registration on the literal row-2 stage. -/
def resourceBudgetStage : ResourceBudgetStage :=
  Core.ResourceTranscript.register resourceInput generatorFormStage

/-- The row-2 form query preserved through the row-3 extension. -/
def generatorFormQueryAtRowThree : Core.Residual.Query ResourceBudgetStage
    (fun _ => GeneratorForm model GeneratorState) :=
  generatorFormQuery.preserve
    (Added := fun _ => Core.ResourceTranscript.Transcript resourceInput)

theorem inherited_generator_form_is_literal :
    generatorFormQueryAtRowThree.read resourceBudgetStage = generatorForm :=
  rfl

theorem resource_budget_stage_retains_row_two :
    resourceBudgetStage.previous = generatorFormStage :=
  Core.ResourceTranscript.register_previous resourceInput generatorFormStage

theorem resource_budget_stage_retains_root_residual :
    Core.Residual.residualOf resourceBudgetStage = zeroRootResidual :=
  rfl

theorem registered_transcript_is_literal :
    resourceBudgetStage.added = resourceTranscript :=
  rfl

/-! ## Core-derived B1--B4 consequences -/

def b1_resource_comparison (left right : Nat) : Decidable (left <= right) :=
  resourceTranscript.b1Decidable left right

theorem b1_ceiling_monotone {small large : Nat} (bound : small <= large) :
    algebraicBudget.ceiling small <= algebraicBudget.ceiling large :=
  resourceTranscript.b1CeilingMonotone bound

theorem b1_accumulation_monotone {a b c d : Nat}
    (first : a <= b) (second : c <= d) :
    algebraicBudget.add a c <= algebraicBudget.add b d :=
  resourceTranscript.b1AccumulationMonotone first second

theorem b1_accumulation_commutative (left right : Nat) :
    algebraicBudget.add left right = algebraicBudget.add right left :=
  resourceTranscript.b1AccumulationCommutative left right

theorem b2_zero_state_composition {size : Nat} {left right : GeneratorState}
    (leftAffordable : Core.ResourceTranscript.Affordable
      zeroStateRepresentation size left)
    (rightAffordable : Core.ResourceTranscript.Affordable
      zeroStateRepresentation size right) :
    Core.ResourceTranscript.Affordable zeroStateRepresentation size
      (left + right) := by
  simpa [resourceInput, zeroStateComposition] using
    resourceTranscript.b2Composition leftAffordable rightAffordable

theorem b2_class_bound (size : Nat) :
    zeroStateComposition.enlarge size <=
      zeroStateComposition.classMultiplier * size +
        zeroStateComposition.classOffset :=
  resourceTranscript.b2ClassBound size

theorem b3_representation_affordability {size : Nat}
    {left right : GeneratorState} (equivalent : left = right) :
    (Core.ResourceTranscript.Affordable zeroStateRepresentation size left <->
      Core.ResourceTranscript.Affordable zeroStateRepresentation size right) :=
  resourceTranscript.b3Representation equivalent

theorem b4_static_dynamic_transfer {size static dynamic : Nat}
    (comparable : dynamic <= static) (staticAffordable : static <= size) :
    dynamic <= size :=
  resourceTranscript.b4StaticDynamic comparable staticAffordable

/-! ## Explicit analytic boundary -/

/-- Row 3 imports no NSE energy estimate or analytic affordability theorem. -/
def importedAnalyticContracts : List Core.AuthorPrimitiveRef := []

theorem no_imported_nse_energy_or_affordability_contract :
    importedAnalyticContracts = [] :=
  rfl

#print axioms resource_budget_stage_retains_row_two
#print axioms resource_budget_stage_retains_root_residual
#print axioms registered_transcript_is_literal
#print axioms inherited_generator_form_is_literal
#print axioms b1_ceiling_monotone
#print axioms b1_accumulation_monotone
#print axioms b1_accumulation_commutative
#print axioms b2_zero_state_composition
#print axioms b2_class_bound
#print axioms b3_representation_affordability
#print axioms b4_static_dynamic_transfer
#print axioms no_imported_nse_energy_or_affordability_contract

end

end HypostructurePDEExamples.RepresentedNS2DResourceBudgetPacket
