import StructuralExhaustion.CT9.ClasswiseTokenLedger
import StructuralExhaustion.Core.GreedyMatchingStar
import StructuralExhaustion.Graph.SurplusCapacityTokenRouting

namespace StructuralExhaustion.Graph.SurplusClasswiseOverload

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext
  (PackedMinimumDegreeCycle.StaticInput.problem.{u} input)
  (PackedMinimumDegreeCycle.StaticInput.Target.{u} input)}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

abbrev Pair := SurplusPairResponse.ScheduledPair (setup := setup)
abbrev Token := SurplusCapacityTokenRouting.Token (ctx := ctx) (setup := setup)
abbrev Role := SurplusTokenRole.TotalRole
abbrev Class := SurplusTokenRole.TokenClass

/-!
# Coupled classwise overload of the complete surplus-pair ledger

The profile below consumes exactly the node-[136] pair schedule and its total
capacity-token/role map.  It does not use a Boolean-state realization or a
baseline entropy estimate: its load is the literal complete scheduled-pair
count.  Each overload is therefore a computed CT9 fibre of the same selected
graph.
-/

/-- Sharp matching--star cap appearing in the manuscript. -/
def matchingStarCap (size : Nat) : Nat :=
  Core.GreedyMatchingStar.matchingStarCap size

def classCapacity (windowSize remainderSize primitiveSize : Nat) : Class → Nat
  | .window => matchingStarCap windowSize
  | .remainder => matchingStarCap remainderSize
  | .primitive => matchingStarCap primitiveSize

noncomputable def tokenClass (token : Token (ctx := ctx) (setup := setup)) : Class :=
  (SurplusCapacityTokenRouting.tokenSubtype
    (ctx := ctx) (setup := setup) token).tokenClass

noncomputable def profile (windowSize remainderSize primitiveSize : Nat) :
    CT9.ClasswiseTokenLedger.Profile
      (PackedMinimumDegreeCycle.StaticInput.problem.{u} input) where
  Item := Pair (setup := setup)
  Token := Token (ctx := ctx) (setup := setup)
  Role := Role
  Class := Class
  tokens := SurplusCapacityTokenRouting.tokens (ctx := ctx) (setup := setup)
  roles := SurplusTokenRole.totalRoleEnum
  classOf := tokenClass (ctx := ctx) (setup := setup)
  token := SurplusCapacityTokenRouting.pairToken stage
  role := SurplusCapacityTokenRouting.pairRole stage
  classCapacity := classCapacity windowSize remainderSize primitiveSize

noncomputable def items : Core.OrderedCollection (Pair (setup := setup)) :=
  (SurplusCapacityTokenRouting.pairs (setup := setup)).toOrderedCollection

theorem items_length :
    (items (setup := setup)).values.length =
      (SurplusCapacityTokenRouting.pairs (setup := setup)).card := by
  exact FinEnum.toOrderedCollection_length _

noncomputable def decision (windowSize remainderSize primitiveSize : Nat) :=
  (profile stage windowSize remainderSize primitiveSize).decide
    ctx.toBranchContext (items (setup := setup))

/-- The two diagram class tests are one exhaustive decision on the actual
token constructor. -/
inductive RoutedClass (token : Token (ctx := ctx) (setup := setup)) : Type
  | window (isWindow : tokenClass token = .window)
  | remainder (isRemainder : tokenClass token = .remainder)
  | primitive (isPrimitive : tokenClass token = .primitive)

noncomputable def routeClass (token : Token (ctx := ctx) (setup := setup)) :
    RoutedClass (ctx := ctx) (setup := setup) token := by
  cases classEq : tokenClass token with
  | window => exact .window classEq
  | remainder => exact .remainder classEq
  | primitive => exact .primitive classEq

/-- Positive node-[137] output together with the exact node-[139]/[141]
class route. -/
structure RoutedOverload (windowSize remainderSize primitiveSize : Nat) where
  overload : (profile stage windowSize remainderSize primitiveSize).Overload
    ctx.toBranchContext (items (setup := setup))
  routed : RoutedClass (ctx := ctx) (setup := setup) overload.residual.label.1

noncomputable def routedOverload (windowSize remainderSize primitiveSize : Nat)
    (overload : (profile stage windowSize remainderSize primitiveSize).Overload
      ctx.toBranchContext (items (setup := setup))) :
    RoutedOverload stage windowSize remainderSize primitiveSize :=
  ⟨overload, routeClass overload.residual.label.1⟩

theorem exactPartition (windowSize remainderSize primitiveSize : Nat) :
    (items (setup := setup)).values.length =
      ((profile stage windowSize remainderSize primitiveSize).labels.orderedValues.map
        fun label => CT9.fibreCount
          (profile stage windowSize remainderSize primitiveSize).capability
          ((profile stage windowSize remainderSize primitiveSize).input
            ctx.toBranchContext (items (setup := setup))) label).sum :=
  (profile stage windowSize remainderSize primitiveSize).exactPartition
    ctx.toBranchContext (items (setup := setup))

noncomputable def coupledCapacity
    (windowSize remainderSize primitiveSize : Nat) : Nat :=
  (profile (input := input) (ctx := ctx) (setup := setup) stage
    windowSize remainderSize primitiveSize).totalCapacity

noncomputable def coupledExcess
    (windowSize remainderSize primitiveSize : Nat) : Nat :=
  (items (setup := setup)).values.length -
    coupledCapacity stage windowSize remainderSize primitiveSize

theorem coupledExcess_pos_iff
    (windowSize remainderSize primitiveSize : Nat) :
    0 < coupledExcess stage windowSize remainderSize primitiveSize ↔
      coupledCapacity stage windowSize remainderSize primitiveSize <
        (items (setup := setup)).values.length := by
  exact Nat.sub_pos_iff_lt

def maxCap (windowSize remainderSize primitiveSize : Nat) : Nat :=
  max (matchingStarCap windowSize)
    (max (matchingStarCap remainderSize) (matchingStarCap primitiveSize))

theorem classCapacity_le_max (windowSize remainderSize primitiveSize : Nat)
    (classValue : Class) :
    classCapacity windowSize remainderSize primitiveSize classValue ≤
      maxCap windowSize remainderSize primitiveSize := by
  cases classValue <;> simp [classCapacity, maxCap]

theorem totalCapacity_le (windowSize remainderSize primitiveSize : Nat) :
    coupledCapacity stage windowSize remainderSize primitiveSize ≤
      maxCap windowSize remainderSize primitiveSize *
        ((SurplusCapacityTokenRouting.tokens
          (ctx := ctx) (setup := setup)).card * 25) := by
  have bound :=
    (profile (input := input) (ctx := ctx) (setup := setup) stage
      windowSize remainderSize primitiveSize).totalCapacity_le
      (maxCap windowSize remainderSize primitiveSize)
      (classCapacity_le_max windowSize remainderSize primitiveSize)
  change coupledCapacity stage windowSize remainderSize primitiveSize ≤
    maxCap windowSize remainderSize primitiveSize *
      ((SurplusCapacityTokenRouting.tokens
        (ctx := ctx) (setup := setup)).card *
        SurplusTokenRole.totalRoleEnum.card) at bound
  rw [SurplusTokenRole.totalRole_card] at bound
  exact bound

noncomputable def checks (_windowSize _remainderSize _primitiveSize : Nat) : Nat :=
  (SurplusCapacityTokenRouting.pairs (setup := setup)).card *
    ((SurplusCapacityTokenRouting.tokens
      (ctx := ctx) (setup := setup)).card * 25)

theorem checks_eq (windowSize remainderSize primitiveSize : Nat) :
    checks (setup := setup) windowSize remainderSize primitiveSize =
      (SurplusCapacityTokenRouting.pairs (setup := setup)).card *
        ((SurplusCapacityTokenRouting.tokens
          (ctx := ctx) (setup := setup)).card * 25) := by
  rfl

/-- Complete reusable contract for the coupled overload and its two class
tests. -/
structure VerifiedStage (windowSize remainderSize primitiveSize : Nat) : Type _ where
  source : SurplusCapacityTokenRouting.VerifiedStage stage
  exactLedger : (items (setup := setup)).values.length =
    ((profile stage windowSize remainderSize primitiveSize).labels.orderedValues.map
      fun label => CT9.fibreCount
        (profile stage windowSize remainderSize primitiveSize).capability
        ((profile stage windowSize remainderSize primitiveSize).input
          ctx.toBranchContext (items (setup := setup))) label).sum
  coupledDecision :
    (profile stage windowSize remainderSize primitiveSize).Decision
      ctx.toBranchContext (items (setup := setup))
  capacityBound :
    coupledCapacity stage windowSize remainderSize primitiveSize ≤
      maxCap windowSize remainderSize primitiveSize *
        ((SurplusCapacityTokenRouting.tokens
          (ctx := ctx) (setup := setup)).card * 25)
  checkCount : checks (setup := setup) windowSize remainderSize primitiveSize =
    (SurplusCapacityTokenRouting.pairs (setup := setup)).card *
      ((SurplusCapacityTokenRouting.tokens
        (ctx := ctx) (setup := setup)).card * 25)

noncomputable def verifiedStage (windowSize remainderSize primitiveSize : Nat) :
    VerifiedStage stage windowSize remainderSize primitiveSize where
  source := SurplusCapacityTokenRouting.verifiedStage stage
  exactLedger := exactPartition stage windowSize remainderSize primitiveSize
  coupledDecision := decision stage windowSize remainderSize primitiveSize
  capacityBound := totalCapacity_le stage windowSize remainderSize primitiveSize
  checkCount := checks_eq (input := input) (ctx := ctx) (setup := setup)
    windowSize remainderSize primitiveSize

end StructuralExhaustion.Graph.SurplusClasswiseOverload
