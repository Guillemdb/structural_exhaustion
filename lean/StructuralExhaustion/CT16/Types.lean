import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT16

universe uAmbient uBranch uCoordinate uCode

/-- Primitive whole-object exact-type vocabulary. -/
structure Capability (P : Core.Problem.{uAmbient, uBranch}) where
  Coordinate : Type uCoordinate
  coordinates : FinEnum Coordinate
  InSupport : P.Ambient → Coordinate → Prop
  inSupportDecidable : ∀ G coordinate, Decidable (InSupport G coordinate)
  ClosedCode : Type uCode
  codeDecidableEq : DecidableEq ClosedCode
  closedCode : P.Ambient → ClosedCode
  targetCode : ClosedCode

/-- Transition-facing invocation; the branch context is an index and is never
duplicated inside a residual. -/
structure Input {P : Core.Problem.{uAmbient, uBranch}}
    (_capability : Capability P) (_context : Core.BranchContext P) where

structure ProperSupportResidual {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability P) (context : Core.BranchContext P) where
  missing : capability.Coordinate
  absent : ¬ capability.InSupport context.G missing

structure WholeSupportState {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability P) (context : Core.BranchContext P) : Prop where
  covers : ∀ coordinate, capability.InSupport context.G coordinate

structure ClosedCodeState {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability P) (context : Core.BranchContext P) where
  whole : WholeSupportState capability context
  code : capability.ClosedCode
  exact : code = capability.closedCode context.G

def computeCode {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability P) (context : Core.BranchContext P)
    (whole : WholeSupportState capability context) :
    ClosedCodeState capability context :=
  ⟨whole, capability.closedCode context.G, rfl⟩

structure ExactCodeCertificate {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability P) (context : Core.BranchContext P) where
  state : ClosedCodeState capability context
  equal : state.code = capability.targetCode

structure ClosedTypeMismatchResidual {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability P) (context : Core.BranchContext P) where
  state : ClosedCodeState capability context
  notEqual : state.code ≠ capability.targetCode

inductive SupportDecision {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability P) (context : Core.BranchContext P) where
  | proper (residual : ProperSupportResidual capability context)
  | whole (state : WholeSupportState capability context)

def scanSupport {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability P) (context : Core.BranchContext P) :
    SupportDecision capability context :=
  match Core.FiniteSearch.search capability.coordinates
      (fun coordinate => ¬ capability.InSupport context.G coordinate)
      (fun coordinate =>
        match capability.inSupportDecidable context.G coordinate with
        | .isTrue present => .isFalse fun absent => absent present
        | .isFalse absent => .isTrue absent) with
  | .found coordinate absent => .proper ⟨coordinate, absent⟩
  | .absent noneMissing => .whole ⟨fun coordinate => by
      cases capability.inSupportDecidable context.G coordinate with
      | isTrue present => exact present
      | isFalse absent => exact (noneMissing coordinate absent).elim⟩

inductive CodeDecision {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability P) (context : Core.BranchContext P)
    (state : ClosedCodeState capability context) where
  | equal (certificate : ExactCodeCertificate capability context)
  | mismatch (residual : ClosedTypeMismatchResidual capability context)

def compareCode {P : Core.Problem.{uAmbient, uBranch}}
    (capability : Capability P) (context : Core.BranchContext P)
    (state : ClosedCodeState capability context) :
    CodeDecision capability context state :=
  match capability.codeDecidableEq
      state.code capability.targetCode with
  | .isTrue equal => .equal ⟨state, equal⟩
  | .isFalse notEqual => .mismatch ⟨state, notEqual⟩

end StructuralExhaustion.CT16
