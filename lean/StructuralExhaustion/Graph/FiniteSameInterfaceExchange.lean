import StructuralExhaustion.Graph.FiniteContextResponseComparison

namespace StructuralExhaustion.Graph.FiniteSameInterfaceExchange

open StructuralExhaustion

universe uAmbient uBranch uPiece uOutside uCode uProfile uSilent

/-!
# Finite response algebra for two same-interface representatives

This module owns the reusable part of a bounded-germ exchange.  Applications
must still construct the two literal representatives and their graph-specific
boundary compatibility; the framework never manufactures those facts.
-/

/-- Two exact representatives, with the manuscript's signed increment. -/
structure Representatives (Piece : Type uPiece) where
  source : Piece
  replacement : Piece
  size : Piece → Nat
  increment : Int
  incrementExact : increment =
    Int.ofNat (size source) - Int.ofNat (size replacement)

namespace Representatives

variable {Piece : Type uPiece}

noncomputable def exact (source replacement : Piece) (size : Piece → Nat) :
    Representatives Piece where
  source := source
  replacement := replacement
  size := size
  increment := Int.ofNat (size source) - Int.ofNat (size replacement)
  incrementExact := rfl

end Representatives

/-- Full boundary-profile compatibility, kept separate from merely capped or
single-role equality. -/
structure BoundaryCompatible {Piece : Type uPiece}
    (representatives : Representatives Piece) where
  Profile : Type uProfile
  profile : Piece → Profile
  equal : profile representatives.replacement =
    profile representatives.source

/-- A finite local response table with symbolic coverage of every compatible
outside context.  `coverage` is a theorem, not an enumeration of `Outside`. -/
structure ResponseTable {Piece : Type uPiece}
    (representatives : Representatives Piece) where
  Outside : Type uOutside
  Code : Type uCode
  codes : FinEnum Code
  decode : Code → Outside
  targetResponseReplacement : Outside → Prop
  targetResponseSource : Outside → Prop
  replacementResponse : Code → Bool
  sourceResponse : Code → Bool
  replacementReflect : ∀ code,
    replacementResponse code = true ↔
      targetResponseReplacement (decode code)
  sourceReflect : ∀ code,
    sourceResponse code = true ↔ targetResponseSource (decode code)
  coverage : ∀ outside, ∃ code,
    (targetResponseReplacement outside ↔
      replacementResponse code = true) ∧
    (targetResponseSource outside ↔ sourceResponse code = true)

namespace ResponseTable

variable {Piece : Type uPiece}

private noncomputable def decodeRealized
    {Outside : Type uOutside} [Nonempty Outside]
    (target : Outside → Prop) [DecidablePred target] (bit : Bool) : Outside := by
  classical
  exact if realized : ∃ outside, decide (target outside) = bit then
    Classical.choose realized
  else Classical.choice inferInstance

private theorem decodeRealized_spec
    {Outside : Type uOutside} [Nonempty Outside]
    (target : Outside → Prop) [DecidablePred target] (bit : Bool)
    (realized : ∃ outside, decide (target outside) = bit) :
    decide (target (decodeRealized target bit)) = bit := by
  classical
  simp only [decodeRealized, dif_pos realized]
  exact Classical.choose_spec realized

/-- Build the exact finite response table from a symbolic universal-response
theorem.  The two Boolean codes decode to proof-selected contexts realizing
that truth value when it is realized, and to an arbitrary context otherwise.
There is no enumeration of `Outside`. -/
noncomputable def ofUniversal
    {representatives : Representatives Piece}
    (Outside : Type uOutside) [Nonempty Outside]
    (targetReplacement targetSource : Outside → Prop)
    [DecidablePred targetReplacement] [DecidablePred targetSource]
    (universal : ∀ outside,
      targetReplacement outside ↔ targetSource outside) :
    ResponseTable representatives where
  Outside := Outside
  Code := Bool
  codes := Core.Enumeration.bool
  decode := decodeRealized targetSource
  targetResponseReplacement := targetReplacement
  targetResponseSource := targetSource
  replacementResponse := fun code =>
    decide (targetSource (decodeRealized targetSource code))
  sourceResponse := fun code =>
    decide (targetSource (decodeRealized targetSource code))
  replacementReflect := by
    intro code
    simpa using (universal (decodeRealized targetSource code)).symm
  sourceReflect := by intro code; simp
  coverage := by
    intro outside
    let code := decide (targetSource outside)
    have realized : ∃ witness,
        decide (targetSource witness) = code := ⟨outside, rfl⟩
    have decoded := decodeRealized_spec targetSource code realized
    refine ⟨code, ?_, ?_⟩
    · rw [universal outside]
      simpa [code] using decoded.symm
    · simpa [code] using decoded.symm

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {branch : Core.BranchContext P}
variable {representatives : Representatives Piece}
variable (table : ResponseTable.{uPiece, uOutside, uCode} representatives)

/-- CT7 specialization: realization is disabled, so the exact finite scan
returns either a distinguishing decoded context or universal neutrality. -/
def comparisonProfile :
    FiniteContextResponseComparison.Profile P branch where
  Object := Bool
  Outside := table.Outside
  Code := table.Code
  codes := table.codes
  left := false
  right := true
  response := fun side code =>
    if side then table.sourceResponse code else table.replacementResponse code
  targetResponse := fun side outside =>
    if side then table.targetResponseSource outside
    else table.targetResponseReplacement outside
  decode := table.decode
  response_reflect := by
    intro side code
    cases side <;> simp [table.replacementReflect, table.sourceReflect]
  pairCoverage := by
    intro outside
    simpa using table.coverage outside

noncomputable def run := (table.comparisonProfile (P := P) (branch := branch)).run

theorem checks_eq :
    (table.comparisonProfile (P := P) (branch := branch)).checks =
      2 * table.codes.card :=
  (table.comparisonProfile (P := P) (branch := branch)).checks_eq

theorem run_verified :
    (table.comparisonProfile (P := P) (branch := branch)).ct7Run.outcome.Valid :=
  (table.comparisonProfile (P := P) (branch := branch)).ct7Run_verified

end ResponseTable

/-- Target completeness derived only after the finite response scan is
neutral and the full boundary profile is known equal. -/
structure TargetComplete {Piece : Type uPiece}
    (representatives : Representatives Piece)
    (boundary : BoundaryCompatible representatives)
    (table : ResponseTable representatives) : Prop where
  boundaryEqual : boundary.profile representatives.replacement =
    boundary.profile representatives.source
  universal : ∀ outside : table.Outside,
    table.targetResponseReplacement outside ↔
      table.targetResponseSource outside

noncomputable def targetCompleteOfNeutral
    {P : Core.Problem.{uAmbient, uBranch}}
    {branch : Core.BranchContext P}
    {Piece : Type uPiece}
    {representatives : Representatives Piece}
    {boundary : BoundaryCompatible representatives}
    {table : ResponseTable representatives}
    (neutral :
      (table.comparisonProfile (P := P) (branch := branch)).Neutrality) :
    TargetComplete representatives boundary table where
  boundaryEqual := boundary.equal
  universal := neutral.universal

/-- Conditional silent orientation.  No admissibility or strictness is stored
in the neutral germ; it is requested only after nonzero increment and target
completeness, matching the manuscript's G3 order. -/
structure ConditionalSilent {Piece : Type uPiece}
    (representatives : Representatives Piece)
    (boundary : BoundaryCompatible representatives)
    (table : ResponseTable representatives) where
  Silent : Type uSilent
  orient : representatives.increment ≠ 0 →
    TargetComplete representatives boundary table → Silent

end StructuralExhaustion.Graph.FiniteSameInterfaceExchange
