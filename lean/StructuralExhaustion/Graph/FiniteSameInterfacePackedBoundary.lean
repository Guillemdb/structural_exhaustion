import StructuralExhaustion.Core.ResidualRefinement
import StructuralExhaustion.Graph.FiniteSameInterfaceExchange
import StructuralExhaustion.Graph.PackedBoundariedGluing

namespace StructuralExhaustion.Graph.FiniteSameInterfaceExchange.PackedBoundary

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.PackedBoundariedGluing

universe u

/-!
# Orienting finite same-interface tables to packed graph replacement

This module is the graph-owned bridge from the CT3 finite same-interface
response algebra to the literal packed-boundary replacement theorem.  An
application may supply only semantic reflection facts for its current local
residual; the routing, target-completeness conversion, silent exchange, and
minimality contradiction remain framework-owned.
-/

namespace MinimumDegreeCycleReplacement

variable (input : PackedMinimumDegreeCycle.StaticInput)
variable {T : Type u} (boundaries : FinEnum T)
variable {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
variable (atom :
  PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom
    input boundaries ctx)

section Coded

variable {CodePiece : Type u}
variable (representatives : FiniteSameInterfaceExchange.Representatives CodePiece)
variable (table : FiniteSameInterfaceExchange.ResponseTable representatives)

/-- Semantic reflection of a finite same-interface response table whose
representatives are finite codes, not literal graph pieces.  This is the
form needed when CT3 compares bounded local signatures or lengths and a
separate graph interpretation turns the winning code into an actual
replacement piece. -/
private structure CodedReflection where
  replacement : PackedBoundariedGluing.Piece T
  boundaryProfile_eq :
    PackedBoundariedGluing.MinimumDegreeCycleReplacement.BoundaryDegreeProfile
        boundaries replacement =
      PackedBoundariedGluing.MinimumDegreeCycleReplacement.BoundaryDegreeProfile
        boundaries atom.source
  encode :
    PackedBoundariedGluing.Context T → table.Outside
  replacement_reflect : ∀ outside,
    table.targetResponseReplacement (encode outside) ↔
      input.Target (PackedBoundariedGluing.glue boundaries replacement outside)
  source_reflect : ∀ outside,
    table.targetResponseSource (encode outside) ↔
      input.Target
        (PackedBoundariedGluing.glue boundaries atom.source outside)

namespace CodedReflection

variable {input boundaries atom representatives table}

/-- Convert finite target-completeness on codes into packed-boundary target
completeness after semantic reflection identifies the coded responses with
literal graph gluing responses. -/
private theorem targetComplete
    (reflection :
      CodedReflection input boundaries atom representatives table)
    {boundary :
      FiniteSameInterfaceExchange.BoundaryCompatible representatives}
    (complete :
      FiniteSameInterfaceExchange.TargetComplete
        representatives boundary table) :
    PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetComplete
      input boundaries reflection.replacement atom.source := by
  refine ⟨reflection.boundaryProfile_eq, ?_⟩
  intro outside
  have universal := complete.universal (reflection.encode outside)
  constructor
  · intro replacementTarget
    exact (reflection.source_reflect outside).mp
      (universal.mp
        ((reflection.replacement_reflect outside).mpr replacementTarget))
  · intro sourceTarget
    exact (reflection.replacement_reflect outside).mp
      (universal.mpr
        ((reflection.source_reflect outside).mpr sourceTarget))

end CodedReflection

/-- Local graph admissibility facts for a coded finite replacement. -/
private structure CodedAdmissible
    (reflection :
      CodedReflection input boundaries atom representatives table) where
  internalTargetFree :
    ¬ input.Target
      (PackedBoundariedGluing.Piece.pack boundaries reflection.replacement)
  internalBaseline :
    reflection.replacement.InternalBaseline boundaries input.minimumDegree
  locallySmaller :
    PackedBoundariedGluing.Piece.LexSmaller
      reflection.replacement atom.source

namespace CodedAdmissible

variable [Nonempty T]
variable {input boundaries atom representatives table}
variable {boundary :
  FiniteSameInterfaceExchange.BoundaryCompatible representatives}

/-- Framework-owned orientation from a coded finite table to a literal
packed-boundary silent exchange. -/
private noncomputable def silentExchange
    {reflection :
      CodedReflection input boundaries atom representatives table}
    (admissible :
      CodedAdmissible input boundaries atom representatives table reflection)
    {boundary :
      FiniteSameInterfaceExchange.BoundaryCompatible representatives}
    (complete :
      FiniteSameInterfaceExchange.TargetComplete
        representatives boundary table) :
    PackedBoundariedGluing.MinimumDegreeCycleReplacement.SilentExchange
      input boundaries atom where
  replacement := reflection.replacement
  targetComplete := reflection.targetComplete complete
  internalTargetFree := admissible.internalTargetFree
  internalBaseline := admissible.internalBaseline
  locallySmaller := admissible.locallySmaller

/-- Reusable closure theorem for a coded finite same-interface replacement. -/
private theorem impossible
    {reflection :
      CodedReflection input boundaries atom representatives table}
    (admissible :
      CodedAdmissible input boundaries atom representatives table reflection)
    {boundary :
      FiniteSameInterfaceExchange.BoundaryCompatible representatives}
    (complete :
      FiniteSameInterfaceExchange.TargetComplete
        representatives boundary table) :
    False :=
  (admissible.silentExchange complete).impossible

/-- Coded replacement packaged behind the generic finite same-interface
orientation interface. -/
private noncomputable def conditionalSilent
    (reflection :
      CodedReflection input boundaries atom representatives table)
    (admissible :
      CodedAdmissible input boundaries atom representatives table reflection) :
    {boundary :
      FiniteSameInterfaceExchange.BoundaryCompatible representatives} →
    FiniteSameInterfaceExchange.ConditionalSilent
      representatives boundary table :=
  fun {_boundary} => {
    Silent :=
      PackedBoundariedGluing.MinimumDegreeCycleReplacement.SilentExchange
        input boundaries atom
    orient := fun _changing complete =>
      admissible.silentExchange complete }

end CodedAdmissible

/-- A fully parameterized coded same-interface compression profile.  The
problem layer supplies the mathematical interpretation of its finite code
table: which literal replacement piece a code denotes, how coded responses
reflect packed-boundary gluing responses, and how the code size agrees with
internal vertex counts.  The framework derives target completeness,
admissibility, strict local decrease, silent exchange routing, and closure. -/
structure CodedCompressionProfile where
  replacement : PackedBoundariedGluing.Piece T
  boundaryProfile_eq :
    PackedBoundariedGluing.MinimumDegreeCycleReplacement.BoundaryDegreeProfile
        boundaries replacement =
      PackedBoundariedGluing.MinimumDegreeCycleReplacement.BoundaryDegreeProfile
        boundaries atom.source
  encode :
    PackedBoundariedGluing.Context T → table.Outside
  replacement_reflect : ∀ outside,
    table.targetResponseReplacement (encode outside) ↔
      input.Target (PackedBoundariedGluing.glue boundaries replacement outside)
  source_reflect : ∀ outside,
    table.targetResponseSource (encode outside) ↔
      input.Target
        (PackedBoundariedGluing.glue boundaries atom.source outside)
  internalTargetFree :
    ¬ input.Target (PackedBoundariedGluing.Piece.pack boundaries replacement)
  internalBaseline :
    replacement.InternalBaseline boundaries input.minimumDegree
  source_size_eq :
    representatives.size representatives.source = atom.source.internalVertexCount
  replacement_size_eq :
    representatives.size representatives.replacement =
      replacement.internalVertexCount
  size_decreases :
    representatives.size representatives.replacement <
      representatives.size representatives.source

namespace CodedCompressionProfile

variable {input boundaries atom representatives table}

/-- Framework-built semantic reflection from the problem's interpretation
parameters. -/
private def reflection
    (profile :
      CodedCompressionProfile input boundaries atom representatives table) :
    CodedReflection input boundaries atom representatives table where
  replacement := profile.replacement
  boundaryProfile_eq := profile.boundaryProfile_eq
  encode := profile.encode
  replacement_reflect := profile.replacement_reflect
  source_reflect := profile.source_reflect

/-- Framework derivation of the strict packed-boundary local order from the
finite code-size decrease and the supplied size interpretation. -/
theorem locallySmaller
    (profile :
      CodedCompressionProfile input boundaries atom representatives table) :
    PackedBoundariedGluing.Piece.LexSmaller
      profile.replacement atom.source := by
  left
  rw [← profile.replacement_size_eq, ← profile.source_size_eq]
  exact profile.size_decreases

/-- Framework-built admissibility package.  Application code should supply
`CodedCompressionProfile` rather than manually assembling this object. -/
private def admissible
    (profile :
      CodedCompressionProfile input boundaries atom representatives table) :
    CodedAdmissible input boundaries atom representatives table
      profile.reflection where
  internalTargetFree := profile.internalTargetFree
  internalBaseline := profile.internalBaseline
  locallySmaller := profile.locallySmaller

/-- Target completeness transported from the finite code table to literal
packed-boundary gluing. -/
theorem targetComplete
    (profile :
      CodedCompressionProfile input boundaries atom representatives table)
    {boundary :
      FiniteSameInterfaceExchange.BoundaryCompatible representatives}
    (complete :
      FiniteSameInterfaceExchange.TargetComplete
        representatives boundary table) :
    PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetComplete
      input boundaries profile.replacement atom.source :=
  profile.reflection.targetComplete complete

variable [Nonempty T]

/-- Public framework executor for a coded same-interface compression profile:
finite target completeness plus the local interpretation profile produce the
literal packed-boundary silent exchange. -/
noncomputable def silentExchange
    (profile :
      CodedCompressionProfile input boundaries atom representatives table)
    {boundary :
      FiniteSameInterfaceExchange.BoundaryCompatible representatives}
    (complete :
      FiniteSameInterfaceExchange.TargetComplete
        representatives boundary table) :
    PackedBoundariedGluing.MinimumDegreeCycleReplacement.SilentExchange
      input boundaries atom :=
  profile.admissible.silentExchange complete

/-- Public framework closure theorem for coded same-interface compression.
Downstream proof nodes should call this theorem, not manually construct a
`SilentExchange`. -/
theorem impossible
    (profile :
      CodedCompressionProfile input boundaries atom representatives table)
    {boundary :
      FiniteSameInterfaceExchange.BoundaryCompatible representatives}
    (complete :
      FiniteSameInterfaceExchange.TargetComplete
        representatives boundary table) :
    False :=
  profile.admissible.impossible complete

/-- Same executor exposed through the generic finite same-interface
orientation interface. -/
noncomputable def conditionalSilent
    (profile :
      CodedCompressionProfile input boundaries atom representatives table) :
    {boundary :
      FiniteSameInterfaceExchange.BoundaryCompatible representatives} →
    FiniteSameInterfaceExchange.ConditionalSilent
      representatives boundary table :=
  profile.admissible.conditionalSilent

end CodedCompressionProfile

/-- Framework-owned closure certificate for a coded same-interface
compression.  It is parameterized only by the generic graph/profile data:
applications instantiate the profile and provide the finite
target-completeness certificate from their ledger. -/
structure ClosureCertificate
    (boundary :
      FiniteSameInterfaceExchange.BoundaryCompatible representatives) where
  profile :
    CodedCompressionProfile input boundaries atom representatives table
  complete :
    FiniteSameInterfaceExchange.TargetComplete representatives boundary table

namespace ClosureCertificate

variable [Nonempty T]
variable {input boundaries atom representatives table}
variable {boundary :
  FiniteSameInterfaceExchange.BoundaryCompatible representatives}

/-- The graph-layer silent exchange generated automatically from the closure
certificate. -/
noncomputable def silentExchange
    (certificate :
      ClosureCertificate input boundaries atom representatives table boundary) :
    PackedBoundariedGluing.MinimumDegreeCycleReplacement.SilentExchange
      input boundaries atom :=
  certificate.profile.silentExchange certificate.complete

/-- The generic closure theorem: once the profile and finite completeness are
registered, the framework closes by target-complete packed replacement. -/
theorem impossible
    (certificate :
      ClosureCertificate input boundaries atom representatives table boundary) :
    False :=
  certificate.profile.impossible certificate.complete

/-- The closure as a conditional finite same-interface orientation. -/
noncomputable def conditionalSilent
    (certificate :
      ClosureCertificate input boundaries atom representatives table boundary) :
    FiniteSameInterfaceExchange.ConditionalSilent
      representatives boundary table :=
  certificate.profile.conditionalSilent

/-- Framework-owned branch closer for coded same-interface compression.
It consumes the exact accumulated focused yes-continuation, asks the
application only for the closure certificate attached to that latest payload,
and delegates all branch transport to Core and all compression closure to the
graph profile. -/
noncomputable def closeFocusedBranchYesContinuation
    {Residual : Type u}
    {facts : List (Residual → Prop)}
    {Bypass Active : Residual → Type u}
    {yes no : (residual : Residual) → Active residual → Prop}
    {Output : (residual : Residual) → (data : Active residual) →
      yes residual data → Sort u}
    {T CodePiece : Type u} [Nonempty T]
    (inputOf : ∀ residual data proof,
      Output residual data proof → PackedMinimumDegreeCycle.StaticInput)
    (boundariesOf : ∀ _residual _data _proof _output, FinEnum T)
    (ctxOf : ∀ residual data proof output,
      Core.MinimalCounterexampleContext
        (inputOf residual data proof output).problem
        (inputOf residual data proof output).Target)
    (atomOf : ∀ residual data proof output,
      PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom
        (inputOf residual data proof output)
        (boundariesOf residual data proof output)
        (ctxOf residual data proof output))
    (representativesOf : ∀ _residual _data _proof _output,
      FiniteSameInterfaceExchange.Representatives CodePiece)
    (tableOf : ∀ residual data proof output,
      FiniteSameInterfaceExchange.ResponseTable
        (representativesOf residual data proof output))
    (boundaryOf : ∀ residual data proof output,
      FiniteSameInterfaceExchange.BoundaryCompatible
        (representativesOf residual data proof output))
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        (Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
          Bypass Active yes no Output)) facts]
    (certificate : ∀ residual data proof output,
      ClosureCertificate
        (inputOf residual data proof output)
        (boundariesOf residual data proof output)
        (atomOf residual data proof output)
        (representativesOf residual data proof output)
        (tableOf residual data proof output)
        (boundaryOf residual data proof output)) :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (Core.ResidualRefinement.State.FocusedBranchDecisionYesClosed
        Bypass Active yes no) :=
  Core.ResidualRefinement.State.StageNode.closeFocusedBranchYesContinuation
    fun residual data proof output =>
      (certificate residual data proof output).impossible

end ClosureCertificate

end Coded

end MinimumDegreeCycleReplacement

end StructuralExhaustion.Graph.FiniteSameInterfaceExchange.PackedBoundary
