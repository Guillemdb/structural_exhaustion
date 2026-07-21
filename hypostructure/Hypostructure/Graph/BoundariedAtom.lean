import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Hypostructure.Core.Residual.Focus
import Hypostructure.Graph.Gluing
import Hypostructure.Graph.Minimality

/-!
# Proper connected boundaried atoms

This module packages the graph-local data used by a boundaried-atom node.
An atom is supplied pointwise as an exact `OwnedDecomposition`; Graph derives
its ordinary proper-subgraph certificate and its uncapped boundary-degree
profile.  No ambient family of graphs, interfaces, or sites is enumerated.

The focused executor consumes only an inherited minimal-counterexample context.
Core owns the active-branch decision and the single accumulated-ledger
extension.
-/

namespace Hypostructure.Graph

universe u v uPrevious

namespace BoundaryPiece

/-- Number of edges locally owned by a boundary piece. -/
def edgeCount {boundary : Boundary.{u}} (piece : BoundaryPiece boundary) : Nat :=
  piece.pack.edgeCount

/-- The local replacement measure omits the fixed boundary from its vertex
coordinate and then counts the edges owned by the piece. -/
def localLexicographicSize {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) : LexicographicSize :=
  (piece.internalVertexCount, piece.edgeCount)

/-- Strict local replacement progress for two pieces with the same labelled
boundary. -/
def LocallySmaller {boundary : Boundary.{u}}
    (replacement source : BoundaryPiece boundary) : Prop :=
  Prod.Lex (· < ·) (· < ·)
    replacement.localLexicographicSize source.localLexicographicSize

theorem locallySmaller_iff {boundary : Boundary.{u}}
    {replacement source : BoundaryPiece boundary} :
    replacement.LocallySmaller source ↔
      replacement.internalVertexCount < source.internalVertexCount ∨
        (replacement.internalVertexCount = source.internalVertexCount ∧
          replacement.edgeCount < source.edgeCount) := by
  simp only [LocallySmaller, localLexicographicSize, Prod.lex_iff]

/-- Degree contributed by the piece at one labelled boundary vertex.  Outside
incidences are deliberately absent, so this is the uncapped local degree. -/
def boundaryDegree {boundary : Boundary.{u}} (piece : BoundaryPiece boundary)
    (vertex : boundary.Vertex) : Nat :=
  piece.pack.degree (.inl vertex)

/-- The complete uncapped boundary-degree vector of one piece. -/
def boundaryDegreeProfile {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) : boundary.Vertex → Nat :=
  piece.boundaryDegree

/-- Minimum-degree requirement restricted to the internal vertices of a
piece.  It is independent of any theorem-specific threshold. -/
def InternalThresholdBaseline {boundary : Boundary.{u}} (threshold : Nat)
    (piece : BoundaryPiece boundary) : Prop :=
  ∀ internal : piece.Internal,
    threshold ≤ piece.pack.degree (.inr internal)

end BoundaryPiece

/-- The uncapped boundary-degree profile carrier for one labelled interface. -/
abbrev BoundaryDegreeProfile (boundary : Boundary.{u}) :=
  boundary.Vertex → Nat

namespace OwnedDecomposition

/-- Canonical embedding of the atom side into the ambient graph reconstructed
by an owned decomposition. -/
def pieceIntoAmbient {object : FiniteObject.{u}}
    (decomposition : OwnedDecomposition object) :
    (decomposition.interface.Vertex ⊕ decomposition.piece.Internal) ↪
      object.Vertex where
  toFun := fun vertex => decomposition.vertexEquiv
    (pieceEmbedding decomposition.piece decomposition.outside vertex)
  inj' := decomposition.vertexEquiv.injective.comp
    (pieceEmbedding decomposition.piece decomposition.outside).injective

/-- Every atom-side edge is an ambient edge, by exact ownership. -/
theorem piece_map_le {object : FiniteObject.{u}}
    (decomposition : OwnedDecomposition object) :
    decomposition.piece.graph.map decomposition.pieceIntoAmbient ≤
      object.graph := by
  intro left right adjacent
  rcases (SimpleGraph.map_adj decomposition.pieceIntoAmbient
      decomposition.piece.graph left right).mp adjacent with
    ⟨pieceLeft, pieceRight, pieceAdjacent, leftEq, rightEq⟩
  subst left
  subst right
  apply (decomposition.ownsAdjacency
    (pieceEmbedding decomposition.piece decomposition.outside pieceLeft)
    (pieceEmbedding decomposition.piece decomposition.outside pieceRight)).mpr
  exact Or.inl ⟨pieceLeft, pieceRight, pieceAdjacent, rfl, rfl⟩

end OwnedDecomposition

/-- A supplied connected atom occurrence with genuine strict graph progress.
Exact edge ownership and reconstruction come from `OwnedDecomposition`; Graph
derives ordinary proper-subgraph inclusion from those fields. -/
structure ProperBoundariedAtom (object : FiniteObject.{u}) where
  decomposition : OwnedDecomposition object
  connected : decomposition.piece.graph.Connected
  decreases : decomposition.piece.pack.LexicographicallySmaller object

namespace ProperBoundariedAtom

/-- The atom side as a certified proper subgraph of its ambient graph. -/
def properSubgraph {object : FiniteObject.{u}}
    (atom : ProperBoundariedAtom object) : ProperSubgraph object where
  value := atom.decomposition.piece.pack
  vertexEmbedding := atom.decomposition.pieceIntoAmbient
  included := atom.decomposition.piece_map_le
  decreases := atom.decreases

/-- The atom side strictly decreases the registered generic graph progress. -/
theorem smaller
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {object : FiniteObject.{u}} (atom : ProperBoundariedAtom object) :
    (lexicographicProgress Baseline BranchState).Smaller
      atom.decomposition.piece.pack object :=
  atom.decreases

end ProperBoundariedAtom

/-- Graph-owned evidence registered for one supplied proper connected atom.
The private constructor prevents callers from registering a guessed profile. -/
structure BoundariedAtomProfileCertificate
    {object : FiniteObject.{u}} (atom : ProperBoundariedAtom object) where
  private mk ::
  properSubgraph : ProperSubgraph object
  boundaryDegreeProfile : BoundaryDegreeProfile atom.decomposition.interface
  profile_eq : boundaryDegreeProfile =
    atom.decomposition.piece.boundaryDegreeProfile

namespace BoundariedAtomProfileCertificate

/-- Read one exact coordinate of the generated uncapped profile. -/
theorem profile_apply
    {object : FiniteObject.{u}} {atom : ProperBoundariedAtom object}
    (certificate : BoundariedAtomProfileCertificate atom)
    (vertex : atom.decomposition.interface.Vertex) :
    certificate.boundaryDegreeProfile vertex =
      atom.decomposition.piece.boundaryDegree vertex := by
  rw [certificate.profile_eq]
  rfl

end BoundariedAtomProfileCertificate

/-- Derive the proper-subgraph and uncapped profile evidence for one atom. -/
def deriveBoundariedAtomProfile
    {object : FiniteObject.{u}} (atom : ProperBoundariedAtom object) :
    BoundariedAtomProfileCertificate atom where
  properSubgraph := atom.properSubgraph
  boundaryDegreeProfile := atom.decomposition.piece.boundaryDegreeProfile
  profile_eq := rfl

/-- Universal pointwise family over supplied typed proper connected atoms.
This is a dependent function, not an enumeration of ambient graphs or sites. -/
abbrev BoundariedAtomFamily
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) :=
  ∀ atom : ProperBoundariedAtom ctx.G,
    BoundariedAtomProfileCertificate atom

/-- Framework derivation of the complete pointwise atom family. -/
def deriveBoundariedAtomFamily
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) :
    BoundariedAtomFamily ctx :=
  fun atom => deriveBoundariedAtomProfile atom

/-! ## Focused accumulated execution -/

/-- Graph-owned output generated on one active minimal-context branch. -/
abbrev FocusedBoundariedAtomOutput
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (previous : Previous) (active : focus.Active previous) :=
  BoundariedAtomFamily (context.read previous active)

/-- Exact accumulated successor carrying the generated atom family. -/
abbrev FocusedBoundariedAtomStage
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :=
  Core.Residual.Focus.Stage focus
    (FocusedBoundariedAtomOutput focus context)

/-- Execute the pointwise atom-family registration on the active branch.
`Focus.run` owns both routing constructors and the sole ledger extension. -/
def executeFocusedBoundariedAtomFamily
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (previous : Previous) :
    FocusedBoundariedAtomStage focus context :=
  Core.Residual.Focus.run focus previous fun active =>
    deriveBoundariedAtomFamily (context.read previous active)

/-- Active branch inherited after the atom-family registration. -/
abbrev FocusedBoundariedAtomProfile
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :=
  Core.Residual.Focus.successor focus
    (FocusedBoundariedAtomOutput focus context)

/-- Query the exact Graph-generated atom family from the newest extension. -/
def focusedBoundariedAtomFamilyQuery
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :
    Core.Residual.Focus.ActiveQuery
      (FocusedBoundariedAtomProfile focus context)
      (fun stage active =>
        FocusedBoundariedAtomOutput focus context stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

end Hypostructure.Graph
