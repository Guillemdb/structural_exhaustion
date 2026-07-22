import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Metadata
import Hypostructure.Core.Residual.Focus
import Hypostructure.Graph.Gluing
import Hypostructure.Graph.Minimality
import Hypostructure.Graph.Response

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

/-- The atom side transported to the ambient vertex carrier. -/
noncomputable def pieceImage {object : FiniteObject.{u}}
    (decomposition : OwnedDecomposition object) : FiniteObject.{u} where
  Vertex := object.Vertex
  graph := decomposition.piece.graph.map decomposition.pieceIntoAmbient
  vertices := object.vertices
  decideAdj := Classical.decRel _

/-- Intrinsic paper properness for one embedded side: it does not contain both
all ambient vertices and all ambient edges.  This is the typed form of
`X ≠ G` for graphs represented on different finite carriers. -/
def IsProperSide {object : FiniteObject.{u}}
    (decomposition : OwnedDecomposition object) : Prop :=
  ¬ (Function.Surjective decomposition.pieceIntoAmbient ∧
    decomposition.pieceImage.graph = object.graph)

/-- Omitting an ambient vertex strictly decreases the finite vertex count. -/
theorem piece_vertexCount_lt_of_not_surjective
    {object : FiniteObject.{u}} (decomposition : OwnedDecomposition object)
    (notSurjective :
      ¬ Function.Surjective decomposition.pieceIntoAmbient) :
    decomposition.piece.pack.vertexCount < object.vertexCount := by
  letI : Fintype decomposition.piece.pack.Vertex :=
    @FinEnum.instFintype _ decomposition.piece.pack.vertices
  letI : Fintype object.Vertex :=
    @FinEnum.instFintype _ object.vertices
  change decomposition.piece.pack.vertices.card < object.vertices.card
  rw [@FinEnum.card_eq_fintypeCard _ decomposition.piece.pack.vertices
      (@FinEnum.instFintype _ decomposition.piece.pack.vertices),
    @FinEnum.card_eq_fintypeCard _ object.vertices
      (@FinEnum.instFintype _ object.vertices)]
  exact Fintype.card_lt_of_injective_not_surjective
    decomposition.pieceIntoAmbient
    decomposition.pieceIntoAmbient.injective notSurjective

/-- Mapping a finite simple graph along an embedding preserves its exact edge
count. -/
theorem pieceImage_edgeCount
    {object : FiniteObject.{u}} (decomposition : OwnedDecomposition object) :
    decomposition.pieceImage.edgeCount =
      decomposition.piece.pack.edgeCount := by
  letI : Fintype
      (decomposition.interface.Vertex ⊕ decomposition.piece.Internal) :=
    @FinEnum.instFintype _ decomposition.piece.pack.vertices
  letI : Fintype decomposition.piece.pack.Vertex :=
    @FinEnum.instFintype _ decomposition.piece.pack.vertices
  letI : Fintype object.Vertex :=
    @FinEnum.instFintype _ object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel decomposition.piece.graph.Adj :=
    decomposition.piece.decideAdj
  letI : DecidableRel decomposition.pieceImage.graph.Adj :=
    decomposition.pieceImage.decideAdj
  rw [FiniteObject.edgeCount_eq_ncard_edgeSet,
    FiniteObject.edgeCount_eq_ncard_edgeSet]
  change
    (decomposition.piece.graph.map
      decomposition.pieceIntoAmbient).edgeSet.ncard =
        decomposition.piece.graph.edgeSet.ncard
  simpa only [Set.ncard_eq_toFinset_card', SimpleGraph.edgeFinset] using
    (SimpleGraph.card_edgeFinset_map
      decomposition.pieceIntoAmbient decomposition.piece.graph)

/-- A spanning atom side that still omits an ambient edge strictly decreases
the finite edge count. -/
theorem piece_edgeCount_lt_of_spanning_of_graph_ne
    {object : FiniteObject.{u}} (decomposition : OwnedDecomposition object)
    (_spanning : Function.Surjective decomposition.pieceIntoAmbient)
    (graphNe : decomposition.pieceImage.graph ≠ object.graph) :
    decomposition.piece.pack.edgeCount < object.edgeCount := by
  letI : Fintype object.Vertex :=
    @FinEnum.instFintype _ object.vertices
  have graphLt : decomposition.pieceImage.graph < object.graph :=
    lt_of_le_of_ne decomposition.piece_map_le graphNe
  rw [← decomposition.pieceImage_edgeCount]
  rw [FiniteObject.edgeCount_eq_ncard_edgeSet,
    FiniteObject.edgeCount_eq_ncard_edgeSet]
  exact Set.ncard_lt_ncard (SimpleGraph.edgeSet_strict_mono graphLt)
    (Set.toFinite object.graph.edgeSet)

/-- Paper properness and exact decomposition imply the strict graph progress
used by the minimal-counterexample framework. -/
theorem piece_lexicographicallySmaller
    {object : FiniteObject.{u}} (decomposition : OwnedDecomposition object)
    (proper : decomposition.IsProperSide) :
    decomposition.piece.pack.LexicographicallySmaller object := by
  by_cases spanning : Function.Surjective decomposition.pieceIntoAmbient
  · have graphNe : decomposition.pieceImage.graph ≠ object.graph := by
      intro graphEq
      exact proper ⟨spanning, graphEq⟩
    apply FiniteObject.lexicographicallySmaller_of_vertexCount_eq_edgeCount_lt
    · letI : Fintype decomposition.piece.pack.Vertex :=
        @FinEnum.instFintype _ decomposition.piece.pack.vertices
      letI : Fintype object.Vertex :=
        @FinEnum.instFintype _ object.vertices
      change decomposition.piece.pack.vertices.card = object.vertices.card
      rw [@FinEnum.card_eq_fintypeCard _ decomposition.piece.pack.vertices
          (@FinEnum.instFintype _ decomposition.piece.pack.vertices),
        @FinEnum.card_eq_fintypeCard _ object.vertices
          (@FinEnum.instFintype _ object.vertices)]
      exact Fintype.card_congr
        (Equiv.ofBijective decomposition.pieceIntoAmbient
          ⟨decomposition.pieceIntoAmbient.injective, spanning⟩)
    · exact decomposition.piece_edgeCount_lt_of_spanning_of_graph_ne
        spanning graphNe
  · exact FiniteObject.lexicographicallySmaller_of_vertexCount_lt
      (decomposition.piece_vertexCount_lt_of_not_surjective spanning)

end OwnedDecomposition

/-- A connected atom occurrence that is intrinsically proper in its ambient
graph.  Exact edge ownership and reconstruction come from
`OwnedDecomposition`; Graph derives strict progress and ordinary
proper-subgraph inclusion from those fields. -/
structure ProperBoundariedAtom (object : FiniteObject.{u}) where
  decomposition : OwnedDecomposition object
  connected : decomposition.piece.graph.Connected
  proper : decomposition.IsProperSide

namespace ProperBoundariedAtom

/-- Strict graph progress is derived by Graph from intrinsic atom
properness; it is not an application-provided certificate. -/
theorem decreases {object : FiniteObject.{u}}
    (atom : ProperBoundariedAtom object) :
    atom.decomposition.piece.pack.LexicographicallySmaller object :=
  atom.decomposition.piece_lexicographicallySmaller atom.proper

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

/-! ## Complete graph-owned registration -/

/-- Target-complete identification in the immutable uncapped
boundary-degree fibre required by the boundaried-atom argument. -/
abbrev BoundaryProfileTargetComplete
    {boundary : Boundary.{u}}
    (Target : FiniteObject.{u} → Prop)
    (left right : BoundaryPiece boundary) : Prop :=
  Response.TargetComplete
    (fun piece : BoundaryPiece boundary => piece.boundaryDegreeProfile)
    Target left right

/-- A pointwise proof projection performs no primitive finite inspection.
The ambient graph size is retained as the uniform accounting input. -/
def boundariedAtomWorkBudget :
    Core.PolynomialCheckBudget FiniteObject.{u} :=
  Core.PolynomialCheckBudget.zero fun object =>
    object.vertexCount + object.edgeCount

/-- Complete Graph-owned result for the boundaried-atom node.  Its private
constructor prevents applications from supplying profiles, profile-fibre
rules, or work claims independently of the framework derivation. -/
structure BoundariedAtomRegistration
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) where
  private mk ::
  family : BoundariedAtomFamily ctx
  profileMismatchRejected :
    ∀ {boundary : Boundary.{u}} {left right : BoundaryPiece boundary},
      left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile →
        ¬ BoundaryProfileTargetComplete Target left right
  checks : Nat
  checks_eq_zero : checks = 0

namespace BoundariedAtomRegistration

/-- The registered proof-only execution satisfies Graph's uniform polynomial
work envelope. -/
theorem work_bounded
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)}
    (registration : BoundariedAtomRegistration ctx) :
    registration.checks ≤
      boundariedAtomWorkBudget.coefficient *
        (boundariedAtomWorkBudget.size ctx.G + 1) ^
          boundariedAtomWorkBudget.degree := by
  rw [registration.checks_eq_zero]
  exact Nat.zero_le _

end BoundariedAtomRegistration

/-- Derive every atom profile, the mandatory profile-fibre rejection rule,
and the exact proof-only work count from the inherited minimal context. -/
def deriveBoundariedAtomRegistration
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) :
    BoundariedAtomRegistration ctx where
  family := deriveBoundariedAtomFamily ctx
  profileMismatchRejected := by
    intro boundary left right different
    exact Response.profile_ne_not_targetComplete different
  checks := 0
  checks_eq_zero := rfl

/-! ## Focused accumulated execution -/

/-- Private Graph-owned execution certificate. The registration and exact
focus-selection count are produced together by one counted Core execution. -/
structure FocusedBoundariedAtomCertificate
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
    (previous : Previous) (active : focus.Active previous) where
  private mk ::
  registration : BoundariedAtomRegistration (context.read previous active)
  checks : Nat
  checks_eq_budget : checks = focus.selectionBudget.checks previous

namespace FocusedBoundariedAtomCertificate

theorem work_bounded
    {Previous : Type uPrevious}
    {focus : Core.Residual.Focus.Profile Previous}
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))}
    {previous : Previous} {active : focus.Active previous}
    (certificate : FocusedBoundariedAtomCertificate
      focus context previous active) :
    certificate.checks <=
      focus.selectionBudget.coefficient *
        (focus.selectionBudget.size previous + 1) ^
          focus.selectionBudget.degree := by
  rw [certificate.checks_eq_budget]
  exact focus.selectionBudget.bounded previous

/-- Predicate-form work theorem for an active boundaried-atom certificate. -/
theorem work_within
    {Previous : Type uPrevious}
    {focus : Core.Residual.Focus.Profile Previous}
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))}
    {previous : Previous} {active : focus.Active previous}
    (certificate : FocusedBoundariedAtomCertificate
      focus context previous active) :
    focus.selectionBudget.Within previous certificate.checks :=
  certificate.work_bounded

end FocusedBoundariedAtomCertificate

/-- Complete Graph-owned certificate generated on one active
minimal-context branch. -/
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
  FocusedBoundariedAtomCertificate focus context previous active

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

/-- Execute the complete boundaried-atom registration and branch selection as
one counted computation. -/
def executeFocusedBoundariedAtomRegistrationCounted
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
    Core.Counted (FocusedBoundariedAtomStage focus context) :=
  Core.Residual.Focus.runCounted focus previous fun active checks exact =>
    .mk (deriveBoundariedAtomRegistration (context.read previous active))
      checks exact

/-- Public focused successor; exact work remains stored in its private latest
certificate and coupled to the counted execution that produced the stage. -/
def executeFocusedBoundariedAtomRegistration
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
  (executeFocusedBoundariedAtomRegistrationCounted
    focus context previous).value

@[simp] theorem executeFocusedBoundariedAtomRegistrationCounted_checks
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
    (executeFocusedBoundariedAtomRegistrationCounted
      focus context previous).checks =
        focus.selectionBudget.checks previous :=
  Core.Residual.Focus.runCounted_checks focus previous _

/-- The complete counted registration, including inactive outcomes, satisfies
the inherited focus-selection envelope. -/
theorem executeFocusedBoundariedAtomRegistrationCounted_checks_bounded
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
    (executeFocusedBoundariedAtomRegistrationCounted
      focus context previous).checks <=
        focus.selectionBudget.coefficient *
          (focus.selectionBudget.size previous + 1) ^
            focus.selectionBudget.degree := by
  rw [executeFocusedBoundariedAtomRegistrationCounted_checks]
  exact focus.selectionBudget.bounded previous

/-- Predicate-form work theorem for focused boundaried-atom registration. -/
theorem executeFocusedBoundariedAtomRegistrationCounted_work_within
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
    focus.selectionBudget.Within previous
      (executeFocusedBoundariedAtomRegistrationCounted focus context
        previous).checks :=
  executeFocusedBoundariedAtomRegistrationCounted_checks_bounded focus context
    previous

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

/-- Query the private Graph execution certificate from the newest extension. -/
def focusedBoundariedAtomCertificateQuery
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

/-- Project only the Graph-generated atom registration from the exact latest
execution certificate. -/
def focusedBoundariedAtomRegistrationQuery
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
        BoundariedAtomRegistration (context.read stage.previous active)) :=
  (focusedBoundariedAtomCertificateQuery focus context).map
    fun _stage _active certificate => certificate.registration

/-! ## Proof-relevant declaration metadata -/

/-- Canonical audit record for the focused boundaried-atom executor.  It
stores the actual active context query and the exact work budget rather than
describing either one only in prose. -/
def focusedBoundariedAtomMetadata
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
    Core.Metadata.DeclarationMetadata Previous Previous where
  declaration :=
    ⟨"Hypostructure.Graph.BoundariedAtom",
      "executeFocusedBoundariedAtomRegistration"⟩
  primitiveInputs := [
    ⟨⟨"Hypostructure.Graph.BoundariedAtom", "ProperBoundariedAtom"⟩,
      .localCertificate⟩
  ]
  inferredDependencies := [
    ⟨⟨"Hypostructure.Core.Residual.Focus", "ActiveQuery"⟩,
      .predecessorProjection⟩,
    ⟨⟨"Hypostructure.Graph.BoundariedAtom",
      "deriveBoundariedAtomRegistration"⟩, .registeredProfile⟩
  ]
  ledgerQueries := []
  focusedLedgerQueries := [{
    source := ⟨"Hypostructure.Core.Residual.Focus", "ActiveQuery"⟩
    profile := focus
    Result := fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState)
    query := context
  }]
  frameworkSearch := []
  generatedOutputs := [
    ⟨⟨"Hypostructure.Graph.BoundariedAtom",
      "deriveBoundariedAtomRegistration"⟩, .auditRecord⟩,
    ⟨⟨"Hypostructure.Core.Residual.Focus", "runCounted"⟩, .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Graph.BoundariedAtom",
      "OwnedDecomposition.piece_lexicographicallySmaller"⟩,
    ⟨"Hypostructure.Graph.Response",
      "profile_ne_not_targetComplete"⟩,
    ⟨"Hypostructure.Graph.BoundariedAtom",
      "FocusedBoundariedAtomCertificate.work_bounded"⟩
  ]
  workBound := focus.selectionBudget
  manualObligations := []

/-- The canonical executor metadata has no unresolved manual obligation. -/
def focusedBoundariedAtomMetadataComplete
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
    Core.Metadata.Complete
      (focusedBoundariedAtomMetadata focus context) :=
  ⟨rfl⟩

end Hypostructure.Graph
