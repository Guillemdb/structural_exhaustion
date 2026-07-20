import StructuralExhaustion.CT15.SupportStratifiedRank
import StructuralExhaustion.Graph.BoundariedRankDrop

namespace StructuralExhaustion.Graph.SupportStratifiedDetermination

open StructuralExhaustion
open StructuralExhaustion.Graph.PackedBoundariedGluing

universe u v

variable (input : PackedMinimumDegreeCycle.StaticInput)
variable (ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target)
variable (Coordinate : Type v)

/-!
# Graph interfaces for support-stratified rank certificates

The manuscript's rank circuit is evaluated twice: first at its final connected
carrier and then at the smaller atom from which the declared coordinates
originated.  An `Interface` stores one literal boundaried graph interface,
including its own boundary type, outside-context type, exact target response,
and reconstruction in the selected graph.  Thus two nested supports may have
genuinely different context types; no ambient context family is enumerated.
-/

/-- The graph data common to a proper or whole connected support. -/
structure InterfaceBase where
  Boundary : Type u
  boundaries : FinEnum Boundary
  source : Piece Boundary
  outside : Context Boundary
  reconstruct :
    (glue boundaries source outside).object.graph ≃g ctx.G.object.graph
  connected : source.graph.Connected
  coordinatePiece : Coordinate → Piece Boundary
  vertices : Finset ctx.G.Vertex

namespace InterfaceBase

/-- Turn a strict interface into the literal proper atom consumed by the
boundaried CT3 replacement route. -/
def properAtom (base : InterfaceBase input ctx Coordinate)
    (_boundaryNonempty : Nonempty base.Boundary)
    (proper : (Piece.pack base.boundaries base.source).lexRank < ctx.G.lexRank) :
    MinimumDegreeCycleReplacement.ProperAtom input base.boundaries ctx where
  source := base.source
  outside := base.outside
  reconstruct := base.reconstruct
  connected := base.connected
  proper := proper

end InterfaceBase

/-- The existing node-[41] dichotomy, stored on one graph interface. -/
inductive Scope (base : InterfaceBase input ctx Coordinate) where
  | proper
      (boundaryNonempty : Nonempty base.Boundary)
      (rank_lt : (Piece.pack base.boundaries base.source).lexRank < ctx.G.lexRank)
  | whole
      (closedReconstruct :
        (Piece.pack base.boundaries base.source).object.graph ≃g
          ctx.G.object.graph)

/-- A connected support with its literal proper/whole classification. -/
structure Interface where
  toBase : InterfaceBase input ctx Coordinate
  scope : Scope input ctx Coordinate toBase

namespace Interface

variable {input ctx Coordinate}

abbrev Boundary (support : Interface input ctx Coordinate) :=
  support.toBase.Boundary

abbrev boundaries (support : Interface input ctx Coordinate) :=
  support.toBase.boundaries

abbrev source (support : Interface input ctx Coordinate) :=
  support.toBase.source

abbrev coordinatePiece (support : Interface input ctx Coordinate) :=
  support.toBase.coordinatePiece

abbrev vertices (support : Interface input ctx Coordinate) :=
  support.toBase.vertices

/-- The original-support predicate: the original interface must be a proper
atom, while the final carrier may be proper or whole. -/
def OriginalEligible (support : Interface input ctx Coordinate) : Prop :=
  ∃ (boundaryNonempty : Nonempty support.Boundary)
    (rank_lt : (Piece.pack support.boundaries support.source).lexRank <
      ctx.G.lexRank),
    support.scope = .proper boundaryNonempty rank_lt

/-- Whole-support evidence, retaining the exact closed reconstruction. -/
def IsWhole (support : Interface input ctx Coordinate) : Prop :=
  ∃ closedReconstruct,
    support.scope = .whole closedReconstruct

theorem scope_exhaustive (support : Interface input ctx Coordinate) :
    support.OriginalEligible ∨ support.IsWhole := by
  rcases support with ⟨base, scope⟩
  cases scope with
  | proper boundaryNonempty rank_lt =>
      exact Or.inl ⟨boundaryNonempty, rank_lt, rfl⟩
  | whole closedReconstruct =>
      exact Or.inr ⟨closedReconstruct, rfl⟩

/-- The proper/whole tag stored by the graph interface is an executable
decision without inspecting any graph, context, or support universe. -/
def originalEligibleDecidable (support : Interface input ctx Coordinate) :
    Decidable support.OriginalEligible := by
  cases scopeEq : support.scope with
  | proper boundaryNonempty rank_lt =>
      exact isTrue ⟨boundaryNonempty, rank_lt, scopeEq⟩
  | whole closedReconstruct =>
      apply isFalse
      rintro ⟨boundaryNonempty, rank_lt, properEq⟩
      rw [scopeEq] at properEq
      cases properEq

/-- The negative constructor of the proper-support decision is exactly the
stored whole-support constructor.  Applications need not reopen `Scope` or
reimplement the complement proof at each diagram diamond. -/
theorem whole_of_not_originalEligible
    (support : Interface input ctx Coordinate)
    (absent : ¬ support.OriginalEligible) : support.IsWhole := by
  cases scopeEq : support.scope with
  | proper boundaryNonempty rank_lt =>
      exact (absent ⟨boundaryNonempty, rank_lt, scopeEq⟩).elim
  | whole closedReconstruct =>
      exact ⟨closedReconstruct, scopeEq⟩

end Interface

/-- A common code for support-specific boundary profiles.  Equality never
identifies the boundary types silently: the type itself is part of the sigma
value. -/
structure BoundaryProfile where
  Boundary : Type u
  degree : Boundary → Nat

/-- The representative clause indexed by the final carrier.  Proper carriers
store the literal CT3 compression; whole carriers store the certified closed
reduction used by minimality. -/
inductive Representative (support : Interface input ctx Coordinate) where
  | proper
      (boundaryNonempty : Nonempty support.Boundary)
      (rank_lt : (Piece.pack support.boundaries support.source).lexRank <
        ctx.G.lexRank)
      (scope_eq : support.scope = .proper boundaryNonempty rank_lt)
      (compression :
        @MinimumDegreeCycleReplacement.Compression _ support.Boundary
          support.boundaries ctx
          (InterfaceBase.properAtom input ctx Coordinate support.toBase
            boundaryNonempty rank_lt))
  | whole
      (closedReconstruct :
        (Piece.pack support.boundaries support.source).object.graph ≃g
          ctx.G.object.graph)
      (scope_eq : support.scope = .whole closedReconstruct)
      (reduction : Core.CertifiedReduction ctx)

/-- Exact target response of a declared coordinate at one support interface. -/
noncomputable def response
    (support : Interface input ctx Coordinate) (coordinate : Coordinate)
    (outside : Context support.Boundary) : Bool :=
  @decide
    (input.Target
      (glue support.boundaries (support.coordinatePiece coordinate) outside))
    (Classical.propDecidable _)

@[simp] theorem response_true_iff
    (support : Interface input ctx Coordinate) (coordinate : Coordinate)
    (outside : Context support.Boundary) :
    response input ctx Coordinate support coordinate outside = true ↔
      input.Target
        (glue support.boundaries (support.coordinatePiece coordinate) outside) := by
  simp [response]

/-- Reusable graph specialization of the Core support-stratified profile. -/
noncomputable def profile
    (coordinateSupport : Coordinate → Finset ctx.G.Vertex) :
    Core.SupportStratifiedDetermination.Profile where
  Coordinate := Coordinate
  Support := Interface input ctx Coordinate
  Context := fun support => Context support.Boundary
  BoundaryProfile := BoundaryProfile.{u}
  Representative := Representative input ctx Coordinate
  supportLe := fun left right => left.vertices ⊆ right.vertices
  originalEligible := Interface.OriginalEligible
  connected := fun support => support.source.graph.Connected
  carries := fun support coordinate =>
    coordinateSupport coordinate ⊆ support.vertices
  determines := fun support basisCoordinate determined =>
    ∀ outside,
      response input ctx Coordinate support basisCoordinate outside =
        response input ctx Coordinate support determined outside
  boundaryProfile := fun support =>
    ⟨support.Boundary,
      support.source.boundaryDegree support.boundaries⟩
  response := response input ctx Coordinate

namespace Representative

variable {input ctx Coordinate}

/-- A representative on an eligible proper interface executes the framework
CT3 compression and contradicts minimality. -/
theorem impossible_of_originalEligible
    {support : Interface input ctx Coordinate}
    (eligible : support.OriginalEligible)
    (representative : Representative input ctx Coordinate support) : False := by
  rcases eligible with ⟨eligibleNonempty, eligibleRank, eligibleScope⟩
  cases representative with
  | proper boundaryNonempty rank_lt scope_eq compression =>
      exact compression.impossible
  | whole closedReconstruct scope_eq reduction =>
      rw [eligibleScope] at scope_eq
      cases scope_eq

/-- A representative on the whole interface is a genuine certified smaller
counterexample and is therefore impossible. -/
theorem impossible_of_whole
    {support : Interface input ctx Coordinate}
    (whole : support.IsWhole)
    (representative : Representative input ctx Coordinate support) : False := by
  rcases whole with ⟨wholeReconstruct, wholeScope⟩
  cases representative with
  | proper boundaryNonempty rank_lt scope_eq compression =>
      rw [wholeScope] at scope_eq
      cases scope_eq
  | whole closedReconstruct scope_eq reduction =>
      exact reduction.impossible

end Representative

namespace Candidate

variable {input ctx Coordinate}
variable (coordinateSupport : Coordinate → Finset ctx.G.Vertex)

noncomputable def SupportProfile :=
  profile input ctx Coordinate coordinateSupport

abbrev RankCandidate :=
  CT15.SupportStratifiedRank.Candidate
    (SupportProfile coordinateSupport)

/-- If one proof-carrying quotient candidate lives on the whole interface,
its code is injective on every declared coordinate.  The proof requests only
the collision certificate selected by a hypothetical equality and then uses
its retained closed reduction; it scans no quotient or context universe. -/
theorem code_injective_of_carrier_whole
    (candidate : RankCandidate coordinateSupport)
    (whole : candidate.carrier.IsWhole) :
    Function.Injective candidate.quotientCode := by
  intro left right identified
  by_contra distinct
  let certificate := candidate.certify left right distinct identified
  have carrierEq : certificate.carrier = candidate.carrier :=
    candidate.certify_carrier left right distinct identified
  have certificateWhole : certificate.carrier.IsWhole := by
    simpa [carrierEq] using whole
  exact Representative.impossible_of_whole certificateWhole
    certificate.representative

/-- Equality transport from any retained collision certificate to the fixed
carrier owned by its candidate.  Applications commonly retain the selected
certificate rather than the candidate carrier itself; they should not
reimplement this dependent transport at every diagram node. -/
theorem code_injective_of_equal_carrier_whole
    (candidate : RankCandidate coordinateSupport)
    {carrier : Interface input ctx Coordinate}
    (carrierExact : carrier = candidate.carrier)
    (whole : carrier.IsWhole) :
    Function.Injective candidate.quotientCode := by
  apply code_injective_of_carrier_whole coordinateSupport candidate
  exact carrierExact ▸ whole

end Candidate

/-- The complete graph-owned support-stratified rank profile. -/
noncomputable def rankProfile
    (coordinateSupport : Coordinate → Finset ctx.G.Vertex)
    (coordinates : FinEnum Coordinate) :=
  CT15.SupportStratifiedRank.profile
    (profile input ctx Coordinate coordinateSupport) coordinates

end StructuralExhaustion.Graph.SupportStratifiedDetermination
