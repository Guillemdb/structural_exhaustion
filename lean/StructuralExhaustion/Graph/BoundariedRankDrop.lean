import StructuralExhaustion.Graph.PackedBoundariedGluing

namespace StructuralExhaustion.Graph.PackedBoundariedGluing

open StructuralExhaustion

universe u v

/-!
# Certificate-local routing for a boundaried rank drop

The incoming determination certificate has already selected a quotient
realization and an inclusion-minimal connected support.  This layer audits a
concrete context witness or universal response, inspects the certificate's
support-location tag, and executes the existing literal CT3 compression when
the support is the original atom.  No contexts, supports, pieces, or graphs are
enumerated.
-/

namespace MinimumDegreeCycleReplacement.RankDropRouting

abbrev Atom (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    (ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target)
    [Nonempty T] :=
  MinimumDegreeCycleReplacement.ProperAtom input boundaries ctx

/-- Location of the inclusion-minimal connected determination support. -/
inductive SupportLocation
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] (atom : Atom input boundaries ctx)
    (Enlarged : Type v) (realization : Piece T) where
  | atAtom
      (internalTargetFree : ¬ input.Target (Piece.pack boundaries realization))
      (internalBaseline : realization.InternalBaseline boundaries input.minimumDegree)
      (locallySmaller : Piece.LexSmaller realization atom.source)
  | enlarged (residual : Enlarged)

/-- Exact rank-drop input arriving at node `[36]`. -/
structure Certificate
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] (atom : Atom input boundaries ctx) (Enlarged : Type v) where
  realization : Piece T
  boundaryDegree_eq :
    MinimumDegreeCycleReplacement.BoundaryDegreeProfile boundaries realization =
      MinimumDegreeCycleReplacement.BoundaryDegreeProfile boundaries atom.source
  location : SupportLocation input boundaries atom Enlarged realization

namespace Certificate

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {T : Type u} {boundaries : FinEnum T} [Nonempty T]
variable {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
variable {atom : Atom input boundaries ctx} {Enlarged : Type v}

/-- Nodes `[36]`--`[37]`: either a concrete outside context distinguishes the
proposal, or it is target-complete against all compatible contexts. -/
theorem contextAudit (certificate : Certificate input boundaries atom Enlarged) :
    MinimumDegreeCycleReplacement.TargetDefective input boundaries
        certificate.realization atom.source ∨
      MinimumDegreeCycleReplacement.TargetComplete input boundaries
        certificate.realization atom.source := by
  by_cases universal :
      MinimumDegreeCycleReplacement.ContextEquivalent input boundaries
        certificate.realization atom.source
  · exact Or.inr ⟨certificate.boundaryDegree_eq, universal⟩
  · exact Or.inl
      (MinimumDegreeCycleReplacement.targetDefective_of_not_contextEquivalent
        input boundaries universal)

end Certificate

namespace AtAtom

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {T : Type u} {boundaries : FinEnum T} [Nonempty T]
variable {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
variable {atom : Atom input boundaries ctx}

noncomputable def compression (realization : Piece T)
    (internalTargetFree : ¬ input.Target (Piece.pack boundaries realization))
    (internalBaseline : realization.InternalBaseline boundaries input.minimumDegree)
    (locallySmaller : Piece.LexSmaller realization atom.source)
    (universal : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      realization atom.source) :
    MinimumDegreeCycleReplacement.Compression input boundaries atom :=
  MinimumDegreeCycleReplacement.Compression.ofTargetComplete input boundaries
    realization universal internalTargetFree internalBaseline locallySmaller

theorem impossible (realization : Piece T)
    (internalTargetFree : ¬ input.Target (Piece.pack boundaries realization))
    (internalBaseline : realization.InternalBaseline boundaries input.minimumDegree)
    (locallySmaller : Piece.LexSmaller realization atom.source)
    (universal : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      realization atom.source) : False :=
  (compression realization internalTargetFree internalBaseline locallySmaller
    universal).impossible

theorem terminal (realization : Piece T)
    (internalTargetFree : ¬ input.Target (Piece.pack boundaries realization))
    (internalBaseline : realization.InternalBaseline boundaries input.minimumDegree)
    (locallySmaller : Piece.LexSmaller realization atom.source)
    (universal : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      realization atom.source) :
    (MinimumDegreeCycleReplacement.Compression.run
      (compression realization internalTargetFree internalBaseline locallySmaller
        universal)).terminal = .compression := rfl

theorem trace (realization : Piece T)
    (internalTargetFree : ¬ input.Target (Piece.pack boundaries realization))
    (internalBaseline : realization.InternalBaseline boundaries input.minimumDegree)
    (locallySmaller : Piece.LexSmaller realization atom.source)
    (universal : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      realization atom.source) :
    (MinimumDegreeCycleReplacement.Compression.run
      (compression realization internalTargetFree internalBaseline locallySmaller
        universal)).trace = [.entry, .vectorComputation, .compressionSearch,
          .compressionTerminal] := rfl

theorem checks (realization : Piece T)
    (internalTargetFree : ¬ input.Target (Piece.pack boundaries realization))
    (internalBaseline : realization.InternalBaseline boundaries input.minimumDegree)
    (locallySmaller : Piece.LexSmaller realization atom.source)
    (universal : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      realization atom.source) :
    (MinimumDegreeCycleReplacement.Compression.run
      (compression realization internalTargetFree internalBaseline locallySmaller
        universal)).checks = 1 := rfl

theorem polynomial (realization : Piece T)
    (internalTargetFree : ¬ input.Target (Piece.pack boundaries realization))
    (internalBaseline : realization.InternalBaseline boundaries input.minimumDegree)
    (locallySmaller : Piece.LexSmaller realization atom.source)
    (universal : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      realization atom.source) :
    let compression := compression realization internalTargetFree
      internalBaseline locallySmaller universal
    (MinimumDegreeCycleReplacement.Compression.run compression).checks ≤
      (CT3.certifiedCompressionBudget ctx).coefficient *
        ((CT3.certifiedCompressionBudget ctx).size
            compression.certifiedInput + 1) ^
          (CT3.certifiedCompressionBudget ctx).degree :=
  (compression realization internalTargetFree internalBaseline locallySmaller
    universal).run_polynomial

theorem total (realization : Piece T)
    (internalTargetFree : ¬ input.Target (Piece.pack boundaries realization))
    (internalBaseline : realization.InternalBaseline boundaries input.minimumDegree)
    (locallySmaller : Piece.LexSmaller realization atom.source)
    (universal : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      realization atom.source) :
    let compression := compression realization internalTargetFree
      internalBaseline locallySmaller universal
    ∃ result : CT3.CertifiedCompressionRun ctx compression.certifiedInput,
      result.terminal = .compression ∧
        result.trace = [.entry, .vectorComputation, .compressionSearch,
          .compressionTerminal] :=
  (compression realization internalTargetFree internalBaseline locallySmaller
    universal).run_total

end AtAtom

/-- Surviving proposition after nodes `[36]`--`[39]`; the at-atom branch is
closed by its literal CT3 run. -/
def Routed
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] (atom : Atom input boundaries ctx) (Enlarged : Type v) : Prop :=
  (∃ realization : Piece T,
    MinimumDegreeCycleReplacement.TargetDefective input boundaries
      realization atom.source) ∨ Nonempty Enlarged

/-- Complete certificate-local routing for nodes `[36]`--`[39]`. -/
theorem route
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] {atom : Atom input boundaries ctx} {Enlarged : Type v}
    (certificate : Certificate input boundaries atom Enlarged) :
    Routed input boundaries atom Enlarged := by
  rcases certificate.contextAudit with defective | universal
  · exact Or.inl ⟨certificate.realization, defective⟩
  · cases certificate.location with
    | atAtom internalTargetFree internalBaseline locallySmaller =>
        exact (AtAtom.impossible certificate.realization internalTargetFree
          internalBaseline locallySmaller universal).elim
    | enlarged residual => exact Or.inr ⟨residual⟩

/-- Reusable proof that the route is total on every supplied local
determination certificate. -/
theorem route_total
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] {atom : Atom input boundaries ctx} {Enlarged : Type v}
    (certificate : Certificate input boundaries atom Enlarged) :
    Routed input boundaries atom Enlarged :=
  route input boundaries certificate

/-- Complete reusable audit surface for the four-node rank-drop block. -/
structure VerifiedStage
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] (atom : Atom input boundaries ctx) (Enlarged : Type v) : Prop where
  contextAudit : ∀ certificate : Certificate input boundaries atom Enlarged,
    MinimumDegreeCycleReplacement.TargetDefective input boundaries
        certificate.realization atom.source ∨
      MinimumDegreeCycleReplacement.TargetComplete input boundaries
        certificate.realization atom.source
  atAtomImpossible : ∀ (realization : Piece T)
    (_internalTargetFree : ¬ input.Target (Piece.pack boundaries realization))
    (_internalBaseline : realization.InternalBaseline boundaries input.minimumDegree)
    (_locallySmaller : Piece.LexSmaller realization atom.source)
    (_universal : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      realization atom.source), False
  atAtomTerminal : ∀ (realization : Piece T)
    (internalTargetFree : ¬ input.Target (Piece.pack boundaries realization))
    (internalBaseline : realization.InternalBaseline boundaries input.minimumDegree)
    (locallySmaller : Piece.LexSmaller realization atom.source)
    (universal : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      realization atom.source),
    (MinimumDegreeCycleReplacement.Compression.run
      (AtAtom.compression realization internalTargetFree internalBaseline
        locallySmaller universal)).terminal = .compression
  atAtomTrace : ∀ (realization : Piece T)
    (internalTargetFree : ¬ input.Target (Piece.pack boundaries realization))
    (internalBaseline : realization.InternalBaseline boundaries input.minimumDegree)
    (locallySmaller : Piece.LexSmaller realization atom.source)
    (universal : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      realization atom.source),
    (MinimumDegreeCycleReplacement.Compression.run
      (AtAtom.compression realization internalTargetFree internalBaseline
        locallySmaller universal)).trace =
      [.entry, .vectorComputation, .compressionSearch, .compressionTerminal]
  atAtomChecks : ∀ (realization : Piece T)
    (internalTargetFree : ¬ input.Target (Piece.pack boundaries realization))
    (internalBaseline : realization.InternalBaseline boundaries input.minimumDegree)
    (locallySmaller : Piece.LexSmaller realization atom.source)
    (universal : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      realization atom.source),
    (MinimumDegreeCycleReplacement.Compression.run
      (AtAtom.compression realization internalTargetFree internalBaseline
        locallySmaller universal)).checks = 1
  atAtomPolynomial : ∀ (realization : Piece T)
    (internalTargetFree : ¬ input.Target (Piece.pack boundaries realization))
    (internalBaseline : realization.InternalBaseline boundaries input.minimumDegree)
    (locallySmaller : Piece.LexSmaller realization atom.source)
    (universal : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      realization atom.source),
    let compression := AtAtom.compression realization internalTargetFree
      internalBaseline locallySmaller universal
    (MinimumDegreeCycleReplacement.Compression.run compression).checks ≤
      (CT3.certifiedCompressionBudget ctx).coefficient *
        ((CT3.certifiedCompressionBudget ctx).size
            compression.certifiedInput + 1) ^
          (CT3.certifiedCompressionBudget ctx).degree
  atAtomTotal : ∀ (realization : Piece T)
    (internalTargetFree : ¬ input.Target (Piece.pack boundaries realization))
    (internalBaseline : realization.InternalBaseline boundaries input.minimumDegree)
    (locallySmaller : Piece.LexSmaller realization atom.source)
    (universal : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      realization atom.source),
    let compression := AtAtom.compression realization internalTargetFree
      internalBaseline locallySmaller universal
    ∃ result : CT3.CertifiedCompressionRun ctx compression.certifiedInput,
      result.terminal = .compression ∧
        result.trace = [.entry, .vectorComputation, .compressionSearch,
          .compressionTerminal]
  routed : ∀ _certificate : Certificate input boundaries atom Enlarged,
    Routed input boundaries atom Enlarged

noncomputable def verifiedStage
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] (atom : Atom input boundaries ctx) (Enlarged : Type v) :
    VerifiedStage input boundaries atom Enlarged where
  contextAudit := Certificate.contextAudit
  atAtomImpossible := AtAtom.impossible
  atAtomTerminal := AtAtom.terminal
  atAtomTrace := AtAtom.trace
  atAtomChecks := AtAtom.checks
  atAtomPolynomial := AtAtom.polynomial
  atAtomTotal := AtAtom.total
  routed := route input boundaries

end MinimumDegreeCycleReplacement.RankDropRouting

namespace MinimumDegreeCycleReplacement.ProperDelocalization

/-!
## Enlarged-support route

The preceding rank-drop route returns an enlarged connected support without
classifying whether that support is still proper in the selected graph.  This
profile performs exactly that next local split.  A proper extension is itself
a literal `ProperAtom`; its proposed determining realization is audited by the
same exact context semantics and CT3 compression kernel.  The whole-graph
constructor is retained unchanged for the later closed-profile route.
-/

abbrev Atom (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    (ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target)
    [Nonempty T] :=
  MinimumDegreeCycleReplacement.ProperAtom input boundaries ctx

/-- Exact node-`[40]` data when the enlarged determination support is still
proper.  The embedding and strict rank inequality record `C ⊊ Z`; the
remaining fields are precisely the local quotient realization on `Z`. -/
structure ProperExtension
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] (original : Atom input boundaries ctx) where
  enlarged : Atom input boundaries ctx
  embeds : original.source.graph ↪g enlarged.source.graph
  fixesBoundary : ∀ boundary : T,
    embeds (Sum.inl boundary) = Sum.inl boundary
  strict : (Piece.pack boundaries original.source).lexRank <
    (Piece.pack boundaries enlarged.source).lexRank
  realization : Piece T
  boundaryDegree_eq :
    MinimumDegreeCycleReplacement.BoundaryDegreeProfile boundaries realization =
      MinimumDegreeCycleReplacement.BoundaryDegreeProfile boundaries enlarged.source
  internalTargetFree : ¬ input.Target (Piece.pack boundaries realization)
  internalBaseline : realization.InternalBaseline boundaries input.minimumDegree
  locallySmaller : Piece.LexSmaller realization enlarged.source

namespace ProperExtension

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {T : Type u} {boundaries : FinEnum T} [Nonempty T]
variable {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
variable {original : Atom input boundaries ctx}

/-- Node `[42]`: a proper enlarged support either exposes a distinguishing
outside context or its universal quotient executes CT3 and is impossible.
Therefore the only returned residual is the literal target defect. -/
theorem targetDefective
    (extension : ProperExtension input boundaries original) :
    MinimumDegreeCycleReplacement.TargetDefective input boundaries
      extension.realization extension.enlarged.source := by
  by_cases universal :
      MinimumDegreeCycleReplacement.ContextEquivalent input boundaries
        extension.realization extension.enlarged.source
  · have complete :
        MinimumDegreeCycleReplacement.TargetComplete input boundaries
          extension.realization extension.enlarged.source :=
      ⟨extension.boundaryDegree_eq, universal⟩
    exact False.elim
      (RankDropRouting.AtAtom.impossible extension.realization
        extension.internalTargetFree extension.internalBaseline
        extension.locallySmaller complete)
  · exact MinimumDegreeCycleReplacement.targetDefective_of_not_contextEquivalent
      input boundaries universal

noncomputable def compression
    (extension : ProperExtension input boundaries original)
    (complete : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      extension.realization extension.enlarged.source) :
    MinimumDegreeCycleReplacement.Compression input boundaries
      extension.enlarged :=
  RankDropRouting.AtAtom.compression extension.realization
    extension.internalTargetFree extension.internalBaseline
    extension.locallySmaller complete

theorem compression_terminal
    (extension : ProperExtension input boundaries original)
    (complete : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      extension.realization extension.enlarged.source) :
    (MinimumDegreeCycleReplacement.Compression.run
      (extension.compression complete)).terminal = .compression := rfl

theorem compression_trace
    (extension : ProperExtension input boundaries original)
    (complete : MinimumDegreeCycleReplacement.TargetComplete input boundaries
      extension.realization extension.enlarged.source) :
    (MinimumDegreeCycleReplacement.Compression.run
      (extension.compression complete)).trace =
      [.entry, .vectorComputation, .compressionSearch, .compressionTerminal] := rfl

end ProperExtension

/-- Node `[41]` is a literal tag: the enlarged support is proper, or it is the
whole selected graph and the unchanged payload continues to node `[43]`. -/
inductive Location
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] (original : Atom input boundaries ctx) (Whole : Type v) where
  | proper (extension : ProperExtension input boundaries original)
  | whole (residual : Whole)

inductive Routed
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] (original : Atom input boundaries ctx) (Whole : Type v) where
  | properClosed (extension : ProperExtension input boundaries original)
      (defective : MinimumDegreeCycleReplacement.TargetDefective input boundaries
        extension.realization extension.enlarged.source)
  | whole (residual : Whole)

def route
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] (original : Atom input boundaries ctx) (Whole : Type v)
    (location : Location input boundaries original Whole) :
    Routed input boundaries original Whole := by
  cases location with
  | proper extension =>
      exact .properClosed extension extension.targetDefective
  | whole residual => exact .whole residual

structure VerifiedStage
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] (original : Atom input boundaries ctx) (Whole : Type v) : Prop where
  properAudit : ∀ extension : ProperExtension input boundaries original,
    MinimumDegreeCycleReplacement.TargetDefective input boundaries
      extension.realization extension.enlarged.source
  total : ∀ _location : Location input boundaries original Whole,
    Nonempty (Routed input boundaries original Whole)

def verifiedStage
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] (original : Atom input boundaries ctx) (Whole : Type v) :
    VerifiedStage input boundaries original Whole where
  properAudit := ProperExtension.targetDefective
  total := fun location => ⟨route input boundaries original Whole location⟩

/-! ## Typed composition with the preceding rank-drop route -/

/-- Exact output of the combined nodes-`[36]`--`[42]` route.  A context
defect produced before delocalization is retained verbatim.  Otherwise the
enlarged payload has the precise `Location` type consumed by `route`, so no
untyped or proof-specific handoff occurs between the two stages. -/
def CombinedRouted
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] (original : Atom input boundaries ctx) (Whole : Type v) : Prop :=
  (∃ realization : Piece T,
    MinimumDegreeCycleReplacement.TargetDefective input boundaries
      realization original.source) ∨
    Nonempty (Routed input boundaries original Whole)

/-- Execute the rank-drop audit and immediately feed its enlarged-support
payload to the proper/whole delocalization route. -/
def routeAfterRankDrop
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] (original : Atom input boundaries ctx) (Whole : Type v)
    (certificate : RankDropRouting.Certificate input boundaries original
      (Location input boundaries original Whole)) :
    CombinedRouted input boundaries original Whole := by
  cases RankDropRouting.route input boundaries certificate with
  | inl defective => exact Or.inl defective
  | inr locationExists =>
      cases locationExists with
      | intro location =>
          exact Or.inr ⟨route input boundaries original Whole location⟩

theorem routeAfterRankDrop_total
    (input : PackedMinimumDegreeCycle.StaticInput)
    {T : Type u} (boundaries : FinEnum T)
    {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
    [Nonempty T] (original : Atom input boundaries ctx) (Whole : Type v)
    (certificate : RankDropRouting.Certificate input boundaries original
      (Location input boundaries original Whole)) :
    CombinedRouted input boundaries original Whole :=
  routeAfterRankDrop input boundaries original Whole certificate

end MinimumDegreeCycleReplacement.ProperDelocalization

end StructuralExhaustion.Graph.PackedBoundariedGluing
