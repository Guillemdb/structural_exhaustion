import StructuralExhaustion.Graph.InducedPathPacking

namespace StructuralExhaustion.Graph.InducedPathMaximalPacking

open StructuralExhaustion

universe u uAmbient uBranch

variable {V : Type u}

/-!
# Maximal-only induced-path packing view

This module deliberately does not enumerate induced embeddings.  It reuses
the graph layer's existing noncomputable proof-selected packing and exposes
only the inclusion-maximal facts and selected-list CT12 audit.  In
particular, application nodes using this wrapper receive no
maximum-cardinality field.
-/

abbrev Window (object : FiniteObject V) (order : Nat) :=
  InducedPathPacking.Window object order

noncomputable def support (object : FiniteObject V) (order : Nat)
    (window : Window object order) : Finset V :=
  InducedPathPacking.support object order window

private noncomputable def sourceProfile (object : FiniteObject V)
    (order : Nat) (positive : 0 < order) :=
  InducedPathPacking.profile object order positive

/-- The already selected list, viewed only as a maximal packing. -/
noncomputable def windows (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) : List (Window object order) :=
  InducedPathPacking.windows object order positive

noncomputable def packingNumber (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) : Nat :=
  (windows object order positive).length

/-- The selected-list CT12 execution, with the packing producer kept private. -/
noncomputable def run {P : Core.Problem.{uAmbient, uBranch}}
    (object : FiniteObject V) (order : Nat) (positive : 0 < order)
    (context : Core.BranchContext P) :=
  (sourceProfile object order positive).run context

/-- Framework-owned work certificate for auditing only the selected list. -/
noncomputable def workBudget {P : Core.Problem.{uAmbient, uBranch}}
    (object : FiniteObject V) (order : Nat) (positive : 0 < order)
    (context : Core.BranchContext P) : Core.PolynomialCheckBudget Unit :=
  (sourceProfile object order positive).workBudget context

/-- Every induced path meets a selected path. -/
theorem saturated (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) (window : Window object order) :
    ∃ selected ∈ windows object order positive,
      ¬Disjoint
        (support object order window)
        (support object order selected) :=
  InducedPathPacking.saturated object order positive window

theorem windows_nonempty_of_realization (object : FiniteObject V)
    (order : Nat) (positive : 0 < order)
    (realization : HasInducedPath object.graph order) :
    windows object order positive ≠ [] :=
  InducedPathPacking.windows_nonempty_of_realization
    object order positive realization

/-- The selected disjoint supports occupy at most the ambient vertex carrier.
This exposes only a consequence of disjointness and fixed support size; it
does not expose or require a maximum-cardinality claim at the application
interface. -/
theorem packing_vertices_bound (object : FiniteObject V) (order : Nat)
    (positive : 0 < order) :
    order * packingNumber object order positive ≤
      object.input.vertices.card := by
  exact InducedPathPacking.packing_vertices_bound object order positive

/-- Maximal-only graph-level CT12 contract. -/
abbrev VerifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (object : FiniteObject V) (order : Nat) (positive : 0 < order)
    (context : Core.BranchContext P) :=
  (sourceProfile object order positive).MaximalVerifiedStage context

noncomputable def verifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (object : FiniteObject V) (order : Nat) (positive : 0 < order)
    (context : Core.BranchContext P) :
    VerifiedStage object order positive context :=
  (sourceProfile object order positive).maximalVerifiedStage context

end StructuralExhaustion.Graph.InducedPathMaximalPacking
