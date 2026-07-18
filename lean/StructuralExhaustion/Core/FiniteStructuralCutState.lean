import StructuralExhaustion.Core.FixedTwoBoundaryCutState
import StructuralExhaustion.Core.BoundedListCode
import StructuralExhaustion.Core.FiniteObservedColumn
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace StructuralExhaustion.Core.FiniteStructuralCutState

universe uHalfEdge uOffset uD4 uD5 uD6 uD7

/-!
# Finite two-boundary structural cut states

This is the graph-independent product used by bounded-corridor arguments when
the state records two capped boundary degrees, two normalized half-edge roles,
two interface offsets, and four already-normalized finite coordinate blocks.
It stores no ambient vertex, graph, prefix, or outside context.

The graph application remains responsible for proving that its four blocks
contain every coordinate declared by the manuscript.  Finiteness of the
product never supplies that semantic completeness claim.
-/

abbrev BoundaryRole := FixedTwoBoundaryCutState.BoundaryRole
abbrev CappedDegree := FixedTwoBoundaryCutState.CappedDegree

noncomputable def product2EquivFin
    {α : Type uHalfEdge} {β : Type uOffset} {a b : Nat}
    (left : α ≃ Fin a) (right : β ≃ Fin b) :
    α × β ≃ Fin (a * b) :=
  (left.prodCongr right).trans finProdFinEquiv

noncomputable def product3EquivFin
    {α : Type uHalfEdge} {β : Type uOffset} {γ : Type uD4}
    {a b c : Nat}
    (first : α ≃ Fin a) (second : β ≃ Fin b)
    (third : γ ≃ Fin c) :
    α × β × γ ≃ Fin (a * b * c) :=
  (first.prodCongr (product2EquivFin second third)).trans <|
    finProdFinEquiv.trans <| finCongr (by ring)

noncomputable def product4EquivFin
    {α : Type uHalfEdge} {β : Type uOffset} {γ : Type uD4}
    {δ : Type uD5} {a b c d : Nat}
    (first : α ≃ Fin a) (second : β ≃ Fin b)
    (third : γ ≃ Fin c) (fourth : δ ≃ Fin d) :
    α × β × γ × δ ≃ Fin (a * b * c * d) :=
  (first.prodCongr (product3EquivFin second third fourth)).trans <|
    finProdFinEquiv.trans <| finCongr (by ring)

noncomputable def product5EquivFin
    {α : Type uHalfEdge} {β : Type uOffset} {γ : Type uD4}
    {δ : Type uD5} {ε : Type uD6} {a b c d e : Nat}
    (first : α ≃ Fin a) (second : β ≃ Fin b)
    (third : γ ≃ Fin c) (fourth : δ ≃ Fin d)
    (fifth : ε ≃ Fin e) :
    α × β × γ × δ × ε ≃ Fin (a * b * c * d * e) :=
  (first.prodCongr (product4EquivFin second third fourth fifth)).trans <|
    finProdFinEquiv.trans <| finCongr (by ring)

noncomputable def product6EquivFin
    {α : Type uHalfEdge} {β : Type uOffset} {γ : Type uD4}
    {δ : Type uD5} {ε : Type uD6} {ζ : Type uD7}
    {a b c d e f : Nat}
    (first : α ≃ Fin a) (second : β ≃ Fin b)
    (third : γ ≃ Fin c) (fourth : δ ≃ Fin d)
    (fifth : ε ≃ Fin e) (sixth : ζ ≃ Fin f) :
    α × β × γ × δ × ε × ζ ≃ Fin (a * b * c * d * e * f) :=
  (first.prodCongr (product5EquivFin second third fourth fifth sixth)).trans <|
    finProdFinEquiv.trans <| finCongr (by ring)

noncomputable def product7EquivFin
    {α : Type uHalfEdge} {β : Type uOffset} {γ : Type uD4}
    {δ : Type uD5} {ε : Type uD6} {ζ : Type uD7} {η : Type*}
    {a b c d e f g : Nat}
    (first : α ≃ Fin a) (second : β ≃ Fin b)
    (third : γ ≃ Fin c) (fourth : δ ≃ Fin d)
    (fifth : ε ≃ Fin e) (sixth : ζ ≃ Fin f)
    (seventh : η ≃ Fin g) :
    α × β × γ × δ × ε × ζ × η ≃
      Fin (a * b * c * d * e * f * g) :=
  (first.prodCongr
      (product6EquivFin second third fourth fifth sixth seventh)).trans <|
    finProdFinEquiv.trans <| finCongr (by ring)

/-- A reusable finite structural state with four clause-labelled coordinate
blocks.  The alphabets are parameters so applications can normalize observed
local lists without enumerating the state space. -/
structure State
    (HalfEdgeRole : Type uHalfEdge) (InterfaceOffset : Type uOffset)
    (D4Code : Type uD4) (D5Code : Type uD5)
    (D6Code : Type uD6) (D7Code : Type uD7) where
  boundaryDegree : BoundaryRole → CappedDegree
  activeHalfEdge : BoundaryRole → HalfEdgeRole
  windowOffset : BoundaryRole → InterfaceOffset
  d4 : D4Code
  d5 : D5Code
  d6 : D6Code
  d7 : D7Code

def stateEquiv
    (HalfEdgeRole : Type uHalfEdge) (InterfaceOffset : Type uOffset)
    (D4Code : Type uD4) (D5Code : Type uD5)
    (D6Code : Type uD6) (D7Code : Type uD7) :
    State HalfEdgeRole InterfaceOffset D4Code D5Code D6Code D7Code ≃
      ((BoundaryRole → CappedDegree) ×
        (BoundaryRole → HalfEdgeRole) ×
        (BoundaryRole → InterfaceOffset) ×
        D4Code × D5Code × D6Code × D7Code) where
  toFun state := (state.boundaryDegree, state.activeHalfEdge,
    state.windowOffset, state.d4, state.d5, state.d6, state.d7)
  invFun data := ⟨data.1, data.2.1, data.2.2.1,
    data.2.2.2.1, data.2.2.2.2.1, data.2.2.2.2.2.1,
    data.2.2.2.2.2.2⟩
  left_inv := by intro state; cases state; rfl
  right_inv := by intro data; rcases data with ⟨a, b, c, d, e, f, g⟩; rfl

noncomputable instance
    (HalfEdgeRole : Type uHalfEdge) (InterfaceOffset : Type uOffset)
    (D4Code : Type uD4) (D5Code : Type uD5)
    (D6Code : Type uD6) (D7Code : Type uD7)
    [Fintype HalfEdgeRole] [Fintype InterfaceOffset]
    [Fintype D4Code] [Fintype D5Code] [Fintype D6Code] [Fintype D7Code] :
    Fintype (State HalfEdgeRole InterfaceOffset D4Code D5Code D6Code D7Code) := by
  classical
  exact Fintype.ofEquiv _
    (stateEquiv HalfEdgeRole InterfaceOffset D4Code D5Code D6Code D7Code).symm

noncomputable instance
    (HalfEdgeRole : Type uHalfEdge) (InterfaceOffset : Type uOffset)
    (D4Code : Type uD4) (D5Code : Type uD5)
    (D6Code : Type uD6) (D7Code : Type uD7)
    : DecidableEq
      (State HalfEdgeRole InterfaceOffset D4Code D5Code D6Code D7Code) :=
  Classical.decEq _

/-- Exact cardinality of the symbolic product.  In particular the bound is
independent of the ambient graph order and of the number of corridor stages. -/
theorem state_card
    (HalfEdgeRole : Type uHalfEdge) (InterfaceOffset : Type uOffset)
    (D4Code : Type uD4) (D5Code : Type uD5)
    (D6Code : Type uD6) (D7Code : Type uD7)
    [Fintype HalfEdgeRole] [Fintype InterfaceOffset]
    [Fintype D4Code] [Fintype D5Code] [Fintype D6Code] [Fintype D7Code] :
    Fintype.card
        (State HalfEdgeRole InterfaceOffset D4Code D5Code D6Code D7Code) =
      4 ^ 2 * Fintype.card HalfEdgeRole ^ 2 *
        Fintype.card InterfaceOffset ^ 2 *
        Fintype.card D4Code * Fintype.card D5Code *
        Fintype.card D6Code * Fintype.card D7Code := by
  classical
  rw [Fintype.card_congr
    (stateEquiv HalfEdgeRole InterfaceOffset D4Code D5Code D6Code D7Code)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  ring

noncomputable def stateEquivFinOfEquiv
    {HalfEdgeRole : Type uHalfEdge} {InterfaceOffset : Type uOffset}
    {D4Code : Type uD4} {D5Code : Type uD5}
    {D6Code : Type uD6} {D7Code : Type uD7}
    {halfEdgeCard offsetCard d4Card d5Card d6Card d7Card : Nat}
    (halfEdgeEquiv : HalfEdgeRole ≃ Fin halfEdgeCard)
    (offsetEquiv : InterfaceOffset ≃ Fin offsetCard)
    (d4Equiv : D4Code ≃ Fin d4Card)
    (d5Equiv : D5Code ≃ Fin d5Card)
    (d6Equiv : D6Code ≃ Fin d6Card)
    (d7Equiv : D7Code ≃ Fin d7Card) :
    State HalfEdgeRole InterfaceOffset D4Code D5Code D6Code D7Code ≃
      Fin (4 ^ 2 * halfEdgeCard ^ 2 * offsetCard ^ 2 *
        d4Card * d5Card * d6Card * d7Card) :=
  (stateEquiv HalfEdgeRole InterfaceOffset D4Code D5Code D6Code D7Code).trans <|
    product7EquivFin
      (BoundedListCode.functionEquivFinOfEquiv (Equiv.refl CappedDegree) 2)
      (BoundedListCode.functionEquivFinOfEquiv halfEdgeEquiv 2)
      (BoundedListCode.functionEquivFinOfEquiv offsetEquiv 2)
      d4Equiv d5Equiv d6Equiv d7Equiv

theorem stateEquivFinOfEquiv_injective
    {HalfEdgeRole : Type uHalfEdge} {InterfaceOffset : Type uOffset}
    {D4Code : Type uD4} {D5Code : Type uD5}
    {D6Code : Type uD6} {D7Code : Type uD7}
    {halfEdgeCard offsetCard d4Card d5Card d6Card d7Card : Nat}
    (halfEdgeEquiv : HalfEdgeRole ≃ Fin halfEdgeCard)
    (offsetEquiv : InterfaceOffset ≃ Fin offsetCard)
    (d4Equiv : D4Code ≃ Fin d4Card)
    (d5Equiv : D5Code ≃ Fin d5Card)
    (d6Equiv : D6Code ≃ Fin d6Card)
    (d7Equiv : D7Code ≃ Fin d7Card) :
    Function.Injective
      (stateEquivFinOfEquiv halfEdgeEquiv offsetEquiv
        d4Equiv d5Equiv d6Equiv d7Equiv) :=
  (stateEquivFinOfEquiv halfEdgeEquiv offsetEquiv
    d4Equiv d5Equiv d6Equiv d7Equiv).injective

/-- A finite symbolic encoding carries its bound, encoder, and injectivity
certificate together.  Clients can consume the bound without asking Lean to
normalize the expression from which it was assembled. -/
structure FiniteEncoding (α : Type u) where
  bound : Nat
  encode : α → Fin bound
  encode_injective : Function.Injective encode

/-- A structural-state encoding additionally retains the exact symbolic
product cardinal supplied by its component alphabets. -/
structure StateFiniteEncoding (α : Type u) where
  productCard : Nat
  finite : FiniteEncoding α
  bound_eq_productCard : finite.bound = productCard

/-- A structural-state encoding assembled from observed columns.  Besides the
complete state encoding, it retains the framework-computed product of the
column-code cardinalities.  Applications therefore project `qCols` from the
same bundle that supplies the state bound and encoder; they never define or
transport a separate column factor. -/
structure ColumnStateFiniteEncoding (α : Type u) (expectedQCols : Nat)
    extends StateFiniteEncoding α where
  qCols : Nat
  qCols_eq_expected : qCols = expectedQCols

namespace StateFiniteEncoding

/-- View the bundled encoder directly in the recorded symbolic product
cardinality.  The cast uses the stored certificate and performs no arithmetic
normalization. -/
def encodeToProduct {α : Type u} (encoding : StateFiniteEncoding α) :
    α → Fin encoding.productCard :=
  fun value => Fin.cast encoding.bound_eq_productCard (encoding.finite.encode value)

theorem encodeToProduct_injective {α : Type u}
    (encoding : StateFiniteEncoding α) :
    Function.Injective encoding.encodeToProduct := by
  intro left right equal
  apply encoding.finite.encode_injective
  exact (Fin.cast_injective encoding.bound_eq_productCard) equal

end StateFiniteEncoding

/-- Bundle the explicit seven-field structural-state encoding.  The product
cardinality remains symbolic; constructing this value does not enumerate its
inhabitants. -/
noncomputable def stateEncodingOfEquiv
    {HalfEdgeRole : Type uHalfEdge} {InterfaceOffset : Type uOffset}
    {D4Code : Type uD4} {D5Code : Type uD5}
    {D6Code : Type uD6} {D7Code : Type uD7}
    {halfEdgeCard offsetCard d4Card d5Card d6Card d7Card : Nat}
    (halfEdgeEquiv : HalfEdgeRole ≃ Fin halfEdgeCard)
    (offsetEquiv : InterfaceOffset ≃ Fin offsetCard)
    (d4Equiv : D4Code ≃ Fin d4Card)
    (d5Equiv : D5Code ≃ Fin d5Card)
    (d6Equiv : D6Code ≃ Fin d6Card)
    (d7Equiv : D7Code ≃ Fin d7Card) :
    StateFiniteEncoding
      (State HalfEdgeRole InterfaceOffset D4Code D5Code D6Code D7Code) :=
  let equivalence := stateEquivFinOfEquiv halfEdgeEquiv offsetEquiv
    d4Equiv d5Equiv d6Equiv d7Equiv
  { productCard := 4 ^ 2 * halfEdgeCard ^ 2 * offsetCard ^ 2 *
      d4Card * d5Card * d6Card * d7Card
    finite :=
      { bound := 4 ^ 2 * halfEdgeCard ^ 2 * offsetCard ^ 2 *
          d4Card * d5Card * d6Card * d7Card
        encode := equivalence
        encode_injective := equivalence.injective }
    bound_eq_productCard := rfl }

/-- Build a structural-state encoding directly from four framework-owned
observed-column packages.  This is the canonical propagation path: clients
name their alphabets once and never restate column bounds, code cardinalities,
or `Fin` equivalences. -/
noncomputable def stateEncodingOfColumns
    {HalfEdgeRole : Type uHalfEdge} {InterfaceOffset : Type uOffset}
    {D4 : Type uD4} {D5 : Type uD5} {D6 : Type uD6} {D7 : Type uD7}
    {halfEdgeCard offsetCard : Nat}
    (halfEdgeEquiv : HalfEdgeRole ≃ Fin halfEdgeCard)
    (offsetEquiv : InterfaceOffset ≃ Fin offsetCard)
    (d4 : FiniteObservedColumn.Encoding D4)
    (d5 : FiniteObservedColumn.Encoding D5)
    (d6 : FiniteObservedColumn.Encoding D6)
    (d7 : FiniteObservedColumn.Encoding D7) :
    StateFiniteEncoding
      (State HalfEdgeRole InterfaceOffset
        d4.Code d5.Code d6.Code d7.Code) :=
  stateEncodingOfEquiv halfEdgeEquiv offsetEquiv
    d4.codeEquivFin d5.codeEquivFin d6.codeEquivFin d7.codeEquivFin

/-- Canonical state encoding from one framework-owned four-column bundle. -/
noncomputable def stateEncodingOfColumnBundle
    {HalfEdgeRole : Type uHalfEdge} {InterfaceOffset : Type uOffset}
    {D4 : Type uD4} {D5 : Type uD5} {D6 : Type uD6} {D7 : Type uD7}
    {halfEdgeCard offsetCard : Nat}
    (halfEdgeEquiv : HalfEdgeRole ≃ Fin halfEdgeCard)
    (offsetEquiv : InterfaceOffset ≃ Fin offsetCard)
    (columns : FiniteObservedColumn.FourEncoding D4 D5 D6 D7) :
    ColumnStateFiniteEncoding
      (State HalfEdgeRole InterfaceOffset
        columns.d4.Code columns.d5.Code columns.d6.Code columns.d7.Code)
      columns.qCols :=
  { stateEncodingOfColumns halfEdgeEquiv offsetEquiv
      columns.d4 columns.d5 columns.d6 columns.d7 with
    qCols := columns.qCols
    qCols_eq_expected := rfl }

/-- The column factor retained by the canonical state bundle is definitionally
the sole `FourEncoding.qCols` authority. -/
@[simp] theorem stateEncodingOfColumnBundle_qCols
    {HalfEdgeRole : Type uHalfEdge} {InterfaceOffset : Type uOffset}
    {D4 : Type uD4} {D5 : Type uD5} {D6 : Type uD6} {D7 : Type uD7}
    {halfEdgeCard offsetCard : Nat}
    (halfEdgeEquiv : HalfEdgeRole ≃ Fin halfEdgeCard)
    (offsetEquiv : InterfaceOffset ≃ Fin offsetCard)
    (columns : FiniteObservedColumn.FourEncoding D4 D5 D6 D7) :
    (stateEncodingOfColumnBundle halfEdgeEquiv offsetEquiv columns).qCols =
      columns.qCols :=
  (stateEncodingOfColumnBundle halfEdgeEquiv offsetEquiv columns).qCols_eq_expected

/-- The complete symbolic state cardinality automatically contains the
retained column factor.  This is the generic manuscript-facing product formula
and avoids unfolding the four individual code cardinalities in applications. -/
theorem stateEncodingOfColumnBundle_productCard
    {HalfEdgeRole : Type uHalfEdge} {InterfaceOffset : Type uOffset}
    {D4 : Type uD4} {D5 : Type uD5} {D6 : Type uD6} {D7 : Type uD7}
    {halfEdgeCard offsetCard : Nat}
    (halfEdgeEquiv : HalfEdgeRole ≃ Fin halfEdgeCard)
    (offsetEquiv : InterfaceOffset ≃ Fin offsetCard)
    (columns : FiniteObservedColumn.FourEncoding D4 D5 D6 D7) :
    (stateEncodingOfColumnBundle halfEdgeEquiv offsetEquiv columns).productCard =
      4 ^ 2 * halfEdgeCard ^ 2 * offsetCard ^ 2 *
        (stateEncodingOfColumnBundle halfEdgeEquiv offsetEquiv columns).qCols := by
  change
    4 ^ 2 * halfEdgeCard ^ 2 * offsetCard ^ 2 *
        columns.d4.codeCard * columns.d5.codeCard *
        columns.d6.codeCard * columns.d7.codeCard =
      4 ^ 2 * halfEdgeCard ^ 2 * offsetCard ^ 2 *
        (columns.d4.codeCard * columns.d5.codeCard *
          columns.d6.codeCard * columns.d7.codeCard)
  ring

theorem stateEncodingOfEquiv_bound
    {HalfEdgeRole : Type uHalfEdge} {InterfaceOffset : Type uOffset}
    {D4Code : Type uD4} {D5Code : Type uD5}
    {D6Code : Type uD6} {D7Code : Type uD7}
    {halfEdgeCard offsetCard d4Card d5Card d6Card d7Card : Nat}
    (halfEdgeEquiv : HalfEdgeRole ≃ Fin halfEdgeCard)
    (offsetEquiv : InterfaceOffset ≃ Fin offsetCard)
    (d4Equiv : D4Code ≃ Fin d4Card)
    (d5Equiv : D5Code ≃ Fin d5Card)
    (d6Equiv : D6Code ≃ Fin d6Card)
    (d7Equiv : D7Code ≃ Fin d7Card) :
    (stateEncodingOfEquiv halfEdgeEquiv offsetEquiv
      d4Equiv d5Equiv d6Equiv d7Equiv).finite.bound =
      4 ^ 2 * halfEdgeCard ^ 2 * offsetCard ^ 2 *
        d4Card * d5Card * d6Card * d7Card :=
  (stateEncodingOfEquiv halfEdgeEquiv offsetEquiv
    d4Equiv d5Equiv d6Equiv d7Equiv).bound_eq_productCard

theorem stateEncodingOfEquiv_productCard
    {HalfEdgeRole : Type uHalfEdge} {InterfaceOffset : Type uOffset}
    {D4Code : Type uD4} {D5Code : Type uD5}
    {D6Code : Type uD6} {D7Code : Type uD7}
    {halfEdgeCard offsetCard d4Card d5Card d6Card d7Card : Nat}
    (halfEdgeEquiv : HalfEdgeRole ≃ Fin halfEdgeCard)
    (offsetEquiv : InterfaceOffset ≃ Fin offsetCard)
    (d4Equiv : D4Code ≃ Fin d4Card)
    (d5Equiv : D5Code ≃ Fin d5Card)
    (d6Equiv : D6Code ≃ Fin d6Card)
    (d7Equiv : D7Code ≃ Fin d7Card) :
    (stateEncodingOfEquiv halfEdgeEquiv offsetEquiv
      d4Equiv d5Equiv d6Equiv d7Equiv).productCard =
      4 ^ 2 * halfEdgeCard ^ 2 * offsetCard ^ 2 *
        d4Card * d5Card * d6Card * d7Card := rfl

/-- The standard corridor allowance obtained by adjoining a fixed interface
decoration budget to a finite state bound. -/
def exchangeBound (stateBound interfaceAllowance : Nat) : Nat :=
  stateBound + interfaceAllowance

/-- The denominator produced by a support-size bound and a point-multiplicity
bound in the bounded-overlap conflict graph. -/
def overlapDenominator (supportBound pointMultiplicityBound : Nat) : Nat :=
  supportBound * pointMultiplicityBound + 1

@[simp] theorem exchangeBound_eq (stateBound interfaceAllowance : Nat) :
    exchangeBound stateBound interfaceAllowance =
      stateBound + interfaceAllowance := rfl

@[simp] theorem overlapDenominator_eq
    (supportBound pointMultiplicityBound : Nat) :
    overlapDenominator supportBound pointMultiplicityBound =
      supportBound * pointMultiplicityBound + 1 := rfl

theorem exchangeBound_pos_of_allowance_pos {stateBound interfaceAllowance : Nat}
    (positive : 0 < interfaceAllowance) :
    0 < exchangeBound stateBound interfaceAllowance := by
  simp [exchangeBound]
  omega

/-- A requested support margin fits in an exchange allowance whenever it fits
in the fixed interface budget.  This stays symbolic in `stateBound`, so
clients never need to unfold a concrete finite-state cardinality. -/
theorem add_le_exchangeBound_of_le {stateBound requested interfaceAllowance : Nat}
    (fits : requested ≤ interfaceAllowance) :
    stateBound + requested ≤ exchangeBound stateBound interfaceAllowance := by
  unfold exchangeBound
  exact Nat.add_le_add_left fits stateBound

namespace FiniteEncoding

/-- Extend the exact bound stored in a finite encoding by a fixed interface
allowance. -/
abbrev exchangeWith {α : Type u} (encoding : FiniteEncoding α)
    (interfaceAllowance : Nat) : Nat :=
  exchangeBound encoding.bound interfaceAllowance

theorem add_le_exchangeWith_of_le {α : Type u}
    (encoding : FiniteEncoding α) {requested interfaceAllowance : Nat}
    (fits : requested ≤ interfaceAllowance) :
    encoding.bound + requested ≤ encoding.exchangeWith interfaceAllowance :=
  add_le_exchangeBound_of_le fits

theorem exchangeWith_pos_of_allowance_pos {α : Type u}
    (encoding : FiniteEncoding α) {interfaceAllowance : Nat}
    (positive : 0 < interfaceAllowance) :
    0 < encoding.exchangeWith interfaceAllowance :=
  exchangeBound_pos_of_allowance_pos positive

end FiniteEncoding

/-- Package a symbolic natural-number expression with the positivity of its
successor, without asking a client to normalize that expression. -/
def successorWithPos (value : Nat) : {bound : Nat // 0 < bound} :=
  ⟨Nat.succ value, Nat.succ_pos value⟩

/-- Multiply two already-positive symbolic bounds while retaining their
certificate, again without normalizing either factor. -/
def productWithPos
    (left right : {bound : Nat // 0 < bound}) : {bound : Nat // 0 < bound} :=
  ⟨left.1 * right.1, Nat.mul_pos left.2 right.2⟩

theorem overlapDenominator_pos (supportBound pointMultiplicityBound : Nat) :
    0 < overlapDenominator supportBound pointMultiplicityBound := by
  simp [overlapDenominator]

end StructuralExhaustion.Core.FiniteStructuralCutState
