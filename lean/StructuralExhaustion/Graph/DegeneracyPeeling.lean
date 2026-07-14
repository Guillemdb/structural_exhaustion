import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import StructuralExhaustion.CT12.ListPeeling
import StructuralExhaustion.Graph.EliminationOrder
import StructuralExhaustion.Graph.InducedSubgraph

namespace StructuralExhaustion.Graph.DegeneracyPeeling

open StructuralExhaustion
open EliminationOrder

universe u uAmbient uBranch

/-- A complete, duplicate-free elimination schedule whose later degree is
bounded at every step. -/
structure Certificate {V : Type u} (object : FiniteObject V) (bound : Nat) where
  values : List V
  nodup : values.Nodup
  complete : ∀ vertex, vertex ∈ values
  bounded : BoundedOrder object bound values

private structure PartialCertificate {V : Type u}
    (object : FiniteObject V) (bound : Nat) (support : Finset V) where
  values : List V
  nodup : values.Nodup
  exact : ∀ vertex, vertex ∈ values ↔ vertex ∈ support
  bounded : BoundedOrder object bound values

private theorem laterNeighbors_length_le_inducedDegree
    {V : Type u} (object : FiniteObject V) (support : Finset V)
    (vertex : {value : V // value ∈ support}) (tail : List V)
    (tailNodup : tail.Nodup)
    (tailSubset : ∀ value, value ∈ tail → value ∈ support) :
    (laterNeighbors object vertex.1 tail).length ≤
      (object.induceFinset support).degree vertex := by
  letI : DecidableEq V := object.input.vertices.decEq
  let induced := object.induceFinset support
  letI : FinEnum {value : V // value ∈ support} :=
    induced.input.vertices
  letI : Fintype {value : V // value ∈ support} :=
    @FinEnum.instFintype _ induced.input.vertices
  letI : DecidableRel induced.graph.Adj := induced.input.decideAdj
  let embedding : {value : V // value ∈ support} ↪ V :=
    Function.Embedding.subtype fun value => value ∈ support
  have laterNodup : (laterNeighbors object vertex.1 tail).Nodup :=
    tailNodup.filter _
  have subset :
      (laterNeighbors object vertex.1 tail).toFinset ⊆
        (induced.graph.neighborFinset vertex).map embedding := by
    intro neighbor member
    have memberList : neighbor ∈ laterNeighbors object vertex.1 tail := by
      simpa using member
    have data := (mem_laterNeighbors_iff object vertex.1 neighbor tail).1
      memberList
    let restricted : {value : V // value ∈ support} :=
      ⟨neighbor, tailSubset neighbor data.1⟩
    have adjacent : induced.graph.Adj vertex restricted := by
      simpa [induced, FiniteObject.induceFinset] using data.2
    exact Finset.mem_map.mpr ⟨restricted, (by
      simpa [SimpleGraph.mem_neighborFinset] using adjacent), rfl⟩
  rw [← List.toFinset_card_of_nodup laterNodup]
  calc
    (laterNeighbors object vertex.1 tail).toFinset.card ≤
        ((induced.graph.neighborFinset vertex).map embedding).card :=
      Finset.card_le_card subset
    _ = (induced.graph.neighborFinset vertex).card := by
      rw [Finset.card_map]
    _ = induced.degree vertex := by
      rfl

/-- Internal minimum-degree freeness produces a proof-selected bounded
elimination schedule.  The construction is a finite certificate existence
proof; executable auditing is delegated to CT12 below. -/
theorem exists_certificate_of_internalMinDegreeFree
    {V : Type u} (object : FiniteObject V) (bound : Nat)
    (free : object.InternalMinDegreeFree (bound + 1)) :
    Nonempty (Certificate object bound) := by
  letI : FinEnum V := object.input.vertices
  letI : Fintype V := @FinEnum.instFintype _ object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  have build : ∀ support : Finset V,
      Nonempty (PartialCertificate object bound support) := by
    intro support
    induction support using Finset.strongInduction with
    | H support ih =>
        by_cases supportEmpty : support = ∅
        · subst support
          exact ⟨{
            values := []
            nodup := by simp
            exact := by simp
            bounded := .nil
          }⟩
        · have supportNonempty : support.Nonempty :=
            Finset.nonempty_iff_ne_empty.mpr supportEmpty
          let induced := object.induceFinset support
          letI : Nonempty {vertex : V // vertex ∈ support} :=
            Finset.nonempty_coe_sort.mpr supportNonempty
          letI : FinEnum {vertex : V // vertex ∈ support} :=
            induced.input.vertices
          letI : Fintype {vertex : V // vertex ∈ support} :=
            @FinEnum.instFintype _ induced.input.vertices
          letI : DecidableRel induced.graph.Adj := induced.input.decideAdj
          have minDegreeLe : induced.minDegree ≤ bound := by
            have notHigh : ¬bound + 1 ≤ induced.minDegree := by
              intro high
              exact free ⟨support, high⟩
            omega
          have notAllHigh :
              ¬∀ vertex, bound + 1 ≤ induced.degree vertex := by
            intro allHigh
            have highMinimum : bound + 1 ≤ induced.minDegree :=
              induced.le_minDegree_of_forall_le_degree (bound + 1) allHigh
            omega
          push Not at notAllHigh
          obtain ⟨vertex, vertexLow⟩ := notAllHigh
          have vertexLow' : induced.degree vertex ≤ bound := by omega
          let remainder := support.erase vertex.1
          have remainderStrict : remainder ⊂ support := by
            exact Finset.erase_ssubset vertex.2
          obtain ⟨⟨tail, tailNodup, tailExact, tailBounded⟩⟩ :=
            ih remainder remainderStrict
          have vertexNotTail : vertex.1 ∉ tail := by
            intro member
            have inRemainder := (tailExact vertex.1).1 member
            have absent : vertex.1 ∉ remainder := by
              simp [remainder]
            exact absent inRemainder
          have tailSubset : ∀ value, value ∈ tail → value ∈ support := by
            intro value member
            exact Finset.mem_of_mem_erase ((tailExact value).1 member)
          have headBound :
              (laterNeighbors object vertex.1 tail).length ≤ bound :=
            (laterNeighbors_length_le_inducedDegree object support vertex tail
              tailNodup tailSubset).trans vertexLow'
          refine ⟨{
            values := vertex.1 :: tail
            nodup := ?_
            exact := ?_
            bounded := .cons headBound tailBounded
          }⟩
          · exact List.nodup_cons.mpr ⟨vertexNotTail, tailNodup⟩
          · intro value
            constructor
            · intro member
              rcases List.mem_cons.mp member with equal | inTail
              · subst value
                exact vertex.2
              · exact tailSubset value inTail
            · intro member
              by_cases equal : value = vertex.1
              · exact List.mem_cons.mpr (Or.inl equal)
              · apply List.mem_cons.mpr
                right
                apply (tailExact value).2
                exact Finset.mem_erase.mpr ⟨equal, member⟩
  obtain ⟨⟨values, nodup, exact, bounded⟩⟩ :=
    build (Finset.univ : Finset V)
  exact ⟨{
    values := values
    nodup := nodup
    complete := fun vertex => (exact vertex).2 (Finset.mem_univ vertex)
    bounded := bounded
  }⟩

/-- Canonical proof-selected elimination certificate. -/
noncomputable def certificateOfInternalMinDegreeFree
    {V : Type u} (object : FiniteObject V) (bound : Nat)
    (free : object.InternalMinDegreeFree (bound + 1)) :
    Certificate object bound :=
  Classical.choice (exists_certificate_of_internalMinDegreeFree object bound free)

/-- The sharp edge bound obtained by repeatedly peeling a vertex of degree at
most two.  Every recursive call is on one explicitly smaller support, so this
is the graph-theoretic theorem audited by the CT12 elimination schedule rather
than a search through finite graphs. -/
theorem edgeCount_le_two_mul_vertexCount_sub_three
    {V : Type u} (object : FiniteObject V)
    (free : object.InternalMinDegreeFree 3)
    (atLeastTwo : 2 ≤ object.input.vertices.card) :
    object.edgeCount ≤ 2 * object.input.vertices.card - 3 := by
  letI : FinEnum V := object.input.vertices
  letI : Fintype V := @FinEnum.instFintype _ object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  have supportBound : ∀ support : Finset V, 2 ≤ support.card →
      (object.induceFinset support).edgeCount ≤ 2 * support.card - 3 := by
    intro support
    induction support using Finset.strongInduction with
    | H support ih =>
        intro supportLarge
        let induced := object.induceFinset support
        letI : Nonempty {vertex : V // vertex ∈ support} := by
          exact Finset.nonempty_coe_sort.mpr
            (Finset.card_pos.mp (by omega))
        have notAllHigh :
            ¬∀ vertex, 3 ≤ induced.degree vertex := by
          intro allHigh
          apply free
          exact ⟨support,
            induced.le_minDegree_of_forall_le_degree 3 allHigh⟩
        push Not at notAllHigh
        obtain ⟨vertex, vertexLow⟩ := notAllHigh
        have degreeAtMostTwo : induced.degree vertex ≤ 2 := by omega
        let remainder := support.erase vertex.1
        have remainderStrict : remainder ⊂ support :=
          Finset.erase_ssubset vertex.2
        have cardRecurrence : remainder.card + 1 = support.card := by
          rw [show remainder.card = support.card - 1 by
            simp [remainder, Finset.card_erase_of_mem vertex.2]]
          omega
        by_cases remainderLarge : 2 ≤ remainder.card
        · have smallerBound := ih remainder remainderStrict remainderLarge
          have edgeRecurrence :=
            object.edgeCount_induceFinset_erase_add_degree
              support vertex.1 vertex.2
          change (object.induceFinset remainder).edgeCount +
              (object.induceFinset support).degree vertex =
                (object.induceFinset support).edgeCount at edgeRecurrence
          change (object.induceFinset support).degree vertex ≤ 2 at degreeAtMostTwo
          omega
        · have supportCard : support.card = 2 := by omega
          have edgeUpper := induced.edgeCount_le_choose_two
          rw [object.induceFinset_vertexCount] at edgeUpper
          norm_num [supportCard] at edgeUpper ⊢
          exact edgeUpper
  have whole := supportBound object.vertexFinset (by
    simpa using atLeastTwo)
  rw [object.induceFinset_univ_edgeCount] at whole
  simpa using whole

namespace Certificate

variable {V : Type u} {object : FiniteObject V} {bound : Nat}

/-- The certificate lists every declared vertex exactly once. -/
theorem length_eq_vertexCount (certificate : Certificate object bound) :
    certificate.values.length = object.input.vertices.card := by
  letI : FinEnum V := object.input.vertices
  letI : Fintype V := @FinEnum.instFintype _ object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  rw [← List.toFinset_card_of_nodup certificate.nodup]
  have all : certificate.values.toFinset = Finset.univ := by
    ext vertex
    simp [certificate.complete]
  rw [all, Finset.card_univ]
  exact FinEnum.card_eq_fintypeCard.symm

/-- Execute CT12 on the complete elimination schedule. -/
def run {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P)
    (certificate : Certificate object bound) :=
  CT12.ListPeeling.run context certificate.values

theorem run_terminal_exhausted {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P)
    (certificate : Certificate object bound) :
    (certificate.run context).terminal = .exhausted :=
  CT12.ListPeeling.run_terminal_exhausted context certificate.values

theorem run_iterations_eq_vertexCount
    {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P)
    (certificate : Certificate object bound) :
    (certificate.run context).iterations = object.input.vertices.card := by
  unfold run
  rw [CT12.ListPeeling.run_iterations_eq_length]
  exact certificate.length_eq_vertexCount

/-- Exact CT12 trace, including every saturation/peel/restoration/decrease
loop and the final exhausted terminal. -/
theorem run_trace_eq_expected
    {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P)
    (certificate : Certificate object bound) :
    (certificate.run context).trace =
      CT12.ListPeeling.expectedTrace object.input.vertices.card := by
  unfold run
  rw [CT12.ListPeeling.run_trace_eq_expected]
  rw [certificate.length_eq_vertexCount]

theorem run_trace_valid {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P)
    (certificate : Certificate object bound) :
    CT12.Graph.ValidTrace (CT12.ListPeeling.capability P V)
      (certificate.run context).trace :=
  CT12.run_trace_valid _ _

theorem run_total {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P)
    (certificate : Certificate object bound) :
    ∃ result, result = certificate.run context ∧
      result.outcome.Valid ∧
      CT12.Graph.ValidTrace (CT12.ListPeeling.capability P V) result.trace ∧
      result.iterations ≤ object.input.vertices.card := by
  refine ⟨certificate.run context, rfl, CT12.run_verified _ _,
    certificate.run_trace_valid context, ?_⟩
  rw [certificate.run_iterations_eq_vertexCount context]

/-- The CT12 machine performs exactly one local peeling iteration per
certificate vertex, hence has a uniform linear primitive-check budget. -/
noncomputable def budget {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P)
    (certificate : Certificate object bound) :
    Core.PolynomialCheckBudget Unit where
  size := fun _ => object.input.vertices.card
  checks := fun _ => (certificate.run context).iterations
  coefficient := 1
  degree := 1
  bounded := by
    intro _unit
    rw [certificate.run_iterations_eq_vertexCount context]
    simp

/-- Complete reusable audit record for a certified degeneracy peeling run. -/
structure VerifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P)
    (certificate : Certificate object bound) : Prop where
  terminal : (certificate.run context).terminal = .exhausted
  trace : (certificate.run context).trace =
    CT12.ListPeeling.expectedTrace object.input.vertices.card
  verified : (certificate.run context).outcome.Valid
  traceValid : CT12.Graph.ValidTrace (CT12.ListPeeling.capability P V)
    (certificate.run context).trace
  total : ∃ result, result = certificate.run context ∧
    result.outcome.Valid ∧
    CT12.Graph.ValidTrace (CT12.ListPeeling.capability P V) result.trace ∧
    result.iterations ≤ object.input.vertices.card
  linearWork : (certificate.run context).iterations =
    object.input.vertices.card

theorem verifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P)
    (certificate : Certificate object bound) :
    VerifiedStage context certificate where
  terminal := certificate.run_terminal_exhausted context
  trace := certificate.run_trace_eq_expected context
  verified := CT12.run_verified _ _
  traceValid := certificate.run_trace_valid context
  total := certificate.run_total context
  linearWork := certificate.run_iterations_eq_vertexCount context

end Certificate

/-- Local mathematical contract for a proof-selected bounded elimination
order.  Certificate existence is proved from induced-core freeness; the CT12
runner inspects only the resulting finite vertex list. -/
structure Profile {V : Type u} (object : FiniteObject V) (bound : Nat) where
  free : object.InternalMinDegreeFree (bound + 1)

namespace Profile

variable {V : Type u} {object : FiniteObject V} {bound : Nat}

noncomputable def certificate (profile : Profile object bound) :
    Certificate object bound :=
  certificateOfInternalMinDegreeFree object bound profile.free

noncomputable def run {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile object bound) (context : Core.BranchContext P) :=
  profile.certificate.run context

theorem verifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile object bound) (context : Core.BranchContext P) :
    Certificate.VerifiedStage context profile.certificate :=
  profile.certificate.verifiedStage context

noncomputable def budget {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile object bound) (context : Core.BranchContext P) :
    Core.PolynomialCheckBudget Unit :=
  profile.certificate.budget context

/-- Sharp semantic consequence for the two-degenerate instance used by the
sparse upper-envelope argument. -/
theorem edgeCount_le_two_mul_vertexCount_sub_three
    (profile : Profile object 2)
    (atLeastTwo : 2 ≤ object.input.vertices.card) :
    object.edgeCount ≤ 2 * object.input.vertices.card - 3 :=
  DegeneracyPeeling.edgeCount_le_two_mul_vertexCount_sub_three object
    profile.free atLeastTwo

end Profile

end StructuralExhaustion.Graph.DegeneracyPeeling
