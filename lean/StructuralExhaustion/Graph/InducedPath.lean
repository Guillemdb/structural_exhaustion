import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic
import StructuralExhaustion.CT1.TargetEncoding
import StructuralExhaustion.Graph.FiniteObject

namespace StructuralExhaustion.Graph

open StructuralExhaustion

universe uAmbient uBranch uVertex

/-!
# Induced-path certificates and CT1 validation

An induced path on `order` vertices is represented by Mathlib's literal graph
embedding `pathGraph order ↪g G`.  The embedding is already a complete local
certificate: injectivity and preservation in both directions rule out repeated
vertices and chords.  CT1 therefore validates one supplied embedding without
enumerating vertex tuples, walks, subgraphs, or ambient graphs.
-/

/-- A literal induced copy of the path on `order` vertices. -/
def HasInducedPath {V : Type uVertex} (G : SimpleGraph V)
    (order : Nat) : Prop :=
  SimpleGraph.IsIndContained (SimpleGraph.pathGraph order) G

/-- The graph contains no induced path on `order` vertices. -/
def InducedPathFree {V : Type uVertex} (G : SimpleGraph V)
    (order : Nat) : Prop :=
  ¬ HasInducedPath G order

/-- Canonical induced two-vertex-path embedding carried by one edge. -/
def inducedPathTwoEmbeddingOfAdj {V : Type uVertex}
    {G : SimpleGraph V} {left right : V} (adjacent : G.Adj left right) :
    SimpleGraph.pathGraph 2 ↪g G := by
  let vertex : Fin 2 → V := fun index =>
    if index = 0 then left else right
  have vertex_injective : Function.Injective vertex := by
    intro first second equal
    fin_cases first <;> fin_cases second <;>
      simp [vertex, adjacent.ne, adjacent.symm.ne] at equal ⊢
  refine {
    toFun := vertex
    inj' := vertex_injective
    map_rel_iff' := ?_
  }
  intro first second
  fin_cases first <;> fin_cases second <;>
    simp [vertex, SimpleGraph.pathGraph_adj, adjacent, adjacent.symm]

/-- Any edge is an induced copy of the two-vertex path. -/
theorem hasInducedPath_two_of_adj {V : Type uVertex}
    {G : SimpleGraph V} {left right : V} (adjacent : G.Adj left right) :
    HasInducedPath G 2 :=
  ⟨inducedPathTwoEmbeddingOfAdj adjacent⟩

namespace InducedPath

/-- Reusable graph family whose induced-path target is validated by CT1. -/
structure Profile
    {P : Core.Problem.{uAmbient, uBranch}} where
  Vertex : P.Ambient → Type uVertex
  graph : (ambient : P.Ambient) → SimpleGraph (Vertex ambient)
  order : Nat

namespace Profile

/-- Public graph target carried by an induced-path profile. -/
def Target {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (ambient : P.Ambient) : Prop :=
  HasInducedPath (profile.graph ambient) profile.order

/-- The proof-carrying code is the induced graph embedding itself. -/
abbrev Code {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (ambient : P.Ambient) :=
  SimpleGraph.pathGraph profile.order ↪g profile.graph ambient

/-- Certificate-driven CT1 encoding for induced paths. -/
def encoding {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P)) :
    CT1.TargetCertificateEncoding profile.Target where
  Code := profile.Code
  Accepts := fun _ambient _certificate => True
  encode := by
    intro ambient target
    rcases target with ⟨certificate⟩
    exact ⟨certificate, trivial⟩
  decode := by
    intro ambient certificate _accepted
    exact ⟨certificate⟩

/-- Execute CT1 from one explicit induced-path embedding. -/
def run {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P) (certificate : profile.Code input.context.G) :
    CT1.CertifiedC1Run profile.encoding.spec input :=
  profile.encoding.run input certificate trivial

/-- Execute CT1's avoiding path from an exact induced-path-free proof. -/
def runAvoiding {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P)
    (free : InducedPathFree (profile.graph input.context.G) profile.order) :
    CT1.CertifiedAvoidingRun profile.encoding.spec input :=
  profile.encoding.runAvoiding input free

theorem run_terminal {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P) (certificate : profile.Code input.context.G) :
    (profile.run input certificate).result.terminal = .c1 :=
  (profile.run input certificate).terminal_eq

theorem run_trace {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P) (certificate : profile.Code input.context.G) :
    (profile.run input certificate).result.trace =
      [.entry, .equivalenceCertification, .realizationDecision,
        .c1Terminal] :=
  (profile.run input certificate).trace_eq

theorem run_verified {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P) (certificate : profile.Code input.context.G) :
    profile.Target input.context.G :=
  profile.encoding.publicTarget_of_run input certificate trivial

theorem run_total {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P) (certificate : profile.Code input.context.G) :
    ∃ run : CT1.CertifiedC1Run profile.encoding.spec input,
      run.result.terminal = .c1 ∧
        run.result.trace =
          [.entry, .equivalenceCertification, .realizationDecision,
            .c1Terminal] :=
  ⟨profile.run input certificate,
    profile.run_terminal input certificate,
    profile.run_trace input certificate⟩

theorem run_checks {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P) (certificate : profile.Code input.context.G) :
    (profile.run input certificate).checks = 1 :=
  (profile.run input certificate).checks_eq

theorem run_polynomial {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P) (certificate : profile.Code input.context.G) :
    (profile.run input certificate).checks ≤
      (CT1.certifiedC1Budget profile.encoding.spec).coefficient *
        ((CT1.certifiedC1Budget profile.encoding.spec).size input + 1) ^
          (CT1.certifiedC1Budget profile.encoding.spec).degree := by
  change 1 ≤ 1 * (1 + 1) ^ 0
  decide

theorem runAvoiding_terminal {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P)
    (free : InducedPathFree (profile.graph input.context.G) profile.order) :
    (profile.runAvoiding input free).result.terminal = .avoiding :=
  (profile.runAvoiding input free).terminal_eq

theorem runAvoiding_trace {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P)
    (free : InducedPathFree (profile.graph input.context.G) profile.order) :
    (profile.runAvoiding input free).result.trace =
      [.entry, .equivalenceCertification, .realizationDecision,
        .avoidingTerminal] :=
  (profile.runAvoiding input free).trace_eq

theorem runAvoiding_verified {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P)
    (free : InducedPathFree (profile.graph input.context.G) profile.order) :
    InducedPathFree (profile.graph input.context.G) profile.order :=
  profile.encoding.not_publicTarget_of_runAvoiding input free

theorem runAvoiding_total {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P)
    (free : InducedPathFree (profile.graph input.context.G) profile.order) :
    ∃ run : CT1.CertifiedAvoidingRun profile.encoding.spec input,
      run.result.terminal = .avoiding ∧
        run.result.trace =
          [.entry, .equivalenceCertification, .realizationDecision,
            .avoidingTerminal] :=
  ⟨profile.runAvoiding input free,
    profile.runAvoiding_terminal input free,
    profile.runAvoiding_trace input free⟩

theorem runAvoiding_checks {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P)
    (free : InducedPathFree (profile.graph input.context.G) profile.order) :
    (profile.runAvoiding input free).checks = 0 :=
  (profile.runAvoiding input free).checks_eq

theorem runAvoiding_polynomial {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P)
    (free : InducedPathFree (profile.graph input.context.G) profile.order) :
    (profile.runAvoiding input free).checks ≤
      (CT1.certifiedAvoidingBudget profile.encoding.spec).coefficient *
        ((CT1.certifiedAvoidingBudget profile.encoding.spec).size input + 1) ^
          (CT1.certifiedAvoidingBudget profile.encoding.spec).degree := by
  change 0 ≤ 0 * (1 + 1) ^ 0
  decide

/-- Complete CT1 output after an induced-path realization has been forced.
It retains one exact C1 execution existentially, together with its semantic
claim, trace, totality, and constant work bound. -/
structure VerifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P) : Prop where
  realization : profile.Target input.context.G
  execution : ∃ certificate : profile.Code input.context.G,
    (profile.run input certificate).result.terminal = .c1 ∧
      (profile.run input certificate).result.trace =
        [.entry, .equivalenceCertification, .realizationDecision,
          .c1Terminal] ∧
      profile.Target input.context.G ∧
      (∃ run : CT1.CertifiedC1Run profile.encoding.spec input,
        run.result.terminal = .c1 ∧
          run.result.trace =
            [.entry, .equivalenceCertification, .realizationDecision,
              .c1Terminal]) ∧
      (profile.run input certificate).checks = 1 ∧
      (profile.run input certificate).checks ≤
        (CT1.certifiedC1Budget profile.encoding.spec).coefficient *
          ((CT1.certifiedC1Budget profile.encoding.spec).size input + 1) ^
            (CT1.certifiedC1Budget profile.encoding.spec).degree

/-- Construct the complete certificate-driven stage from the mathematical
induced-path realization. -/
def verifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uVertex} (P := P))
    (input : CT1.Input P) (realization : profile.Target input.context.G) :
    profile.VerifiedStage input := by
  refine {
    realization := realization
    execution := ?_
  }
  rcases realization with ⟨certificate⟩
  exact ⟨certificate,
    profile.run_terminal input certificate,
    profile.run_trace input certificate,
    profile.run_verified input certificate,
    profile.run_total input certificate,
    profile.run_checks input certificate,
    profile.run_polynomial input certificate⟩

end Profile

/-! ## Canonical edge specialization -/

/-- Reusable order-two induced-path profile for an explicitly finite graph. -/
def edgeProfile (V : Type uVertex) :
    Profile (P := FiniteObject.problem V) where
  Vertex := fun _object => V
  graph := fun object => object.graph
  order := 2

/-- Canonical CT1 input for an explicitly finite graph object. -/
def edgeInput {V : Type uVertex} (object : FiniteObject V) :
    CT1.Input (FiniteObject.problem V) where
  context := FiniteObject.context object

/-- The proof-carrying induced-`P₂` certificate carried by one dart. -/
def edgeCertificate {V : Type uVertex} (object : FiniteObject V)
    (dart : object.graph.Dart) :
    (edgeProfile V).Code object :=
  inducedPathTwoEmbeddingOfAdj dart.adj

/-- Execute the canonical induced-`P₂` CT1 stage from one graph edge. -/
def runEdge {V : Type uVertex} (object : FiniteObject V)
    (dart : object.graph.Dart) :=
  (edgeProfile V).run (edgeInput object) (edgeCertificate object dart)

theorem runEdge_terminal {V : Type uVertex} (object : FiniteObject V)
    (dart : object.graph.Dart) :
    (runEdge object dart).result.terminal = .c1 :=
  (edgeProfile V).run_terminal (edgeInput object) (edgeCertificate object dart)

theorem runEdge_trace {V : Type uVertex} (object : FiniteObject V)
    (dart : object.graph.Dart) :
    (runEdge object dart).result.trace =
      [.entry, .equivalenceCertification, .realizationDecision,
        .c1Terminal] :=
  (edgeProfile V).run_trace (edgeInput object) (edgeCertificate object dart)

theorem runEdge_verified {V : Type uVertex} (object : FiniteObject V)
    (dart : object.graph.Dart) :
    HasInducedPath object.graph 2 :=
  (edgeProfile V).run_verified (edgeInput object) (edgeCertificate object dart)

theorem runEdge_total {V : Type uVertex} (object : FiniteObject V)
    (dart : object.graph.Dart) :
    ∃ run : CT1.CertifiedC1Run (edgeProfile V).encoding.spec
        (edgeInput object),
      run.result.terminal = .c1 ∧
        run.result.trace =
          [.entry, .equivalenceCertification, .realizationDecision,
            .c1Terminal] :=
  (edgeProfile V).run_total (edgeInput object) (edgeCertificate object dart)

theorem runEdge_checks {V : Type uVertex} (object : FiniteObject V)
    (dart : object.graph.Dart) :
    (runEdge object dart).checks = 1 :=
  (edgeProfile V).run_checks (edgeInput object) (edgeCertificate object dart)

theorem runEdge_polynomial {V : Type uVertex} (object : FiniteObject V)
    (dart : object.graph.Dart) :
    (runEdge object dart).checks ≤
      (CT1.certifiedC1Budget (edgeProfile V).encoding.spec).coefficient *
        ((CT1.certifiedC1Budget
            (edgeProfile V).encoding.spec).size (edgeInput object) + 1) ^
          (CT1.certifiedC1Budget (edgeProfile V).encoding.spec).degree :=
  (edgeProfile V).run_polynomial (edgeInput object) (edgeCertificate object dart)

/-- Complete reusable graph-level CT1 result obtained from one edge. -/
def verifiedEdgeStage {V : Type uVertex} (object : FiniteObject V)
    (dart : object.graph.Dart) :
    (edgeProfile V).VerifiedStage (edgeInput object) :=
  (edgeProfile V).verifiedStage (edgeInput object)
    (hasInducedPath_two_of_adj dart.adj)

end InducedPath

end StructuralExhaustion.Graph
