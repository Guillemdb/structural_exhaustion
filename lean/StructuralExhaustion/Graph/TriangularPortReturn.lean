import Mathlib.Tactic
import StructuralExhaustion.CT1.TargetEncoding
import StructuralExhaustion.Graph.EdgeRootedReturn
import StructuralExhaustion.Graph.TriangularShoulderCompletion

namespace StructuralExhaustion.Graph.TriangularPortReturn

open StructuralExhaustion

universe u

/-!
# Certificate-driven returns at triangular ports

The input is one simple deleted-edge return supplied by a preceding
bridgelessness theorem.  This profile identifies its first vertex as one of
the two shoulders, removes the port endpoint, restores the root edge to a
cycle, and executes CT1 from that one proof-carrying certificate.  No walk,
path, cycle, subgraph, or ambient graph family is enumerated.
-/

abbrev Setup
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (center : V) :=
  TriangularShoulderCompletion.Setup base object baseline center

abbrev TriPort
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :=
  TriangularShoulderCompletion.TriPort setup

/-- The oriented centre-to-port edge whose return is required. -/
def rootDart
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (port : TriPort setup) : object.graph.Dart :=
  ⟨(center, HighCenterPort.endpoint object center port.1),
    HighCenterPort.endpoint_adjacent object center port.1⟩

/-- Exact certificate behind the manuscript's port-return path.  The site is
derived from the first vertex of the deleted-edge return and records which
of the two shoulders it is. -/
structure Certificate
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (port : TriPort setup) where
  root : DartReturn object.graph (rootDart setup port)
  site : TriangularShoulderCompletion.Site setup
  site_port : site.1 = port
  startsAt : TriangularShoulderCompletion.shoulder setup site = root.path.snd

namespace Certificate

variable
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    {port : TriPort setup}

/-- The root return is nonempty because its endpoints form a dart. -/
theorem root_not_nil (certificate : Certificate setup port) :
    ¬certificate.root.path.Nil :=
  certificate.root.path.not_nil_of_ne (rootDart setup port).snd_ne_fst

/-- Identify the first return vertex as a declared shoulder. -/
noncomputable def ofDartReturn
    (root : DartReturn object.graph (rootDart setup port)) :
    Certificate setup port := by
  classical
  have notNil : ¬root.path.Nil :=
    root.path.not_nil_of_ne (rootDart setup port).snd_ne_fst
  have deletedAdjacent := root.path.adj_snd notNil
  have ambientAdjacent : object.graph.Adj
      (HighCenterPort.endpoint object center port.1) root.path.snd :=
    (object.graph.deleteEdges_le {(rootDart setup port).edge}) deletedAdjacent
  have firstNeCenter : root.path.snd ≠ center := by
    intro firstEq
    have deleted := (SimpleGraph.deleteEdges_adj.mp deletedAdjacent).2
    apply deleted
    simp only [Set.mem_singleton_iff]
    change s(HighCenterPort.endpoint object center port.1, root.path.snd) =
      s(center, HighCenterPort.endpoint object center port.1)
    rw [firstEq]
    exact Sym2.eq_swap
  have member := HighCenterPort.mem_shoulders_of_adjacent_endpoint_of_ne_center
    object center port.1 ambientAdjacent firstNeCenter
  have alternatives :=
    HighCenterPort.eq_firstShoulder_or_eq_secondShoulder_of_mem
      object center setup.centerHigh setup.deletionCritical port.1 member
  by_cases first : root.path.snd =
      HighCenterPort.firstShoulder object center setup.centerHigh
        setup.deletionCritical port.1
  · refine ⟨root, ⟨port, false⟩, rfl, ?_⟩
    simpa [TriangularShoulderCompletion.shoulder] using first.symm
  · have second := alternatives.resolve_left first
    refine ⟨root, ⟨port, true⟩, rfl, ?_⟩
    simpa [TriangularShoulderCompletion.shoulder] using second.symm

/-- The simple shoulder-to-centre path after removing the first edge and
viewing the remainder in the ambient graph. -/
def path (certificate : Certificate setup port) :
    object.graph.Walk
      (TriangularShoulderCompletion.shoulder setup certificate.site) center :=
  ((certificate.root.path.tail.mapLe
      (object.graph.deleteEdges_le {(rootDart setup port).edge})).copy
    certificate.startsAt.symm rfl)

theorem path_isPath (certificate : Certificate setup port) :
    certificate.path.IsPath := by
  rw [path, SimpleGraph.Walk.isPath_copy]
  exact certificate.root.isPath.tail.mapLe _

/-- The path really lies in `G-x`: its support omits the port endpoint. -/
theorem endpoint_not_mem_path (certificate : Certificate setup port) :
    HighCenterPort.endpoint object center port.1 ∉ certificate.path.support := by
  have rootPath := certificate.root.isPath
  rw [← certificate.root.path.cons_tail_eq certificate.root_not_nil] at rootPath
  have absent := (SimpleGraph.Walk.cons_isPath_iff _ _).mp rootPath |>.2
  rw [path, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_mapLe_eq_support]
  simpa [rootDart] using absent

def edgeCertificate (certificate : Certificate setup port) :
    EdgeRootedReturn object.graph (fun _length => True) :=
  certificate.root.toEdgeRootedReturn

/-- Restoring `hx` and the removed first edge closes the original simple
cycle. -/
def cycle (certificate : Certificate setup port) :
    object.graph.Walk center center :=
  certificate.edgeCertificate.cycle

theorem cycle_isCycle (certificate : Certificate setup port) :
    certificate.cycle.IsCycle :=
  certificate.edgeCertificate.cycle_isCycle

theorem path_length (certificate : Certificate setup port) :
    certificate.path.length = certificate.root.path.tail.length := by
  rw [path, SimpleGraph.Walk.length_copy]
  change (certificate.root.path.tail.map _).length = _
  rw [SimpleGraph.Walk.length_map]

/-- Exact two-edge reconstruction arithmetic. -/
theorem cycle_length (certificate : Certificate setup port) :
    certificate.cycle.length = certificate.path.length + 2 := by
  have rootCycleLength := certificate.edgeCertificate.cycle_length
  have edgePathLength : certificate.edgeCertificate.path.length =
      certificate.root.path.length := rfl
  have pathLength := certificate.path_length
  have tailLength :=
    certificate.root.path.length_tail_add_one certificate.root_not_nil
  change certificate.edgeCertificate.cycle.length = certificate.path.length + 2
  rw [rootCycleLength, edgePathLength, pathLength]
  omega

/-- Target avoidance excludes the reconstructed cycle length. -/
theorem length_excluded (certificate : Certificate setup port)
    (avoids : ¬HasCycleWithLength object.graph base.LengthOK) :
    ¬base.LengthOK (certificate.path.length + 2) := by
  intro accepted
  apply avoids
  exact ⟨{
    vertex := center
    walk := certificate.cycle
    isCycle := certificate.cycle_isCycle
    length_ok := by rwa [certificate.cycle_length]
  }⟩

/-- Exact first-landing alternatives.  The third case is important: after
the initial shoulder edge the next completion may be the central edge at the
other shoulder.  Thus no unjustified "noncentral" conclusion is assumed. -/
def LandingAlternative (certificate : Certificate setup port) : Prop :=
  let Q := certificate.path
  let other := TriangularShoulderCompletion.otherShoulder setup certificate.site
  (Q.snd = center ∧ Q.length = 1) ∨
  (Q.snd ≠ center ∧ Q.snd ≠ other ∧
    TriangularShoulderCompletion.IsCompletion setup certificate.site Q.snd) ∨
  (Q.snd = other ∧ Q.tail.snd = center ∧ Q.length = 2) ∨
  (Q.snd = other ∧ Q.tail.snd ≠ center ∧
    TriangularShoulderCompletion.IsCompletion setup
      (TriangularShoulderCompletion.oppositeSite setup certificate.site)
      Q.tail.snd)

theorem landingAlternative (certificate : Certificate setup port) :
    certificate.LandingAlternative := by
  let Q := certificate.path
  let other := TriangularShoulderCompletion.otherShoulder setup certificate.site
  have qNotNil : ¬Q.Nil :=
    Q.not_nil_of_ne
      (TriangularShoulderCompletion.shoulder_ne_center setup certificate.site)
  have firstAdjacent := Q.adj_snd qNotNil
  have firstMem : Q.snd ∈ Q.support :=
    List.mem_of_mem_tail (Q.snd_mem_tail_support qNotNil)
  have firstNeEndpoint :
      Q.snd ≠ TriangularShoulderCompletion.endpoint setup certificate.site := by
    intro equal
    have endpointEq : TriangularShoulderCompletion.endpoint setup
        certificate.site = HighCenterPort.endpoint object center port.1 := by
      simp [TriangularShoulderCompletion.endpoint, certificate.site_port]
    apply certificate.endpoint_not_mem_path
    rw [← endpointEq]
    exact equal ▸ firstMem
  change (Q.snd = center ∧ Q.length = 1) ∨
    (Q.snd ≠ center ∧ Q.snd ≠ other ∧
      TriangularShoulderCompletion.IsCompletion setup certificate.site Q.snd) ∨
    (Q.snd = other ∧ Q.tail.snd = center ∧ Q.length = 2) ∨
    (Q.snd = other ∧ Q.tail.snd ≠ center ∧
      TriangularShoulderCompletion.IsCompletion setup
        (TriangularShoulderCompletion.oppositeSite setup certificate.site)
        Q.tail.snd)
  by_cases firstCentral : Q.snd = center
  · left
    refine ⟨firstCentral, ?_⟩
    have tailPath := certificate.path_isPath.tail
    change Q.tail.IsPath at tailPath
    have tailNil : Q.tail.Nil :=
      tailPath.nil_iff_eq.mpr firstCentral
    have tailLength := tailNil.length_eq_zero
    have splitLength := Q.length_tail_add_one qNotNil
    omega
  by_cases firstOther : Q.snd = other
  · right; right
    have otherNeCenter : other ≠ center :=
      TriangularShoulderCompletion.otherShoulder_ne_center setup certificate.site
    have tailNotNil : ¬Q.tail.Nil := by
      apply Q.tail.not_nil_of_ne
      simpa [firstOther] using otherNeCenter
    have secondAdjacent := Q.tail.adj_snd tailNotNil
    by_cases secondCentral : Q.tail.snd = center
    · left
      refine ⟨firstOther, secondCentral, ?_⟩
      have secondTailPath := certificate.path_isPath.tail.tail
      change Q.tail.tail.IsPath at secondTailPath
      have secondTailNil : Q.tail.tail.Nil :=
        secondTailPath.nil_iff_eq.mpr secondCentral
      have firstSplit := Q.length_tail_add_one qNotNil
      have secondSplit := Q.tail.length_tail_add_one tailNotNil
      have secondTailLength := secondTailNil.length_eq_zero
      omega
    · right
      refine ⟨firstOther, secondCentral, ?_⟩
      have secondMemTail : Q.tail.snd ∈ Q.tail.support :=
        List.mem_of_mem_tail (Q.tail.snd_mem_tail_support tailNotNil)
      have secondMem : Q.tail.snd ∈ Q.support := by
        rw [Q.support_tail_of_not_nil qNotNil] at secondMemTail
        exact List.mem_of_mem_tail secondMemTail
      have secondNeEndpoint :
          Q.tail.snd ≠ TriangularShoulderCompletion.endpoint setup
            (TriangularShoulderCompletion.oppositeSite setup certificate.site) := by
        intro equal
        have endpointEq : TriangularShoulderCompletion.endpoint setup
            (TriangularShoulderCompletion.oppositeSite setup certificate.site) =
            HighCenterPort.endpoint object center port.1 := by
          simp [TriangularShoulderCompletion.endpoint, certificate.site_port]
        apply certificate.endpoint_not_mem_path
        rw [← endpointEq]
        exact equal ▸ secondMem
      have supportNodup := certificate.path_isPath.support_nodup
      change Q.support.Nodup at supportNodup
      have startNotSupportTail :
          TriangularShoulderCompletion.shoulder setup certificate.site ∉
            Q.support.tail := by
        have nodupCons :
            (TriangularShoulderCompletion.shoulder setup certificate.site ::
              Q.support.tail).Nodup := by
          simpa only [Q.cons_tail_support] using supportNodup
        exact (List.nodup_cons.mp nodupCons).1
      have secondMemSupportTail : Q.tail.snd ∈ Q.support.tail := by
        rw [← Q.support_tail_of_not_nil qNotNil]
        exact secondMemTail
      have secondNeFirst : Q.tail.snd ≠
          TriangularShoulderCompletion.shoulder setup certificate.site := by
        exact ne_of_mem_of_not_mem secondMemSupportTail startNotSupportTail
      refine ⟨?_, secondNeEndpoint, ?_⟩
      · simpa [firstOther] using secondAdjacent
      · simpa using secondNeFirst
  · right; left
    refine ⟨firstCentral, firstOther, firstAdjacent, firstNeEndpoint, ?_⟩
    exact firstOther

end Certificate

/-- Public CT1 target for this fixed local port. -/
def PublicTarget
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (port : TriPort setup) (candidate : FiniteObject V) : Prop :=
  candidate = object ∧ Nonempty (Certificate setup port)

/-- Dependent CT1 code retaining the equality between the runner's ambient
object and the fixed graph supporting the local return. -/
structure TargetCode
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (port : TriPort setup) (candidate : FiniteObject V) where
  same : candidate = object
  returnCertificate : Certificate setup port

/-- Proof-carrying CT1 encoding.  Its code is the already constructed local
return; there is deliberately no code enumerator. -/
def encoding
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (port : TriPort setup) :
    CT1.TargetCertificateEncoding (P := base.problem)
      (PublicTarget setup port) where
  Code := TargetCode setup port
  Accepts := fun _candidate _code => True
  encode := by
    rintro candidate ⟨same, ⟨certificate⟩⟩
    exact ⟨⟨same, certificate⟩, trivial⟩
  decode := by
    intro candidate code _accepted
    exact ⟨code.same, ⟨code.returnCertificate⟩⟩

def input
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object) :
    CT1.Input base.problem :=
  ⟨⟨object, baseline, ()⟩⟩

noncomputable def certificate
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (port : TriPort setup)
    (root : DartReturn object.graph (rootDart setup port)) :
    Certificate setup port :=
  Certificate.ofDartReturn root

/-- One-check CT1 execution from the preceding return certificate. -/
noncomputable def run
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (port : TriPort setup)
    (root : DartReturn object.graph (rootDart setup port)) :
    CT1.CertifiedC1Run (encoding setup port).spec
      (input base object baseline) :=
  (encoding setup port).run (input base object baseline)
    ⟨rfl, certificate setup port root⟩ trivial

/-- Exact CT1 avoiding execution when no such local return exists.  This is
the negative proof-carrying branch and performs zero candidate checks. -/
def runAvoiding
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (port : TriPort setup) (noReturn : ¬Nonempty (Certificate setup port)) :
    CT1.CertifiedAvoidingRun (encoding setup port).spec
      (input base object baseline) :=
  (encoding setup port).runAvoiding (input base object baseline) <| by
    rintro ⟨_same, returnExists⟩
    exact noReturn returnExists

theorem runAvoiding_terminal
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (port : TriPort setup) (noReturn : ¬Nonempty (Certificate setup port)) :
    (runAvoiding setup port noReturn).result.terminal = .avoiding :=
  (runAvoiding setup port noReturn).terminal_eq

theorem runAvoiding_checks
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (port : TriPort setup) (noReturn : ¬Nonempty (Certificate setup port)) :
    (runAvoiding setup port noReturn).checks = 0 :=
  (runAvoiding setup port noReturn).checks_eq

/-- Complete framework-owned CT1 stage for one triangular port. -/
structure VerifiedStage
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (port : TriPort setup)
    (root : DartReturn object.graph (rootDart setup port))
    (avoids : ¬HasCycleWithLength object.graph base.LengthOK) : Prop where
  pathIsSimple : (certificate setup port root).path.IsPath
  avoidsEndpoint : HighCenterPort.endpoint object center port.1 ∉
    (certificate setup port root).path.support
  cycleIsSimple : (certificate setup port root).cycle.IsCycle
  cycleLength : (certificate setup port root).cycle.length =
    (certificate setup port root).path.length + 2
  lengthExcluded : ¬base.LengthOK
    ((certificate setup port root).path.length + 2)
  landing : (certificate setup port root).LandingAlternative
  terminal : (run setup port root).result.terminal = .c1
  trace : (run setup port root).result.trace =
    [.entry, .equivalenceCertification, .realizationDecision, .c1Terminal]
  total : CT1.OutcomeClaim (run setup port root).result.outcome
  checks : (run setup port root).checks = 1

noncomputable def verifiedStage
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (port : TriPort setup)
    (root : DartReturn object.graph (rootDart setup port))
    (avoids : ¬HasCycleWithLength object.graph base.LengthOK) :
    VerifiedStage setup port root avoids where
  pathIsSimple := (certificate setup port root).path_isPath
  avoidsEndpoint := (certificate setup port root).endpoint_not_mem_path
  cycleIsSimple := (certificate setup port root).cycle_isCycle
  cycleLength := (certificate setup port root).cycle_length
  lengthExcluded := (certificate setup port root).length_excluded avoids
  landing := (certificate setup port root).landingAlternative
  terminal := (run setup port root).terminal_eq
  trace := (run setup port root).trace_eq
  total := CT1.certifiedC1Run_verified (run setup port root)
  checks := (run setup port root).checks_eq

end StructuralExhaustion.Graph.TriangularPortReturn
