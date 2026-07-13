import StructuralExhaustion.Graph.InducedPath

namespace StructuralExhaustion.Examples.CT1InducedPath

open StructuralExhaustion

/-- Minimal framework problem used to pin the induced-path CT1 profile. -/
def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def input : CT1.Input problem where
  context := ⟨(), trivial, ()⟩

def profile : Graph.InducedPath.Profile (P := problem) where
  Vertex := fun _ => Fin 2
  graph := fun _ => SimpleGraph.pathGraph 2
  order := 2

def certificate : profile.Code input.context.G :=
  SimpleGraph.Embedding.refl

def run := profile.run input certificate

theorem terminal : run.result.terminal = .c1 :=
  profile.run_terminal input certificate

theorem trace : run.result.trace =
    [.entry, .equivalenceCertification, .realizationDecision,
      .c1Terminal] :=
  profile.run_trace input certificate

theorem semantic : profile.Target input.context.G :=
  profile.run_verified input certificate

theorem total :
    ∃ execution : CT1.CertifiedC1Run profile.encoding.spec input,
      execution.result.terminal = .c1 ∧
        execution.result.trace =
          [.entry, .equivalenceCertification, .realizationDecision,
            .c1Terminal] :=
  profile.run_total input certificate

theorem checks : run.checks = 1 :=
  profile.run_checks input certificate

theorem polynomial : run.checks ≤
    (CT1.certifiedC1Budget profile.encoding.spec).coefficient *
      ((CT1.certifiedC1Budget profile.encoding.spec).size input + 1) ^
        (CT1.certifiedC1Budget profile.encoding.spec).degree :=
  profile.run_polynomial input certificate

def verifiedStage : profile.VerifiedStage input :=
  profile.verifiedStage input semantic

end StructuralExhaustion.Examples.CT1InducedPath
