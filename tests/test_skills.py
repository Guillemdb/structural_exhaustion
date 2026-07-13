from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SKILLS_ROOT = ROOT / ".agents/skills"
STRATEGY = "design-structural-exhaustion-proof"
ROUTE = "implement-structural-exhaustion-route"
ERDOS_NEXT_CT = "implement-next-erdos-64-eg-ct"
CT_SKILLS = {
    f"implement-structural-exhaustion-ct{number}": f"CT{number}"
    for number in range(1, 18)
}
EXPECTED_SKILLS = {STRATEGY, ROUTE, ERDOS_NEXT_CT, *CT_SKILLS}


def read_skill(name: str) -> str:
    return (SKILLS_ROOT / name / "SKILL.md").read_text(encoding="utf-8")


def frontmatter(content: str) -> dict[str, str]:
    match = re.match(r"^---\n(?P<body>.*?)\n---\n", content, re.DOTALL)
    assert match is not None
    fields: dict[str, str] = {}
    for line in match.group("body").splitlines():
        key, separator, value = line.partition(":")
        assert separator == ":"
        fields[key.strip()] = value.strip().strip('"')
    return fields


def quoted_yaml_value(content: str, key: str) -> str:
    match = re.search(rf'^\s+{re.escape(key)}: "(?P<value>.*)"$', content, re.MULTILINE)
    assert match is not None
    return match.group("value")


def test_skill_inventory_and_metadata_are_complete() -> None:
    skill_directories = {
        path.name for path in SKILLS_ROOT.iterdir() if path.is_dir()
    }
    assert skill_directories == EXPECTED_SKILLS

    total_description_length = 0
    for name in sorted(EXPECTED_SKILLS):
        directory = SKILLS_ROOT / name
        skill = read_skill(name)
        metadata = frontmatter(skill)
        assert metadata.keys() == {"name", "description"}
        assert metadata["name"] == name
        assert 1 <= len(metadata["description"]) <= 1024
        total_description_length += len(metadata["description"])
        assert len(skill.splitlines()) < 500
        assert not any(
            marker in skill
            for marker in (
                "[TODO",
                "FIXME",
                "Structuring This Skill",
                "Replace with the first main section",
            )
        )
        assert not any((directory / child).exists() for child in ("scripts", "references", "assets"))

        ui = (directory / "agents/openai.yaml").read_text(encoding="utf-8")
        assert ui.startswith("interface:\n")
        assert set(re.findall(r"^\s{2}([a-z_]+):", ui, re.MULTILINE)) == {
            "display_name",
            "short_description",
            "default_prompt",
        }
        short_description = quoted_yaml_value(ui, "short_description")
        default_prompt = quoted_yaml_value(ui, "default_prompt")
        assert 25 <= len(short_description) <= 64
        assert f"${name}" in default_prompt

    assert total_description_length < 8000


def test_each_ct_skill_tracks_its_live_contract_and_fixture() -> None:
    catalog = json.loads(
        (ROOT / "generated/lean-machines.json").read_text(encoding="utf-8")
    )
    catalog_ids = {tactic["tacticId"] for tactic in catalog["tactics"]}
    assert catalog_ids == {f"CT{number}" for number in range(1, 18)}

    for name, tactic_id in CT_SKILLS.items():
        skill = read_skill(name)
        assert f'select(.tacticId == "{tactic_id}")' in skill
        assert f"{tactic_id}/Automation.lean" in skill
        assert f"Examples/{tactic_id}AutomationFirst.lean" in skill
        assert "The framework owns" in skill
        assert "polynomial" in skill.lower()
        assert "terminal" in skill.lower()
        assert "trace" in skill.lower()


def test_ct_skills_encode_the_specialized_reuse_surfaces() -> None:
    required_by_skill = {
        "implement-structural-exhaustion-ct1": (
            "TargetCertificateEncoding",
            "TargetEncoding",
            "workBound",
        ),
        "implement-structural-exhaustion-ct2": (
            "LocalDeletionCapability",
            "Capability.deletionOnly",
            "localDeletionBudget",
        ),
        "implement-structural-exhaustion-ct3": (
            "TargetCompressionContract",
            "response_correct",
            "localCheckBound",
        ),
        "implement-structural-exhaustion-ct4": ("FunctionalCardinalityProfile",),
        "implement-structural-exhaustion-ct6": ("ActiveLedgerRun",),
        "implement-structural-exhaustion-ct9": (
            "OverloadedRun",
            "ParityCapacityOneSpec",
        ),
        "implement-structural-exhaustion-ct11": ("NegativeBudgetProfile",),
        "implement-structural-exhaustion-ct12": ("ListPeeling",),
    }
    for name, declarations in required_by_skill.items():
        skill = read_skill(name)
        for declaration in declarations:
            assert declaration in skill


def test_strategy_skill_covers_selection_locality_and_delegation() -> None:
    skill = read_skill(STRATEGY)
    for number in range(1, 18):
        assert f"| CT{number} |" in skill
    assert "implement-structural-exhaustion-ctN/SKILL.md" in skill
    for declaration in (
        "Graph.MinimumDegreeCycle.StaticInput",
        "Graph.EndpointParityCycle.Profile",
        "Graph.GreedyColoring",
        "CT1.TargetCertificateEncoding",
        "CT2.LocalDeletionCapability",
        "CT3.TargetCompressionContract",
        "CT4.FunctionalCardinalityProfile",
        "CT9.ParityCapacityOneSpec",
        "CT11.NegativeBudgetProfile",
        "CT12.ListPeeling",
        "Core.FiniteSaturation.Machine",
        "Core.PolynomialCheckBudget",
    ):
        assert declaration in skill
    for prohibited_universe in (
        "all graphs",
        "all subgraphs",
        "all colorings",
        "SimpleGraph V",
    ):
        assert prohibited_universe in skill
    assert "implement-structural-exhaustion-route/SKILL.md" in skill


def test_route_skill_covers_every_registered_authoring_boundary() -> None:
    skill = read_skill(ROUTE)
    catalog = json.loads(
        (ROOT / "generated/lean-machines.json").read_text(encoding="utf-8")
    )
    assert len(catalog["routes"]) == 5
    for route_phrase, adapter, example in (
        ("CT1 avoidance to CT2", "MinimalityKernel", "CT1ToCT2AutomationFirst.lean"),
        (
            "CT1 avoidance to local-deletion CT2",
            "LocalDeletionCapability",
            "CT1ToCT2AutomationFirst.lean",
        ),
        ("CT2 separating context to CT3", "PieceDiscovery", "CT2ToCT3AutomationFirst.lean"),
        ("CT2 criticality to CT10", "DataDiscovery", "CT2ToCT10AutomationFirst.lean"),
        ("CT6 active ledger to CT9", "ItemCollectionAdapter", "CT6ToCT9AutomationFirst.lean"),
    ):
        assert route_phrase in skill
        assert adapter in skill
        assert example in skill


def test_erdos_next_ct_skill_advances_one_unconditional_stage() -> None:
    skill = read_skill(ERDOS_NEXT_CT)

    for authority in (
        "proofs/erdos_64_eg/erdos_64_proof.tex",
        "Erdos64EG/OfficialStatement.lean",
        "Erdos64EG/InternalProblem.lean",
        "Proof-dependency diagram",
        "Detailed dependency table",
        "generated/lean-machines.json",
        "design-structural-exhaustion-proof/SKILL.md",
        "implement-structural-exhaustion-ctN/SKILL.md",
        "implement-structural-exhaustion-route/SKILL.md",
    ):
        assert authority in skill

    for one_stage_guardrail in (
        "Advance exactly one CT per invocation",
        "first dependency-ready manuscript stage that fails the audit",
        "caller-supplied contract",
        "preceding execution result",
        "Do not start a second CT",
    ):
        assert one_stage_guardrail in skill

    for rigorous_output in (
        "public framework runner",
        "terminal-indexed outcome",
        "typed trace",
        "semantic soundness",
        "totality",
        "Core.PolynomialCheckBudget",
    ):
        assert rigorous_output in skill


def test_erdos_next_ct_skill_keeps_tex_lean_and_web_bidirectionally_indexed() -> None:
    skill = read_skill(ERDOS_NEXT_CT)
    normalized = " ".join(skill.split())

    for authority in (
        "Erdos64EG/WebExport.lean",
        "generated/examples/erdos-64.json",
        "ExampleProofStepDescriptor",
        "ExampleDeclarationGroup",
        "erdosManuscript",
    ):
        assert authority in skill

    for invariant in (
        "Maintain the bidirectional TeX--Lean--web index",
        "never put Lean declaration names or implementation status in a LaTeX label",
        "The union of `p`'s declaration groups must equal `D(s)`",
        "Every displayed stage must map to exactly one proof step",
        "TeX label or diagram node -> proof step -> workflow stage",
        "selected Lean declaration -> declaration group and role",
        "explainedDeclarations == displayedDeclarations",
        "instead of hand-editing generated JSON",
        "recorded in TeX, Lean, and the generated web projection",
    ):
        assert invariant in normalized


def test_erdos_next_ct_skill_requires_transfer_and_current_state_log() -> None:
    skill = read_skill(ERDOS_NEXT_CT)
    normalized = " ".join(skill.split())

    for transfer_requirement in (
        "non-Erdős problem instantiation",
        "standard textbook graph theorem",
        "does not alone satisfy this problem-transfer requirement",
        "builds as an external example package",
        "Reuse the generalized graph/core material",
    ):
        assert transfer_requirement in normalized

    assert "examples/erdos_64_eg/IMPLEMENTATION_LOG.md" in skill
    for log_field in (
        "manuscript section, theorem labels, and diagram nodes",
        "provenance chain from the official problem through prior CT outputs",
        "runner, terminal or residual, typed trace, semantic theorem, totality",
        "Reconcile the whole ledger against the compiled Lean declarations",
        "next dependency-ready manuscript section",
        "If validation fails, leave the verified frontier unchanged",
    ):
        assert log_field in normalized

    for layer_rule in (
        "examples/erdos_64_eg",
        "lean/StructuralExhaustion/Graph",
        "API design error",
        "Never put Erdős names or constants in `Core`",
    ):
        assert layer_rule in normalized

    for prohibited_global_search in (
        "all `SimpleGraph V`",
        "all subgraphs",
        "all colorings",
        "all ambient contexts",
    ):
        assert prohibited_global_search in normalized
