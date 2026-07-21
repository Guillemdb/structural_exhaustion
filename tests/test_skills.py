from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SKILLS_ROOT = ROOT / ".agents/skills"

CT_SKILLS = {
    f"implement-hypostructure-ct{number}": f"CT{number}"
    for number in range(1, 18)
}
MIGRATED_WORKFLOWS = {
    "design-hypostructure-proof",
    "implement-hypostructure-route",
    "implement-next-hypostructure-erdos-64-eg-ct",
    "review-hypostructure-erdos-64-eg-expansion",
    "repair-hypostructure-manuscript",
    "red-team-hypostructure-manuscript-repair",
}
FRAMEWORK_WORKFLOWS = {
    "understand-hypostructure-framework",
    "implement-hypostructure-proof",
    "implement-hypostructure-graph-proof",
    "implement-hypostructure-pde-proof",
    "extend-hypostructure-framework",
    "review-hypostructure-framework-change",
    "maintain-hypostructure-migration",
}
EXPECTED_SKILLS = {*CT_SKILLS, *MIGRATED_WORKFLOWS, *FRAMEWORK_WORKFLOWS}

REFERENCE_FILES = {
    "implement-next-hypostructure-erdos-64-eg-ct": {
        "mandatory-node-template.md"
    },
    "repair-hypostructure-manuscript": {"repair-worksheet.md"},
    "red-team-hypostructure-manuscript-repair": {"red-team-checklist.md"},
    "implement-hypostructure-proof": {"proof-work-packet.md"},
    "implement-hypostructure-graph-proof": {"graph-proof-work-packet.md"},
    "implement-hypostructure-pde-proof": {"pde-proof-work-packet.md"},
    "extend-hypostructure-framework": {"extension-work-packet.md"},
    "review-hypostructure-framework-change": {
        "framework-review-checklist.md"
    },
}


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
    match = re.search(
        rf'^\s+{re.escape(key)}: "(?P<value>.*)"$',
        content,
        re.MULTILINE,
    )
    assert match is not None
    return match.group("value")


def normalized(name: str) -> str:
    return " ".join(read_skill(name).split())


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
        assert not (directory / "scripts").exists()
        assert not (directory / "assets").exists()

        expected_references = REFERENCE_FILES.get(name)
        references = directory / "references"
        if expected_references is None:
            assert not references.exists()
        else:
            assert references.is_dir()
            assert {
                path.name for path in references.iterdir() if path.is_file()
            } == expected_references

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
        assert "$" + name in default_prompt

    assert total_description_length < 14000


def test_skill_links_resolve() -> None:
    for name in EXPECTED_SKILLS:
        skill = read_skill(name)
        for reference in re.findall(
            r"(?<!/)references/[a-zA-Z0-9_.-]+\.md", skill
        ):
            assert (SKILLS_ROOT / name / reference).is_file()
        for target_path in re.findall(r"\]\(([^)]+)\)", skill):
            if "://" not in target_path and not target_path.startswith("#"):
                assert (SKILLS_ROOT / name / target_path).resolve().is_file()
        for target in re.findall(
            r"\$([a-z0-9]+(?:-[a-z0-9]+)+)(?![A-Za-z0-9-])",
            skill,
        ):
            assert target in EXPECTED_SKILLS


def test_legacy_skill_names_and_production_paths_are_removed() -> None:
    forbidden_names = (
        "design-structural-exhaustion-proof",
        "implement-structural-exhaustion-ct",
        "implement-structural-exhaustion-route",
        "repair-structural-exhaustion-manuscript",
        "red-team-structural-exhaustion-manuscript-repair",
    )
    parity_only = {
        "implement-next-hypostructure-erdos-64-eg-ct",
        "review-hypostructure-erdos-64-eg-expansion",
        "maintain-hypostructure-migration",
    }

    for name in EXPECTED_SKILLS:
        skill = read_skill(name)
        assert not any(forbidden in skill for forbidden in forbidden_names)
        assert "generated/lean-machines.json" not in skill
        if name not in parity_only:
            assert "lean/StructuralExhaustion" not in skill


def test_each_ct_skill_is_live_status_aware() -> None:
    framework_root = ROOT / "hypostructure/Hypostructure"
    for name, tactic_id in CT_SKILLS.items():
        assert (framework_root / tactic_id).is_dir()
        skill = read_skill(name)
        lower = skill.lower()
        for requirement in (
            "migration/hypostructure/api-feature-matrix.csv",
            f"hypostructure/hypostructure/{tactic_id.lower()}",
            "core.residual.query",
            "$extend-hypostructure-framework",
            "terminal",
            "trace",
            "total",
            "work",
            "fixture",
        ):
            assert requirement.lower() in lower
        assert "application" in lower
        assert any(word in lower for word in ("do not", "forbid", "never"))


def test_ct_suite_covers_every_tactic_role() -> None:
    expected_roles = {
        "CT1": "target",
        "CT2": "deletion",
        "CT3": "response",
        "CT4": "charging",
        "CT5": "witness",
        "CT6": "failure",
        "CT7": "context",
        "CT8": "repetition",
        "CT9": "fibre",
        "CT10": "classification",
        "CT11": "negative",
        "CT12": "peeling",
        "CT13": "fallback",
        "CT14": "aggregate",
        "CT15": "rank",
        "CT16": "support",
        "CT17": "compatibility",
    }
    for name, tactic_id in CT_SKILLS.items():
        assert expected_roles[tactic_id] in read_skill(name).lower()


def test_design_and_route_skills_cover_live_framework_contracts() -> None:
    design = read_skill("design-hypostructure-proof")
    for number in range(1, 18):
        assert f"| CT{number} |" in design
    for requirement in (
        "HYPOSTRUCTURE_MIGRATION_GUIDE.md",
        "migration/hypostructure/api-feature-matrix.csv",
        "$understand-hypostructure-framework",
        "$implement-hypostructure-ctN",
        "$extend-hypostructure-framework",
        "Core.Residual",
        "Graph",
        "PDE",
    ):
        assert requirement in design

    route = normalized("implement-hypostructure-route").lower()
    for requirement in (
        "routes.registry",
        "core.routing.profile",
        "core.routing.transition",
        "routes.accumulated",
        "baseline",
        "planned",
        "literal",
        "provenance",
        "semantic discovery",
        "$extend-hypostructure-framework",
    ):
        assert requirement in route


def test_framework_orientation_and_implementation_skills_are_complete() -> None:
    required = {
        "understand-hypostructure-framework": (
            "DOMAIN_INDEPENDENT_CORE.md",
            "GRAPH_LAYER_API.md",
            "PDE_LAYER_API.md",
            "specified",
            "kernel checked",
            "Core.Provision",
            "Routes.Registry",
        ),
        "implement-hypostructure-proof": (
            "Core.Problem",
            "Core.Residual.Ledger.initial",
            "Core.Residual.Query",
            "Core.Routing.Profile",
            "Core.PolynomialCheckBudget",
            "Core.Metadata",
            "#print axioms",
        ),
        "implement-hypostructure-graph-proof": (
            "GRAPH_LAYER_API.md",
            "Graph.FiniteObject",
            "Graph.TargetInterface",
            "SimpleGraph V",
            "Hypostructure.Graph.CTN",
            "#print axioms",
        ),
        "implement-hypostructure-pde-proof": (
            "PDE_LAYER_API.md",
            "pde-row-matrix.csv",
            "PDE.LocalModel",
            "PDE.LocalAtlas",
            "continuum",
            "Hypostructure.PDE.CTN",
            "Navier-Stokes",
        ),
        "extend-hypostructure-framework": (
            "Core.Provision",
            "Core.Metadata",
            "Spec",
            "Capability",
            "Automation",
            "Core.Routing.Profile",
            "decision record",
            "$review-hypostructure-framework-change",
        ),
        "review-hypostructure-framework-change": (
            "parameterization test",
            "Core.Provision",
            "Core.Metadata",
            "Core.Routing.Profile",
            "Routes.Registry.Entry",
            "Core.PolynomialCheckBudget",
            "#print axioms",
            "PASS",
            "FAIL",
        ),
    }
    for name, requirements in required.items():
        skill = read_skill(name)
        for requirement in requirements:
            assert requirement.lower() in skill.lower()


def test_erdos_migration_skills_use_new_packages_and_evidence() -> None:
    for name in (
        "implement-next-hypostructure-erdos-64-eg-ct",
        "review-hypostructure-erdos-64-eg-expansion",
    ):
        skill = normalized(name).lower()
        for requirement in (
            "examples/hypostructure_erdos_64_eg",
            "migration/hypostructure/eg-node-matrix.csv",
            "original_erdos_64_proof.tex",
            "literal",
            "accumulated",
            "parity",
            "framework gap",
            "trust",
        ):
            assert requirement in skill

    contract = (
        SKILLS_ROOT
        / "implement-next-hypostructure-erdos-64-eg-ct"
        / "references/mandatory-node-template.md"
    ).read_text(encoding="utf-8").lower()
    for requirement in (
        "literal predecessor",
        "accumulated ledger",
        "typed quer",
        "author primitive",
        "framework output",
        "every outcome",
        "work",
    ):
        assert requirement in contract


def test_migration_skill_preserves_evidence_separation_and_cutover() -> None:
    skill = normalized("maintain-hypostructure-migration").lower()
    for requirement in (
        "hypostructure_migration_guide.md",
        "api-feature-matrix.csv",
        "eg-node-matrix.csv",
        "pde-row-matrix.csv",
        "baseline",
        "parity",
        "math",
        "work",
        "trust-allowlist.json",
        "decision",
        "dual-run",
        "cutover",
        "update_hypostructure_migration_records.py",
        "check_hypostructure_imports.py",
    ):
        assert requirement in skill


def test_manuscript_repair_skills_retain_total_residual_audit() -> None:
    repair = normalized("repair-hypostructure-manuscript").lower()
    red_team = normalized(
        "red-team-hypostructure-manuscript-repair"
    ).lower()
    for requirement in (
        "exact incoming",
        "residual",
        "both-sides",
        "typed",
        "consumer",
        "termination",
        "$red-team-hypostructure-manuscript-repair",
    ):
        assert requirement in repair
    for requirement in (
        "quantifier",
        "residual",
        "hidden assumption",
        "every outcome",
        "trust",
        "pass",
        "fail",
    ):
        assert requirement in red_team


def test_live_erdos_diagram_preserves_original_topology() -> None:
    def diagram_source(path: Path) -> str:
        source = path.read_text(encoding="utf-8")
        start = source.index(r"\subsection*{Proof-dependency diagram}")
        end = source.index(r"\subsection*{Detailed dependency table}", start)
        return source[start:end]

    def normalized_commands(pattern: str, source: str) -> list[str]:
        return [
            " ".join(command.split())
            for command in re.findall(pattern, source, re.DOTALL)
        ]

    def node_anchors(source: str) -> list[tuple[str, str | None]]:
        nodes = normalized_commands(r"(\\node\b.*?;)", source)
        result: list[tuple[str, str | None]] = []
        for node in nodes:
            anchor = re.search(r"\\node(?:\[[^]]*\])?\s*\(([^)]+)\)", node)
            assert anchor is not None
            node_id = re.search(r"\\textbf\{\[([0-9]+)\]\}", node)
            result.append((anchor.group(1), node_id.group(1) if node_id else None))
        return result

    original = diagram_source(ROOT / "original_erdos_64_proof.tex")
    live = diagram_source(ROOT / "proofs/erdos_64_eg/erdos_64_proof.tex")
    assert node_anchors(live) == node_anchors(original)
    assert normalized_commands(r"(\\draw\b.*?;)", live) == normalized_commands(
        r"(\\draw\b.*?;)", original
    )
