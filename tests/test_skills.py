from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SKILLS_ROOT = ROOT / ".agents/skills"

STRATEGY_PATTERNS = {
    "implement-ordered-exhaustion-strategy",
    "implement-response-classification-strategy",
    "implement-capacity-accounting-strategy",
    "implement-support-localization-strategy",
    "implement-target-avoidance-strategy",
    "implement-rank-budget-strategy",
    "implement-closed-code-strategy",
}

PROOF_WORKFLOWS = {
    "understand-hypostructure-framework",
    "design-hypostructure-proof",
    "compose-hypostructure-strategies",
    "implement-hypostructure-proof",
    "run-hypostructure-proof",
    "implement-hypostructure-graph-proof",
    "implement-hypostructure-pde-proof",
    "implement-hypostructure-erdos-strategy",
    "review-hypostructure-erdos-strategy",
}

MAINTENANCE_WORKFLOWS = {
    "extend-hypostructure-framework",
    "review-hypostructure-framework-change",
    "maintain-hypostructure-migration",
    "repair-hypostructure-manuscript",
    "red-team-hypostructure-manuscript-repair",
}

EXPECTED_SKILLS = STRATEGY_PATTERNS | PROOF_WORKFLOWS | MAINTENANCE_WORKFLOWS

BACKEND_REFERENCES = {
    "backend-ordered-exhaustion.md",
    "backend-response-classification.md",
    "backend-capacity-accounting.md",
    "backend-support-localization.md",
    "backend-target-avoidance.md",
    "backend-rank-budget.md",
    "backend-closed-code.md",
    "backend-routing.md",
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


def test_strategy_skill_inventory_and_metadata_are_complete() -> None:
    skill_directories = {
        path.name
        for path in SKILLS_ROOT.iterdir()
        if path.is_dir() and (path / "SKILL.md").is_file()
    }
    assert skill_directories == EXPECTED_SKILLS

    for name in sorted(EXPECTED_SKILLS):
        directory = SKILLS_ROOT / name
        skill = read_skill(name)
        metadata = frontmatter(skill)
        assert metadata.keys() == {"name", "description"}
        assert metadata["name"] == name
        assert 1 <= len(metadata["description"]) <= 1024
        assert len(skill.splitlines()) < 500
        assert not any(marker in skill for marker in ("[TODO", "FIXME", "TBD"))

        ui = (directory / "agents/openai.yaml").read_text(encoding="utf-8")
        assert ui.startswith("interface:\n")
        assert set(re.findall(r"^\s{2}([a-z_]+):", ui, re.MULTILINE)) == {
            "display_name",
            "short_description",
            "default_prompt",
        }
        assert 25 <= len(quoted_yaml_value(ui, "short_description")) <= 64
        assert "$" + name in quoted_yaml_value(ui, "default_prompt")


def test_backend_playbooks_are_private_to_framework_extension() -> None:
    references = SKILLS_ROOT / "extend-hypostructure-framework/references"
    assert {path.name for path in references.iterdir() if path.is_file()} == (
        BACKEND_REFERENCES
    )

    extension = read_skill("extend-hypostructure-framework")
    for reference in BACKEND_REFERENCES:
        assert f"references/{reference}" in extension

    assert not any(
        (SKILLS_ROOT / f"implement-hypostructure-ct{number}/SKILL.md").exists()
        for number in range(1, 18)
    )
    assert not (SKILLS_ROOT / "implement-hypostructure-route/SKILL.md").exists()


def test_public_skills_are_strategy_first() -> None:
    forbidden = re.compile(r"\bCT(?:[1-9]|1[0-7])\b")
    old_names = (
        "implement-next-hypostructure-erdos-64-eg-ct",
        "review-hypostructure-erdos-64-eg-expansion",
        "implement-hypostructure-route",
    )

    for name in EXPECTED_SKILLS:
        skill = read_skill(name)
        assert forbidden.search(skill) is None
        assert not any(old_name in skill for old_name in old_names)
        assert "strategy" in skill.lower()

    for name in STRATEGY_PATTERNS:
        skill = normalized(name).lower()
        for phrase in (
            "previous residual",
            "ledger",
            "exhaustive",
            "extend-hypostructure-framework",
        ):
            assert phrase in skill


def test_problem_definition_is_the_canonical_entry_point() -> None:
    for name in {
        "design-hypostructure-proof",
        "implement-hypostructure-proof",
        "run-hypostructure-proof",
        "implement-hypostructure-erdos-strategy",
    }:
        assert "problemDefinition" in read_skill(name)

    implementation = normalized("implement-hypostructure-proof")
    for phrase in (
        "Core.ProblemDefinition",
        "Core.Strategy.Dag.Blueprint",
        "Core.Strategy.Dag.ProblemDeclaration",
        "ProblemDeclaration.ofDag",
        "problemDefinition.result",
        "problemDefinition.report",
    ):
        assert phrase in implementation

    runner = normalized("run-hypostructure-proof").lower()
    assert "compilation alone is not evidence" in runner
    assert "exact dependent residual" in runner
    assert "never guess" in runner


def test_composition_skill_enforces_framework_owned_routing() -> None:
    skill = normalized("compose-hypostructure-strategies").lower()
    for phrase in (
        "literal residual",
        "dependent composition",
        "exhaustive branch",
        "branch witness",
        "typed residual",
        "dag.blueprint",
        "problemdeclaration.ofdag",
        "sum.inl",
        "sum.inr",
    ):
        assert phrase in skill


def test_erdos_skills_are_node_free_and_paper_preserving() -> None:
    implementation = normalized("implement-hypostructure-erdos-strategy").lower()
    review = normalized("review-hypostructure-erdos-strategy").lower()
    for phrase in (
        "original paper",
        "frozen structural-exhaustion proof",
        "eg_chapter1_strategy_translation_plan.md",
        "literal residual",
        "accumulated ledger",
        "no placeholder outcome",
    ):
        assert phrase in implementation
    assert "import no manuscript `nodex`" in implementation
    assert "node imports" in review
    assert "problemdefinition.report" in review


def test_skill_links_resolve() -> None:
    for name in EXPECTED_SKILLS:
        skill = read_skill(name)
        for reference in re.findall(
            r"(?<!/)references/[a-zA-Z0-9_.-]+\.md", skill
        ):
            assert (SKILLS_ROOT / name / reference).is_file()
        for target in re.findall(
            r"\$([a-z0-9]+(?:-[a-z0-9]+)+)(?![A-Za-z0-9-])", skill
        ):
            assert target in EXPECTED_SKILLS


def test_core_and_template_expose_declaration_runner() -> None:
    core = (
        ROOT / "hypostructure/Hypostructure/Core/Strategy/Dag.lean"
    ).read_text(encoding="utf-8")
    for declaration in (
        "structure ProblemDeclaration",
        "def ProblemDeclaration.run",
        "def ProblemDeclaration.diagnose",
        "theorem ProblemDeclaration.result",
        "def ProblemDeclaration.report",
        "theorem ProblemDeclaration.unconditional",
    ):
        assert declaration in core

    template = (
        ROOT / "examples/template/Template/Application.lean"
    ).read_text(encoding="utf-8")
    assert "def problemDefinition : Core.Strategy.Dag.ProblemDeclaration" in template
    assert "ProblemDeclaration.ofDag problem dag" in template
    assert "def application" not in template.lower()


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
