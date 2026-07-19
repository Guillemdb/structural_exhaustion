#!/usr/bin/env python3
"""Render documentation and diagrams from the compiled automation-first catalog."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from collections import defaultdict
from pathlib import Path

try:
    from render_schemas import render_schemas
except ImportError:  # imported as tools.render_artifacts
    from tools.render_schemas import render_schemas


MACHINE_DESCRIPTIONS = {
    "CT1": (
        "CT1 certifies the definitional realization form of the target and then "
        "performs dependent finite search over test indices and their witness "
        "enumerations. A hit produces the C1 certificate; exhaustive absence "
        "produces the target-avoiding state used by the registered CT1-to-CT2 transition."
    ),
    "CT2": (
        "CT2 starts from a discovered proper admissible piece in a shared minimal-"
        "counterexample context. Deletion either closes C2 through the generic "
        "smaller-object theorem or produces the exact critical predecessor for "
        "replacement search. Exhaustive replacement analysis then returns C2, a "
        "separating-context residual, or a criticality residual."
    ),
    "CT3": (
        "CT3 first computes the source piece's exact response vector and searches "
        "the ordered candidate universe for the first admissible smaller piece with "
        "the same response. If compression is absent, the machine validates every "
        "row-context table entry and then performs exact row lookup, yielding a "
        "table defect, a known-row certificate, or a novel-row residual."
    ),
    "CT4": (
        "CT4 computes one canonical first-eligible assignment and stores it in the "
        "assignment predecessor state. Availability consumes that state without "
        "repeating payer search; a complete assignment then determines the payer "
        "fibres. The final stages return a missing-payer or overloaded-fibre "
        "residual, a C4 capacity certificate, or the exact capacity residual."
    ),
    "CT5": (
        "CT5 searches for an active site with no supporting witness. Exhaustive "
        "absence produces the deficit-free predecessor used to compute the local "
        "contribution ledger. The fixed-priority arithmetic comparison returns C4 "
        "when capacity is below the required amount, an aggregate residual when the "
        "computed total exceeds capacity, and otherwise a bounded charge ledger."
    ),
    "CT6": (
        "CT6 performs one ordered first-failure search. A hit records the failing "
        "index, the clean prefix, and its structural failure datum; exhaustive "
        "absence records the no-failure theorem together with the computed active "
        "total. Both branches are semantic residuals with the original branch context."
    ),
    "CT7": (
        "CT7 separates realization from response comparison. The first search either "
        "produces a realizing context for the left object or an exhaustive unrealized "
        "state. Only that state enables the second search, which returns a concrete "
        "response distinction or a neutrality certificate for every declared context."
    ),
    "CT8": (
        "CT8 searches the input sequence for the first ordered pair with repeated "
        "exact type. Absence gives the no-repetition certificate. A repeated pair is "
        "passed to exhaustive response comparison, which returns either a separating "
        "response context or the verified smaller-object removal residual."
    ),
    "CT9": (
        "CT9 records a nullary partition audit boundary and evaluates the exact label-"
        "fibre view from the original input during overload search. Labels are searched "
        "in enumeration order for the first capacity violation. The two terminals "
        "contain either the overload witness or a certificate that every label fibre "
        "is bounded."
    ),
    "CT10": (
        "CT10 records the class-table stage as a nullary audit boundary and searches the "
        "exact class universe for a direct case. Exhaustive direct absence is an explicit "
        "predecessor of the first-empty-row search, which evaluates rows from the original "
        "input. An empty row already contains its canonical promotion; the final promotion "
        "node records the terminal audit edge."
    ),
    "CT11": (
        "CT11 treats the invocation's finite cell collection as predecessor data. "
        "After the decomposition audit edge, it searches for an inadmissible cell. "
        "When every cell is admissible, the negative-total hypothesis and the generic "
        "sum theorem force the second search to return a concrete negative-budget cell."
    ),
    "CT12": (
        "CT12 is the unique cyclic machine. Load zero yields the exhausted certificate; "
        "positive load is peeled and the first declared restoration is selected. A "
        "demand or tier restoration terminates, while a continuation carries its own "
        "strict load decrease and is the only edge permitted to re-enter saturation. "
        "The result also records iteration and trace-length bounds."
    ),
    "CT13": (
        "CT13 first searches for an eligible tier-one payer. Exhaustive absence produces "
        "TierOneAbsenceState; the following node alone computes and proves the canonical "
        "minimum-cost fallback. Reconciliation then detects a duplicated resource or "
        "computes the exact charge, and the final comparison returns a deficit residual "
        "or a reconciliation certificate."
    ),
    "CT14": (
        "CT14 computes the lower mass before scanning members for missing capacities or "
        "labels. A complete MemberScanState retains that exact lower-mass predecessor, "
        "so the upper-capacity and multiplicity ledger carries all data needed by the "
        "final comparison. The comparison yields the aggregate certificate precisely "
        "when upper capacity is below lower mass."
    ),
    "CT15": (
        "CT15 computes target-relative rank from the invocation context and searches for "
        "the first target-dependent coordinate. A hit is the rank-drop residual; "
        "exhaustive absence proves full rank and enables the ordered charge ledger. The "
        "ledger-capacity comparison returns C4 or the reusable full-rank ledger residual."
    ),
    "CT16": (
        "CT16 searches the exact coordinate enumeration for a point outside support. A "
        "missing coordinate gives the proper-support residual. Whole support enables "
        "closed-code computation, after which literal decidable equality with the target "
        "code yields either the exact-code certificate or the mismatch residual."
    ),
    "CT17": (
        "CT17 first checks every target-offset pair for compatibility and then performs "
        "the literal finite-scale split. At finite scale it enumerates the exact survivor "
        "list, returning exhaustion or a nonempty survivor residual. At orbit scale it "
        "searches target-offset arithmetic, returning a target-hit certificate or an "
        "orbit-avoidance residual with the computed value list."
    ),
}


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]


def write_text(path: Path, value: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value, encoding="utf-8")


def write_json(path: Path, value: object) -> None:
    write_text(path, json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def prune_files(directory: Path, expected: set[Path], pattern: str = "*") -> None:
    """Remove files no longer owned by the current compiled catalog.

    Generated directories are projections, not compatibility surfaces.  Pruning at
    generation time prevents renamed tactics or output formats from leaving stale
    files that appear to be part of the current machine contract.
    """
    if not directory.is_dir():
        return
    for path in directory.rglob(pattern):
        if path.is_file() and path not in expected:
            path.unlink()


def tex(value: str) -> str:
    replacements = {
        "\\": r"\textbackslash{}",
        "{": r"\{",
        "}": r"\}",
        "$": r"\$",
        "&": r"\&",
        "#": r"\#",
        "_": r"\_",
        "%": r"\%",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
        "|": r"\textbar{}",
        "→": r"$\to$",
        "∀": r"$\forall$",
        "¬": r"$\neg$",
        "∃": r"$\exists$",
    }
    return "".join(replacements.get(char, char) for char in value)


def tex_code(value: str) -> str:
    """Escape a code-like value and add legal discretionary breakpoints."""
    escaped = tex(value)
    escaped = re.sub(
        r"(?<=[a-z0-9])(?=[A-Z])",
        lambda _match: r"\allowbreak{}",
        escaped,
    )
    escaped = re.sub(
        r"([a-z]{8})(?=[a-z]{5,})",
        lambda match: match.group(1) + r"\allowbreak{}",
        escaped,
    )
    escaped = escaped.replace(".", r".\allowbreak{}")
    escaped = escaped.replace(r"\_", r"\_\allowbreak{}")
    escaped = escaped.replace("@", r"@\allowbreak{}")
    escaped = escaped.replace(r"\textbar{}", r"\textbar{}\allowbreak{}")
    escaped = escaped.replace("-", r"-\allowbreak{}")
    return escaped


def tex_refs(values: list[dict]) -> str:
    if not values:
        return r"$\varnothing$"
    return r"\\".join(
        rf"\texttt{{{tex_code(value['ref'])}}}\\[-0.2ex]"
        rf"{{\tiny {tex_code(value['provision'])}}}"
        for value in values
    )


def table_refs(values: list[dict]) -> str:
    if not values:
        return r"$\varnothing$"
    return r"; \allowbreak ".join(
        rf"\texttt{{{tex_code(value['ref'])}}} "
        rf"{{\scriptsize[{tex_code(value['provision'])}]}}"
        for value in values
    )


def framework_inputs(automation: dict) -> list[dict]:
    return (
        automation["inferredInputs"]
        + automation["derivedInputs"]
        + automation["frameworkTheorems"]
    )


def transition_semantic_discovery(profile: dict) -> dict:
    return profile["authoringBoundary"]["semanticDiscovery"]


def transition_authoring_summary(profile: dict) -> str:
    discovery = transition_semantic_discovery(profile)
    adapter_type = discovery["adapterType"]
    if adapter_type is None:
        return discovery["kind"]
    return f"{discovery['kind']}: {adapter_type}"


def mermaid(tactic: dict, profiles: list[dict]) -> str:
    lines = ["flowchart LR"]
    for node in tactic["nodes"]:
        ordinal = node["ordinal"]
        node_id = node["nodeId"]
        automation = node["automation"]
        label = (
            f"{node_id}<br/>{automation['executionClass']}<br/>"
            f"author={len(automation['authorInputs'])}, "
            f"generated={len(automation['generatedOutputs'])}"
        )
        lines.append(f'  N{ordinal}["{label}"]')
    ordinal = {node["nodeId"]: node["ordinal"] for node in tactic["nodes"]}
    for edge in tactic["transitions"]:
        lines.append(
            f"  N{ordinal[edge['sourceNode']]} -->|{edge['edgeId']}| "
            f"N{ordinal[edge['targetNode']]}"
        )
    for index, profile in enumerate(profiles, start=1):
        lines.append(
            f'  P{index}{{"Transition: {profile["profileId"]}<br/>'
            f'{profile["selectionClass"]}<br/>'
            f'{transition_authoring_summary(profile)}"}}'
        )
    return "\n".join(lines) + "\n"


def transition_label(edge: dict) -> str:
    """Return the stable reader-facing name of a compiled Edge constructor."""

    return edge["constructor"].rsplit(".", 1)[-1]


def cytoscape(tactic: dict, profiles: list[dict]) -> dict:
    elements: list[dict] = []
    for node in tactic["nodes"]:
        elements.append(
            {
                "data": {
                    "id": node["nodeId"],
                    "label": node["nodeId"],
                    "kind": node["nodeKind"],
                    "automation": node["automation"],
                    "formalContract": node["formalContract"],
                }
            }
        )
    for edge in tactic["transitions"]:
        elements.append(
            {
                "data": {
                    "id": edge["edgeId"],
                    "label": transition_label(edge),
                    "kind": "ctTransition",
                    "ordinal": edge["ordinal"],
                    "source": edge["sourceNode"],
                    "target": edge["targetNode"],
                    "constructor": edge["constructor"],
                    "constructorType": edge["constructorType"],
                    "provision": edge["provision"],
                }
            }
        )
    for profile in profiles:
        elements.append(
            {
                "data": {
                    "id": profile["profileId"],
                    "label": profile["profileId"],
                    "kind": "transitionProfile",
                    "transitionProfile": profile,
                }
            }
        )
    return {"tacticId": tactic["tacticId"], "elements": elements}


def node_internals(tactic: dict, source_root: Path) -> dict:
    """Package a CT's Lean-owned low-level flow and inspectable source files.

    The catalog remains the canonical compiled projection.  This per-CT artifact is
    deliberately separate so the web client can load exact declaration dependencies
    and source text only after a reader asks to expand a node.
    """

    lean_root = (source_root / "lean").resolve()
    sources: dict[str, dict] = {}
    declarations: list[dict] = []
    for raw in tactic["internalDeclarations"]:
        declaration = dict(raw)
        project_local = str(raw["name"]).startswith("StructuralExhaustion.")
        declaration["projectLocal"] = project_local
        source_file = declaration.get("sourceFile")
        source_id: str | None = None
        if project_local and isinstance(source_file, str):
            source_path = (lean_root / source_file).resolve()
            if lean_root not in source_path.parents or not source_path.is_file():
                raise ValueError(
                    f"{tactic['tacticId']} declaration {raw['name']} has an unsafe "
                    f"or missing source file: {source_file}"
                )
            source_id = source_file
            if source_id not in sources:
                content = source_path.read_text(encoding="utf-8")
                sources[source_id] = {
                    "sourceId": source_id,
                    "moduleName": declaration.get("module"),
                    "path": f"lean/{source_file}",
                    "sha256": hashlib.sha256(content.encode("utf-8")).hexdigest(),
                    "content": content,
                }
        declaration["sourceId"] = source_id
        declarations.append(declaration)

    return {
        "artifactType": "structuralExhaustionNodeInternals",
        "schemaVersion": "1.0.0",
        "tacticId": tactic["tacticId"],
        "apiVersion": tactic["apiVersion"],
        "nodes": [
            {
                "nodeId": node["nodeId"],
                "internalFlow": node["internalFlow"],
            }
            for node in tactic["nodes"]
        ],
        "declarations": declarations,
        "sources": [sources[source_id] for source_id in sorted(sources)],
    }


def node_style(kind: str) -> str:
    if kind == "entry":
        return "ctentry"
    if kind == "certificate":
        return "ctcertificate"
    if kind == "residual":
        return "ctresidual"
    if kind == "decision":
        return "ctdecision"
    if kind == "loop":
        return "ctloop"
    return "ctnode"


def matching_terminal_for_residual(tactic: dict, residual: dict) -> str | None:
    lean_tail = residual["leanType"].rsplit(".", 1)[-1]
    for terminal in tactic["terminals"]:
        node = next(
            item for item in tactic["nodes"] if item["nodeId"] == terminal["nodeId"]
        )
        incoming_types = " ".join(
            edge["constructorType"] for edge in node["formalContract"]["incomingEdges"]
        )
        if lean_tail in incoming_types:
            return node["nodeId"]
    residual_tail = residual["residualKindId"].rsplit(".", 1)[-1].lower()
    for terminal in tactic["terminals"]:
        if residual_tail in terminal["nodeId"].lower():
            return terminal["nodeId"]
    return None


def tikz_fragment(tactic: dict, transition_profiles: list[dict]) -> str:
    tactic_id = tactic["tacticId"]
    nodes = tactic["nodes"]
    ordinal = {node["nodeId"]: node["ordinal"] for node in nodes}
    lines = [
        rf"\subsection{{{tex(tactic_id)}: {tex(tactic['title'])}}}",
        rf"\label{{sec:{tactic_id.lower()}-automation}}",
        "",
        tex(MACHINE_DESCRIPTIONS[tactic_id]),
        "",
        "A theorem instantiation supplies the problem-specific static entries in the "
        "first table. The framework constructs every remaining node output, exhaustive "
        "decision, certificate, residual, edge, and trace theorem.",
        "",
        r"\paragraph{Public automation surface.}",
        rf"\texttt{{StructuralExhaustion.{tactic_id}.run}} returns the evidence-carrying "
        rf"\texttt{{ExecutionResult}}. \texttt{{{tex_code(tactic_id.lower() + '_execute')}}}, "
        rf"\texttt{{{tex_code(tactic_id.lower())}}}, and "
        rf"\texttt{{{tex_code(tactic_id.lower() + '_total')}}} expose execution, "
        "semantic soundness, and totality, respectively.",
        "",
        r"\paragraph{General problem-specific capability.}",
        r"\begingroup\small",
        r"\begin{longtable}{@{}p{0.27\linewidth}p{0.15\linewidth}p{0.46\linewidth}@{}}",
        r"\toprule",
        r"Reference & Provision & Role \\",
        r"\midrule",
        r"\endhead",
    ]
    capability = tactic["capability"]
    for item in capability["requiredDefinitions"]:
        lines.append(
            rf"\texttt{{{tex_code(item['ref'])}}} & "
            rf"\texttt{{{tex_code(item['provision'])}}} & problem-specific primitive \\"
        )
    lines += [r"\bottomrule", r"\end{longtable}", r"\endgroup", ""]
    if capability["requiredInstances"]:
        indexed = ", ".join(
            rf"\texttt{{{tex_code(item['ref'])}}}"
            for item in capability["requiredInstances"]
        )
        lines += [
            r"\emph{Instance-bridge index.} " + indexed + ". "
            "These references index explicit capability fields already listed above; "
            "they introduce no additional problem-specific inputs.",
            "",
        ]

    capability_profiles = tactic.get("capabilityProfiles", [])
    if capability_profiles:
        lines += [
            r"\paragraph{Generated capability profiles.}",
            "Each profile is a narrower authoring surface for a recurring "
            "structural shape. Its framework constructor fills the omitted "
            "fields of the general capability.",
            r"\begingroup\small",
            r"\begin{longtable}{@{}p{0.25\linewidth}p{0.31\linewidth}p{0.34\linewidth}@{}}",
            r"\toprule",
            r"Profile & Problem-specific inputs & Framework-generated operations \\",
            r"\midrule",
            r"\endhead",
        ]
        for profile in capability_profiles:
            lines.append(
                rf"\texttt{{{tex_code(profile['capabilityId'])}}} & "
                rf"{table_refs(profile['requiredDefinitions'])} & "
                rf"{table_refs(profile['derivedOperations'])} \\"
            )
        lines += [r"\bottomrule", r"\end{longtable}", r"\endgroup", ""]

    lines += [
        r"\paragraph{Per-node dependency and output contracts.}",
        "The execution class appears beneath each node identifier. The displayed "
        "categories are exact catalog projections; every manual-obligation list is empty.",
        r"\begingroup\scriptsize\sloppy",
        r"\begin{longtable}{@{}p{0.13\linewidth}p{0.17\linewidth}p{0.17\linewidth}p{0.18\linewidth}p{0.18\linewidth}@{}}",
        r"\toprule",
        r"Node & Problem-specific static inputs & Predecessor and inferred inputs & Framework-derived & Generated outputs \\",
        r"\midrule",
        r"\endhead",
    ]
    for node in nodes:
        automation = node["automation"]
        predecessor = automation["predecessorInputs"] + automation["inferredInputs"]
        lines.append(
            rf"\texttt{{{tex_code(node['nodeId'])}}}\\"
            rf"{{\scriptsize {tex_code(automation['executionClass'])}}} & "
            rf"{table_refs(automation['authorInputs'])} & "
            rf"{table_refs(predecessor)} & "
            rf"{table_refs(automation['derivedInputs'] + automation['frameworkTheorems'])} & "
            rf"{table_refs(automation['generatedOutputs'])} \\"
        )
    lines += [r"\bottomrule", r"\end{longtable}", r"\endgroup", ""]

    lines += [
        r"\begin{landscape}",
        r"\begin{figure}[p]",
        r"\centering",
        r"\begin{adjustbox}{max totalsize={\linewidth}{0.72\textheight},center}",
        r"\begin{tikzpicture}[x=1cm,y=1cm]",
    ]
    terminal_ids = {terminal["nodeId"] for terminal in tactic["terminals"]}
    executable_nodes = [node for node in nodes if node["nodeId"] not in terminal_ids]
    y_positions: dict[str, float] = {}
    cursor = 0.0
    for node in executable_nodes:
        automation = node["automation"]
        largest_contract = max(
            len(automation["authorInputs"]),
            len(automation["predecessorInputs"]),
            len(framework_inputs(automation)),
            len(automation["generatedOutputs"]),
        )
        y_positions[node["nodeId"]] = -cursor
        cursor += max(3.05, 1.55 + 0.55 * largest_contract)

    for node in executable_nodes:
        index = node["ordinal"]
        y = y_positions[node["nodeId"]]
        automation = node["automation"]
        predecessor = automation["predecessorInputs"]
        derived = framework_inputs(automation)
        outputs = tex_refs(automation["generatedOutputs"])
        lines += [
            rf"\node[ctauthor] (a{index}) at (0,{y:.2f}) "
            rf"{{\textbf{{Problem-specific static inputs}}\\{tex_refs(automation['authorInputs'])}}};",
            rf"\node[ctpred] (p{index}) at (5.6,{y:.2f}) "
            rf"{{\textbf{{Predecessor-derived}}\\{tex_refs(predecessor)}}};",
            rf"\node[ctderived] (d{index}) at (11.2,{y:.2f}) "
            rf"{{\textbf{{Framework-derived}}\\{tex_refs(derived)}}};",
            rf"\node[{node_style(node['nodeKind'])}] (n{index}) at (17.1,{y:.2f}) "
            rf"{{\textbf{{{tex_code(node['nodeId'])}}}\\"
            rf"{{\scriptsize {tex_code(automation['executionClass'])}}}\\[-0.2ex]"
            rf"{{\tiny Outputs: {outputs}}}}};",
            rf"\draw[ctinputarrow] (a{index}.south) |- ([yshift=-5pt]n{index}.west);",
            rf"\draw[ctpredarrow] (p{index}.south) |- (n{index}.west);",
            rf"\draw[ctderivedarrow] (d{index}.south) |- ([yshift=5pt]n{index}.west);",
        ]

    terminal_by_source: dict[str, list[dict]] = defaultdict(list)
    for terminal in tactic["terminals"]:
        node = next(item for item in nodes if item["nodeId"] == terminal["nodeId"])
        incoming = node["formalContract"]["incomingEdges"]
        source = incoming[0]["sourceNode"] if incoming else executable_nodes[-1]["nodeId"]
        terminal_by_source[source].append(node)
    for source, source_terminals in terminal_by_source.items():
        base_y = y_positions[source]
        for position, node in enumerate(source_terminals):
            index = node["ordinal"]
            offset = (position - (len(source_terminals) - 1) / 2) * 1.65
            y = base_y - offset
            y_positions[node["nodeId"]] = y
            lines.append(
                rf"\node[{node_style(node['nodeKind'])}] (n{index}) at (23.4,{y:.2f}) "
                rf"{{\textbf{{{tex_code(node['nodeId'])}}}\\"
                rf"{{\tiny terminal; evidence fixed by the incoming edge}}}};"
            )

    for edge in tactic["transitions"]:
        source = ordinal[edge["sourceNode"]]
        target = ordinal[edge["targetNode"]]
        if edge["targetNode"] in terminal_ids:
            lines.append(
                rf"\draw[ctedge] (n{source}.east) to[bend left=10] "
                rf"node[ctedgelabel] {{{tex_code(edge['edgeId'].rsplit('.', 1)[-1])}}} "
                rf"(n{target}.west);"
            )
        elif y_positions[edge["targetNode"]] < y_positions[edge["sourceNode"]]:
            lines.append(
                rf"\draw[ctedge] (n{source}.south east) to[bend left=15] "
                rf"node[ctedgelabel] {{{tex_code(edge['edgeId'].rsplit('.', 1)[-1])}}} "
                rf"(n{target}.north east);"
            )
        else:
            lines.append(
                rf"\draw[ctloopedge] (n{source}.east) "
                rf"to[bend right=50] node[ctedgelabel] "
                rf"{{{tex_code(edge['edgeId'].rsplit('.', 1)[-1])}}} (n{target}.east);"
            )

    transition_y = -cursor - 0.5
    residual_by_id = {
        residual["residualKindId"]: residual for residual in tactic["residualKinds"]
    }
    for index, profile in enumerate(transition_profiles, start=1):
        x = 3.3 + (index - 1) * 7.0
        discovery = transition_semantic_discovery(profile)
        transition_label = (
            r"\textbf{CT transition}\\"
            + r"\texttt{" + tex_code(profile["profileId"]) + r"}\\"
            + r"{\tiny " + tex_code(profile["selectionClass"])
            + "; " + tex_code(discovery["kind"]) + "}"
        )
        if discovery["adapterType"] is not None:
            transition_label += (
                r"\\{\tiny adapter: \texttt{"
                + tex_code(discovery["adapterType"])
                + "}}"
            )
        lines.append(
            rf"\node[ctroute] (p{index}) at ({x:.2f},{transition_y:.2f}) "
            rf"{{{transition_label}}};"
        )
        residual = residual_by_id.get(profile["sourceResidualKind"])
        if residual:
            terminal_id = matching_terminal_for_residual(tactic, residual)
            if terminal_id:
                lines.append(
                    rf"\draw[ctroutearrow] (n{ordinal[terminal_id]}.south)--(p{index}.north);"
                )

    lines += [
        r"\end{tikzpicture}%",
        r"\end{adjustbox}",
        rf"\caption{{Automation-first sequential machine for {tex(tactic_id)}. "
        "Each executable node has separate problem-specific static, predecessor, and "
        "framework-derived dependency boxes. Terminal nodes consume only incoming "
        "edge evidence. Transition boxes are executable framework profiles.}",
        rf"\label{{fig:{tactic_id.lower()}-machine}}",
        r"\end{figure}",
        r"\end{landscape}",
        "",
        r"\begingroup\small\sloppy",
        r"\paragraph{Residual contracts.}",
    ]
    if tactic["residualKinds"]:
        lines += [
            r"\begin{itemize}",
            *[
                rf"\item \texttt{{{tex_code(residual['residualKindId'])}}}: "
                rf"\texttt{{{tex_code(residual['leanType'])}}}; inherited context "
                rf"\texttt{{{tex_code(residual['inheritedContext'])}}}."
                for residual in tactic["residualKinds"]
            ],
            r"\end{itemize}",
        ]
    else:
        lines.append("This tactic has no transition-visible semantic residual.")
    if transition_profiles:
        lines += [
            r"\paragraph{Registered transition profiles.}",
            r"\begin{itemize}",
            *[
                rf"\item \texttt{{{tex_code(profile['profileId'])}}}: "
                rf"\texttt{{{tex_code(profile['sourceResidualKind'])}}} $\to$ "
                rf"\texttt{{{tex_code(profile['targetTacticId'])}}}; executor "
                rf"\texttt{{{tex_code(profile['advanceExecutor'])}}}; authoring mode "
                rf"\texttt{{{tex_code(transition_semantic_discovery(profile)['kind'])}}}"
                + (
                    rf" with adapter \texttt{{{tex_code(transition_semantic_discovery(profile)['adapterType'])}}}."
                    if transition_semantic_discovery(profile)["adapterType"] is not None
                    else "."
                )
                for profile in transition_profiles
            ],
            r"\end{itemize}",
        ]
    lines += [r"\endgroup", ""]
    return "\n".join(lines)


def machine_inventory(catalog: dict) -> str:
    lines = [
        "# Automation-first Lean CT inventory",
        "",
        "Generated from the compiled `StructuralExhaustion.Canonical` registry.",
        "",
        "| Tactic | Nodes | Edges | Terminals | Author definitions | Derived operations | Residuals |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for tactic in catalog["tactics"]:
        lines.append(
            f"| {tactic['tacticId']} | {len(tactic['nodes'])} | "
            f"{len(tactic['transitions'])} | {len(tactic['terminals'])} | "
            f"{len(tactic['capability']['requiredDefinitions'])} | "
            f"{len(tactic['capability']['derivedOperations'])} | "
            f"{len(tactic['residualKinds'])} |"
        )
    lines += ["", "## Per-node automation contracts", ""]
    for tactic in catalog["tactics"]:
        lines += [f"### {tactic['tacticId']}", ""]
        for node in tactic["nodes"]:
            auto = node["automation"]
            lines.append(
                f"- `{node['nodeId']}` — `{auto['executionClass']}`; "
                f"author {len(auto['authorInputs'])}, predecessor "
                f"{len(auto['predecessorInputs'])}, framework "
                f"{len(auto['derivedInputs']) + len(auto['frameworkTheorems'])}, "
                f"outputs {len(auto['generatedOutputs'])}, manual obligations "
                f"{len(auto['manualObligations'])}."
            )
        lines.append("")
    lines += [
        "## Transition-profile authoring boundaries",
        "",
        "| Profile | Family | Semantic discovery | Problem-specific inputs | Adapter type |",
        "|---|---|---|---|---|",
    ]
    for profile in catalog["transitionProfiles"]:
        discovery = transition_semantic_discovery(profile)
        adapter_type = discovery["adapterType"] or "—"
        problem_inputs = ", ".join(
            profile["authoringBoundary"]["problemSpecificInputs"]
        )
        lines.append(
            f"| `{profile['profileId']}` | `{profile['familyId']}` | "
            f"`{discovery['kind']}` | {problem_inputs} | `{adapter_type}` |"
        )
    lines.append("")
    return "\n".join(lines)


def binding_check(catalog: dict) -> str:
    declarations: list[str] = []
    for tactic in catalog["tactics"]:
        declarations.extend(item["name"] for item in tactic["apiDeclarations"])
        declarations.extend(edge["constructor"] for edge in tactic["transitions"])
        declarations.extend(terminal["constructor"] for terminal in tactic["terminals"])
        for profile in tactic.get("capabilityProfiles", []):
            declarations.extend(
                item["ref"]
                for key in ("requiredDefinitions", "derivedOperations")
                for item in profile[key]
            )
    for profile in catalog["transitionProfiles"]:
        declarations.extend(
            profile[field]
            for field in (
                "targetExecutableInterface",
                "transitionConstructor",
                "advanceExecutor",
            )
        )
        adapter_type = transition_semantic_discovery(profile)["adapterType"]
        if adapter_type is not None:
            declarations.append(adapter_type)
    unique = list(dict.fromkeys(declarations))
    return (
        "import StructuralExhaustion\n\n"
        "/-! Generated declaration binding check. -/\n\n"
        + "\n".join(f"#check {name}" for name in unique)
        + "\n"
    )


def catalog_status_tex(catalog: dict) -> str:
    tactics = catalog["tactics"]
    counts = {
        "tactics": len(tactics),
        "nodes": sum(len(tactic["nodes"]) for tactic in tactics),
        "transitions": sum(len(tactic["transitions"]) for tactic in tactics),
        "terminals": sum(len(tactic["terminals"]) for tactic in tactics),
        "residuals": sum(len(tactic["residualKinds"]) for tactic in tactics),
        "transition_families": len(catalog["transitionFamilies"]),
        "transition_profiles": len(catalog["transitionProfiles"]),
        "capability_profiles": sum(
            transition_semantic_discovery(profile)["kind"]
            == "capabilityDiscovery"
            for profile in catalog["transitionProfiles"]
        ),
        "adapter_profiles": sum(
            transition_semantic_discovery(profile)["kind"]
            == "problemSemanticAdapter"
            for profile in catalog["transitionProfiles"]
        ),
        "manual": sum(
            len(node["automation"]["manualObligations"])
            for tactic in tactics
            for node in tactic["nodes"]
        ),
    }
    return "\n".join(
        [
            "% Generated from the compiled Lean catalog; do not edit by hand.",
            rf"\newcommand{{\CatalogTacticCount}}{{{counts['tactics']}}}",
            rf"\newcommand{{\CatalogNodeCount}}{{{counts['nodes']}}}",
            rf"\newcommand{{\CatalogTransitionCount}}{{{counts['transitions']}}}",
            rf"\newcommand{{\CatalogTerminalCount}}{{{counts['terminals']}}}",
            rf"\newcommand{{\CatalogResidualCount}}{{{counts['residuals']}}}",
            rf"\newcommand{{\CatalogTransitionFamilyCount}}{{{counts['transition_families']}}}",
            rf"\newcommand{{\CatalogTransitionProfileCount}}{{{counts['transition_profiles']}}}",
            rf"\newcommand{{\CatalogCapabilityDiscoveryTransitionProfileCount}}{{{counts['capability_profiles']}}}",
            rf"\newcommand{{\CatalogProblemSemanticAdapterTransitionProfileCount}}{{{counts['adapter_profiles']}}}",
            rf"\newcommand{{\CatalogManualObligationCount}}{{{counts['manual']}}}",
            r"\paragraph{Compiled catalog status.}",
            r"The compiled Lean registry contains \CatalogTacticCount{} tactics, "
            r"\CatalogNodeCount{} nodes, \CatalogTransitionCount{} typed transitions, "
            r"\CatalogTerminalCount{} terminals, \CatalogResidualCount{} semantic "
            r"residual kinds, \CatalogTransitionFamilyCount{} transition families, "
            r"and \CatalogTransitionProfileCount{} executable profiles. The total "
            r"number of manual node obligations is \CatalogManualObligationCount{}. "
            r"Among the profiles, \CatalogCapabilityDiscoveryTransitionProfileCount{} "
            r"use target-capability discovery and "
            r"\CatalogProblemSemanticAdapterTransitionProfileCount{} use "
            r"a problem-semantic adapter.",
            "",
        ]
    )


def render(
    root: Path,
    catalog: dict,
    *,
    generated_only: bool = False,
    source_root: Path | None = None,
) -> dict:
    source_root = (source_root or REPOSITORY_ROOT).resolve()
    profiles_by_source: dict[str, list[dict]] = defaultdict(list)
    for profile in catalog["transitionProfiles"]:
        profiles_by_source[profile["sourceTacticId"]].append(profile)

    manifest_tactics: list[dict] = []
    node_rows: list[list[object]] = []
    expected_mermaid: set[Path] = set()
    expected_cytoscape: set[Path] = set()
    expected_internals: set[Path] = set()
    expected_tex: set[Path] = set()
    for tactic in catalog["tactics"]:
        tactic_id = tactic["tacticId"]
        profiles = profiles_by_source[tactic_id]
        mermaid_path = Path(f"generated/mermaid/{tactic_id}.mmd")
        cytoscape_path = Path(f"generated/cytoscape/{tactic_id}.json")
        internals_path = Path(f"generated/internals/{tactic_id}.json")
        tex_path = Path(f"framework/generated/ct/{tactic_id}.tex")
        write_text(root / mermaid_path, mermaid(tactic, profiles))
        write_json(root / cytoscape_path, cytoscape(tactic, profiles))
        write_json(root / internals_path, node_internals(tactic, source_root))
        if not generated_only:
            write_text(root / tex_path, tikz_fragment(tactic, profiles))
        expected_mermaid.add(root / mermaid_path)
        expected_cytoscape.add(root / cytoscape_path)
        expected_internals.add(root / internals_path)
        if not generated_only:
            expected_tex.add(root / tex_path)
        manifest_tactics.append(
            {
                "tacticId": tactic_id,
                "apiVersion": tactic["apiVersion"],
                "mermaid": mermaid_path.as_posix(),
                "cytoscape": cytoscape_path.as_posix(),
                "internals": internals_path.as_posix(),
                "manuscriptFigure": tex_path.as_posix(),
            }
        )
        for node in tactic["nodes"]:
            auto = node["automation"]
            node_rows.append(
                [
                    tactic_id,
                    node["ordinal"],
                    node["nodeId"],
                    node["nodeKind"],
                    auto["executionClass"],
                    len(auto["authorInputs"]),
                    len(auto["predecessorInputs"]),
                    len(auto["derivedInputs"]) + len(auto["frameworkTheorems"]),
                    len(auto["generatedOutputs"]),
                    len(auto["manualObligations"]),
                ]
            )

    prune_files(root / "generated/mermaid", expected_mermaid)
    prune_files(root / "generated/cytoscape", expected_cytoscape)
    prune_files(root / "generated/internals", expected_internals)
    if not generated_only:
        prune_files(root / "framework/generated/ct", expected_tex)

    # This was the pre-catalog diagram layout.  Nothing consumes it and retaining
    # it would create a second, stale representation of the machine graphs.
    prune_files(root / "generated/graphs", set())

    catalog_status_path = Path("framework/generated/catalog-status.tex")
    if not generated_only:
        write_text(root / catalog_status_path, catalog_status_tex(catalog))

    manifest = {
        "artifactType": "automationFirstDerivedManifest",
        "schemaVersion": "3.0.0",
        "canonicalSource": "lean/StructuralExhaustion",
        "catalog": "generated/lean-machines.json",
        "catalogStatus": catalog_status_path.as_posix(),
        "tactics": manifest_tactics,
        "transitionFamilies": catalog["transitionFamilies"],
        "transitionProfiles": catalog["transitionProfiles"],
    }
    write_json(root / "generated/manifest.json", manifest)
    write_json(root / "generated/transition-manifest.json", {
        "artifactType": "generatedTransitionManifest",
        "schemaVersion": "1.0.0",
        "transitionFamilies": catalog["transitionFamilies"],
        "transitionProfiles": catalog["transitionProfiles"],
    })
    write_json(root / "generated/automation-summary.json", {
        "artifactType": "automationSummary",
        "schemaVersion": "1.0.0",
        "tactics": [
            {
                "tacticId": tactic["tacticId"],
                "authorDefinitions": len(tactic["capability"]["requiredDefinitions"]),
                "inferredInstances": len(tactic["capability"]["requiredInstances"]),
                "derivedOperations": len(tactic["capability"]["derivedOperations"]),
                "capabilityProfiles": [
                    profile["capabilityId"]
                    for profile in tactic.get("capabilityProfiles", [])
                ],
                "manualObligations": sum(
                    len(node["automation"]["manualObligations"])
                    for node in tactic["nodes"]
                ),
            }
            for tactic in catalog["tactics"]
        ],
    })

    csv_path = root / "generated/node-index.csv"
    csv_path.parent.mkdir(parents=True, exist_ok=True)
    with csv_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(
            [
                "tactic_id",
                "ordinal",
                "node_id",
                "node_kind",
                "execution_class",
                "author_inputs",
                "predecessor_inputs",
                "framework_dependencies",
                "generated_outputs",
                "manual_obligations",
            ]
        )
        writer.writerows(node_rows)

    if not generated_only:
        write_text(root / "docs/ct-machines.md", machine_inventory(catalog))
        write_text(
            root / "lean/StructuralExhaustion/Generated/BindingCheck.lean",
            binding_check(catalog),
        )
        render_schemas(root, catalog)
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--catalog", type=Path, default=Path("generated/lean-machines.json")
    )
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument(
        "--generated-only",
        action="store_true",
        help="refresh only files below generated/; leave documentation and Lean untouched",
    )
    args = parser.parse_args()
    catalog = json.loads(args.catalog.read_text(encoding="utf-8"))
    manifest = render(
        args.root.resolve(), catalog, generated_only=args.generated_only
    )
    print(
        f"Rendered {len(manifest['tactics'])} tactic projections and "
        f"{len(manifest['transitionFamilies'])} transition families and "
        f"{len(manifest['transitionProfiles'])} transition profiles"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
