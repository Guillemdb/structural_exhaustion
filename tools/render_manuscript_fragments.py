#!/usr/bin/env python3
"""Render label-addressed LaTeX manuscript fragments for the web companion.

The Lean example descriptor owns which labels matter.  This module only reads
those labels from the trusted manuscript, converts their Pandoc AST into a
small JSON-safe vocabulary, and compiles figures that occur inside a selected
fragment.  Unsupported content is an error: the renderer must never silently
drop part of the mathematical argument.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any


SUPPORTED_PANDOC_API = [1, 23, 1]
LABEL_PATTERN = re.compile(r"\\label(?:\[[^\]]+\])?\{([^}]+)\}")
OPTIONAL_LABEL_PATTERN = re.compile(r"\\label(?:\[[^\]]+\])?\{")
FIGURE_BEGIN_PATTERN = re.compile(r"\\begin\{figure\}(?:\[[^\]]*\])?")
FIGURE_END = r"\end{figure}"
REFERENCE_MARKER_PATTERN = re.compile(r"\\(Cref|ref|eqref)\{([^}]+)\}")
ENVIRONMENT_LABEL_PATTERN = re.compile(
    r"\\begin\{(?P<environment>[A-Za-z*]+)\}"
    r"(?:\[(?P<title>[^\]]*)\])?\s*"
    r"\\label(?:\[[^\]]+\])?\{(?P<label>[^}]+)\}"
)
REFERENCE_TITLES = {
    "theorem": "Theorem",
    "lemma": "Lemma",
    "proposition": "Proposition",
    "corollary": "Corollary",
    "claim": "Claim",
    "definition": "Definition",
    "remark": "Remark",
    "section": "Section",
    "figure": "Figure",
    "table": "Table",
    "equation": "Equation",
}
REFERENCE_PLURALS = {
    "theorem": "Theorems",
    "lemma": "Lemmas",
    "proposition": "Propositions",
    "corollary": "Corollaries",
    "claim": "Claims",
    "definition": "Definitions",
    "remark": "Remarks",
    "section": "Sections",
    "figure": "Figures",
    "table": "Tables",
    "equation": "Equations",
}
MATHEMATICAL_OBJECT_KINDS = {
    "theorem",
    "lemma",
    "proposition",
    "corollary",
    "claim",
    "definition",
    "remark",
}
SVG_ALLOWED_ELEMENTS = {
    "svg",
    "defs",
    "font",
    "font-face",
    "font-face-src",
    "font-face-name",
    "glyph",
    "missing-glyph",
    "g",
    "path",
    "style",
    "text",
    "tspan",
    "use",
    "clipPath",
    "rect",
    "circle",
    "ellipse",
    "line",
    "polyline",
    "polygon",
}


class ManuscriptRenderError(ValueError):
    """The manuscript cannot be projected faithfully into the web artifact."""


def _canonical_hash(value: object) -> str:
    payload = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _unique(values: list[str], label: str) -> None:
    seen: set[str] = set()
    repeated: list[str] = []
    for value in values:
        if value in seen and value not in repeated:
            repeated.append(value)
        seen.add(value)
    if repeated:
        raise ManuscriptRenderError(f"duplicate {label}: {repeated}")


def _trusted_manuscript(path: str, source_root: Path) -> tuple[Path, str, bytes]:
    relative = Path(path)
    if relative.is_absolute() or ".." in relative.parts or relative.suffix != ".tex":
        raise ManuscriptRenderError(
            "manuscript path must be a safe repository-relative .tex file: "
            f"{path}"
        )
    root = source_root.resolve()
    try:
        manuscript_path = (root / relative).resolve(strict=True)
        manuscript_path.relative_to(root)
    except (OSError, ValueError) as error:
        raise ManuscriptRenderError(
            f"manuscript is unavailable or escapes the repository: {path}"
        ) from error
    try:
        source_bytes = manuscript_path.read_bytes()
        source = source_bytes.decode("utf-8")
    except (OSError, UnicodeDecodeError) as error:
        raise ManuscriptRenderError(f"cannot read manuscript {path}: {error}") from error
    return manuscript_path, source, source_bytes


def _run_pandoc(source: str, manuscript_path: Path) -> dict[str, Any]:
    executable = shutil.which("pandoc")
    if executable is None:
        raise ManuscriptRenderError(
            "pandoc is required to render manuscript fragments (expected API 1.23.1)"
        )
    normalized = OPTIONAL_LABEL_PATTERN.sub(r"\\label{", source)
    marker_wrappers = {
        "Cref": "underline",
        "ref": "textbf",
        "eqref": "emph",
    }
    normalized = REFERENCE_MARKER_PATTERN.sub(
        lambda match: (
            "\\textsc{\\"
            + marker_wrappers[match.group(1)]
            + "{\\cref{"
            + match.group(2)
            + "}}}"
        ),
        normalized,
    )
    try:
        process = subprocess.run(
            [executable, "--from=latex", "--to=json"],
            cwd=manuscript_path.parent,
            input=normalized,
            text=True,
            capture_output=True,
            check=False,
        )
    except OSError as error:
        raise ManuscriptRenderError(f"cannot execute pandoc: {error}") from error
    if process.returncode != 0:
        message = process.stderr.strip() or process.stdout.strip()
        raise ManuscriptRenderError(f"pandoc could not parse {manuscript_path}: {message}")
    try:
        document = json.loads(process.stdout)
    except json.JSONDecodeError as error:
        raise ManuscriptRenderError("pandoc returned malformed JSON") from error
    if not isinstance(document, dict) or not isinstance(document.get("blocks"), list):
        raise ManuscriptRenderError("pandoc returned a malformed document")
    if document.get("pandoc-api-version") != SUPPORTED_PANDOC_API:
        raise ManuscriptRenderError(
            "unsupported pandoc AST API; expected "
            f"{SUPPORTED_PANDOC_API}, observed {document.get('pandoc-api-version')}"
        )
    return document


def _annotate_reference_commands(
    document: dict[str, Any], raw_labels: list[str]
) -> None:
    r"""Restore commands hidden in structural wrappers added before Pandoc."""

    wrapper_commands = {
        "Underline": "Cref",
        "Strong": "ref",
        "Emph": "eqref",
    }

    def restore(value: object) -> object:
        if isinstance(value, list):
            return [restore(item) for item in value]
        if not isinstance(value, dict):
            return value
        children = value.get("c")
        if value.get("t") == "SmallCaps" and isinstance(children, list) and len(children) == 1:
            wrapper = children[0]
            if isinstance(wrapper, dict) and wrapper.get("t") in wrapper_commands:
                wrapped = wrapper.get("c")
                if (
                    isinstance(wrapped, list)
                    and len(wrapped) == 1
                    and isinstance(wrapped[0], dict)
                    and wrapped[0].get("t") == "Link"
                ):
                    link = wrapped[0]
                    attributes = _attr(link)
                    if attributes is None:
                        raise ManuscriptRenderError(
                            "pandoc reference marker has malformed attributes"
                        )
                    attributes[2].append(
                        ["reference-command", wrapper_commands[wrapper["t"]]]
                    )
                    return link
        for key, child in list(value.items()):
            value[key] = restore(child)
        return value

    document["blocks"] = restore(document["blocks"])
    known_labels = set(raw_labels)
    for node in _walk(document["blocks"]):
        if node.get("t") != "Link":
            continue
        attributes = _attr(node)
        if attributes is None:
            continue
        metadata = dict(attributes[2])
        reference = metadata.get("reference")
        if not isinstance(reference, str):
            continue
        labels = [label.strip() for label in reference.split(",")]
        if labels and all(label in known_labels for label in labels):
            if "reference-command" not in metadata:
                attributes[2].append(["reference-command", "cref"])


def _attr(node: dict[str, Any]) -> tuple[str, list[str], list[list[str]]] | None:
    kind = node.get("t")
    value = node.get("c")
    raw: object | None = None
    if kind in {"Div", "Figure", "CodeBlock"} and isinstance(value, list) and value:
        raw = value[0]
    elif kind == "Header" and isinstance(value, list) and len(value) >= 2:
        raw = value[1]
    elif kind in {"Span", "Link", "Code"} and isinstance(value, list) and value:
        raw = value[0]
    if (
        isinstance(raw, list)
        and len(raw) == 3
        and isinstance(raw[0], str)
        and isinstance(raw[1], list)
        and isinstance(raw[2], list)
    ):
        return raw[0], raw[1], raw[2]
    return None


def _walk(value: object):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from _walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from _walk(child)


def _block_identity(block: dict[str, Any]) -> tuple[str, str]:
    attributes = _attr(block)
    if attributes is None:
        return "", ""
    if block.get("t") == "Header":
        return attributes[0], "section"
    if block.get("t") == "Figure":
        return attributes[0], "figure"
    classes = attributes[1]
    return attributes[0], classes[0] if classes else "div"


def _label_index(
    document: dict[str, Any], raw_labels: list[str], requested_labels: list[str]
) -> tuple[dict[str, tuple[int, dict[str, Any]]], dict[str, str]]:
    matches: dict[str, list[tuple[int, dict[str, Any]]]] = {
        label: [] for label in raw_labels
    }
    prefix_kinds = {
        "thm": "theorem",
        "lem": "lemma",
        "prop": "proposition",
        "cor": "corollary",
        "claim": "claim",
        "def": "definition",
        "rem": "remark",
        "sec": "section",
        "fig": "figure",
        "tab": "table",
        "eq": "equation",
    }
    kinds: dict[str, str] = {
        label: prefix_kinds.get(label.partition(":")[0], "reference")
        for label in raw_labels
    }
    for block_index, block in enumerate(document["blocks"]):
        for node in _walk(block):
            attributes = _attr(node)
            if attributes is None or not attributes[0]:
                continue
            label = attributes[0]
            if label not in matches:
                continue
            kind = "section" if node.get("t") == "Header" else (
                "figure" if node.get("t") == "Figure" else (
                    attributes[1][0] if attributes[1] else "div"
                )
            )
            matches[label].append((block_index, node))
            kinds[label] = kind
    missing = [label for label in requested_labels if not matches[label]]
    repeated = [label for label, values in matches.items() if len(values) > 1]
    if missing:
        raise ManuscriptRenderError(f"pandoc did not preserve labels: {missing}")
    if repeated:
        raise ManuscriptRenderError(f"pandoc repeated labels: {repeated}")
    return {
        label: values[0]
        for label, values in matches.items()
        if values
    }, kinds


def _bibliography_numbers(source: str) -> dict[str, int]:
    keys = re.findall(r"\\bibitem(?:\[[^\]]+\])?\{([^}]+)\}", source)
    _unique(keys, "bibliography keys")
    return {key: index for index, key in enumerate(keys, start=1)}


def _stringify_inlines(values: object) -> str:
    pieces: list[str] = []
    for node in _walk(values):
        kind = node.get("t")
        value = node.get("c")
        if kind == "Str" and isinstance(value, str):
            pieces.append(value)
        elif kind in {"Space", "SoftBreak", "LineBreak"}:
            pieces.append(" ")
        elif kind in {"Code", "Math"} and isinstance(value, list) and value:
            if isinstance(value[-1], str):
                pieces.append(value[-1])
    return re.sub(r"\s+", " ", "".join(pieces)).strip()


def _inline_converter(
    label_kinds: dict[str, str], bibliography: dict[str, int]
):
    def convert_many(values: object) -> list[dict[str, Any]]:
        if not isinstance(values, list):
            raise ManuscriptRenderError("pandoc inline collection is malformed")
        rendered: list[dict[str, Any]] = []
        for value in values:
            rendered.extend(convert(value))
        return rendered

    def convert(node: object) -> list[dict[str, Any]]:
        if not isinstance(node, dict):
            raise ManuscriptRenderError("pandoc inline is not an object")
        kind = node.get("t")
        value = node.get("c")
        if kind == "Str" and isinstance(value, str):
            return [{"kind": "text", "text": value}]
        if kind == "Space":
            return [{"kind": "space"}]
        if kind == "SoftBreak":
            return [{"kind": "softBreak"}]
        if kind == "LineBreak":
            return [{"kind": "lineBreak"}]
        if kind == "Math" and isinstance(value, list) and len(value) == 2:
            math_kind = value[0]
            tex = value[1]
            if not isinstance(math_kind, dict) or not isinstance(tex, str):
                raise ManuscriptRenderError("pandoc math node is malformed")
            if math_kind.get("t") not in {"InlineMath", "DisplayMath"}:
                raise ManuscriptRenderError("pandoc returned an unknown math mode")
            return [{
                "kind": "math",
                "display": math_kind["t"] == "DisplayMath",
                "tex": tex,
            }]
        if kind in {"Emph", "Strong", "Underline", "Strikeout", "SmallCaps"}:
            style = {
                "Emph": "emphasis",
                "Strong": "strong",
                "Underline": "underline",
                "Strikeout": "strikeout",
                "SmallCaps": "smallCaps",
            }[str(kind)]
            return [{"kind": style, "children": convert_many(value)}]
        if kind == "Quoted" and isinstance(value, list) and len(value) == 2:
            quote_kind = value[0]
            if not isinstance(quote_kind, dict):
                raise ManuscriptRenderError("pandoc quotation kind is malformed")
            delimiters = {
                "DoubleQuote": ("“", "”"),
                "SingleQuote": ("‘", "’"),
            }.get(quote_kind.get("t"))
            if delimiters is None:
                raise ManuscriptRenderError("pandoc returned an unknown quotation kind")
            return [
                {"kind": "text", "text": delimiters[0]},
                *convert_many(value[1]),
                {"kind": "text", "text": delimiters[1]},
            ]
        if kind == "Span" and isinstance(value, list) and len(value) == 2:
            attributes = _attr(node)
            if attributes is None:
                raise ManuscriptRenderError("pandoc span has malformed attributes")
            children = convert_many(value[1])
            classes = attributes[1]
            if not classes:
                return children
            if classes == ["upright"]:
                return [{"kind": "upright", "children": children}]
            raise ManuscriptRenderError(f"unsupported pandoc span classes: {classes}")
        if kind == "Code" and isinstance(value, list) and len(value) == 2:
            if not isinstance(value[1], str):
                raise ManuscriptRenderError("pandoc code inline is malformed")
            return [{"kind": "code", "text": value[1]}]
        if kind == "Link" and isinstance(value, list) and len(value) == 3:
            attributes = _attr(node)
            if attributes is None:
                raise ManuscriptRenderError("pandoc link has malformed attributes")
            metadata = dict(attributes[2])
            raw_label = metadata.get("reference")
            target = value[2]
            labels = raw_label.split(",") if isinstance(raw_label, str) else []
            if not labels or any(label not in label_kinds for label in labels):
                raise ManuscriptRenderError(
                    f"unsupported non-manuscript link in selected fragment: {target}"
                )
            visible = _stringify_inlines(value[1])
            kinds = [label_kinds[label] for label in labels]
            reference_kind = kinds[0] if len(set(kinds)) == 1 else "mixed"
            if reference_kind == "mixed":
                prefix = "References"
            elif len(labels) > 1:
                prefix = REFERENCE_PLURALS.get(reference_kind, "References")
            else:
                prefix = REFERENCE_TITLES.get(reference_kind, "Reference")
            command = metadata.get("reference-command")
            if command not in {"cref", "Cref", "ref", "eqref"}:
                raise ManuscriptRenderError(
                    "pandoc reference is missing its TeX command provenance"
                )
            if command == "cref":
                prefix = prefix[:1].lower() + prefix[1:]
            elif command in {"ref", "eqref"}:
                prefix = ""
                if command == "eqref":
                    visible = f"({visible})"
            return [{
                "kind": "reference",
                "labels": labels,
                "referenceKind": reference_kind,
                "prefix": prefix,
                "text": visible or ", ".join(labels),
            }]
        if kind == "Cite" and isinstance(value, list) and len(value) == 2:
            citations = value[0]
            if not isinstance(citations, list):
                raise ManuscriptRenderError("pandoc citation is malformed")
            keys: list[str] = []
            for citation in citations:
                key = citation.get("citationId") if isinstance(citation, dict) else None
                if not isinstance(key, str):
                    raise ManuscriptRenderError("pandoc citation has no key")
                keys.append(key)
            visible = "[" + ", ".join(
                str(bibliography.get(key, key)) for key in keys
            ) + "]"
            return [{"kind": "citation", "keys": keys, "text": visible}]
        raise ManuscriptRenderError(f"unsupported pandoc inline node: {kind}")

    return convert_many


def _render_environment_titles(
    *,
    source: str,
    manuscript_path: Path,
    raw_labels: list[str],
    label_kinds: dict[str, str],
    bibliography: dict[str, int],
) -> dict[str, list[dict[str, Any]]]:
    """Render optional theorem-like titles that Pandoc otherwise discards."""

    raw_titles: list[tuple[str, str]] = []
    for match in ENVIRONMENT_LABEL_PATTERN.finditer(source):
        title = match.group("title")
        if title:
            raw_titles.append((match.group("label"), title))
    if not raw_titles:
        return {}

    title_source = "\n\n".join(title for _, title in raw_titles)
    title_document = _run_pandoc(title_source, manuscript_path)
    _annotate_reference_commands(title_document, raw_labels)
    title_blocks = title_document["blocks"]
    if len(title_blocks) != len(raw_titles) or any(
        block.get("t") not in {"Para", "Plain"} for block in title_blocks
    ):
        raise ManuscriptRenderError(
            "pandoc could not preserve the manuscript environment titles"
        )
    convert_inlines = _inline_converter(label_kinds, bibliography)
    return {
        label: convert_inlines(block["c"])
        for (label, _), block in zip(raw_titles, title_blocks, strict=True)
    }


def _matching_brace(source: str, opening: int) -> int:
    depth = 0
    escaped = False
    for index in range(opening, len(source)):
        character = source[index]
        if escaped:
            escaped = False
            continue
        if character == "\\":
            escaped = True
            continue
        if character == "{":
            depth += 1
        elif character == "}":
            depth -= 1
            if depth == 0:
                return index
    raise ManuscriptRenderError("unbalanced braces while extracting a figure")


def _remove_braced_command(source: str, command: str) -> str:
    offset = 0
    while True:
        start = source.find(command, offset)
        if start < 0:
            return source
        cursor = start + len(command)
        while cursor < len(source) and source[cursor].isspace():
            cursor += 1
        if cursor < len(source) and source[cursor] == "[":
            close = source.find("]", cursor + 1)
            if close < 0:
                raise ManuscriptRenderError(f"unterminated optional argument for {command}")
            cursor = close + 1
            while cursor < len(source) and source[cursor].isspace():
                cursor += 1
        if cursor >= len(source) or source[cursor] != "{":
            offset = cursor
            continue
        close = _matching_brace(source, cursor)
        source = source[:start] + source[close + 1 :]
        offset = start


def _figure_source(source: str, label: str) -> str:
    label_matches = [
        match for match in LABEL_PATTERN.finditer(source) if match.group(1) == label
    ]
    if len(label_matches) != 1:
        raise ManuscriptRenderError(
            f"figure label {label} must occur exactly once in the TeX source"
        )
    position = label_matches[0].start()
    begins = list(FIGURE_BEGIN_PATTERN.finditer(source, 0, position))
    if not begins:
        raise ManuscriptRenderError(f"figure label {label} has no enclosing figure")
    begin = begins[-1]
    end = source.find(FIGURE_END, position)
    if end < 0:
        raise ManuscriptRenderError(f"figure label {label} has no closing environment")
    body = source[begin.end() : end]
    body = _remove_braced_command(body, r"\caption")
    body = _remove_braced_command(body, r"\label")
    if r"\begin{tikzpicture}" not in body:
        raise ManuscriptRenderError(
            f"selected figure {label} is not a supported inline TikZ figure"
        )
    return body.strip()


def _local_name(value: str) -> str:
    return value.rsplit("}", 1)[-1] if "}" in value else value


def _sanitize_svg(svg: str, label: str) -> str:
    try:
        root = ET.fromstring(svg)
    except ET.ParseError as error:
        raise ManuscriptRenderError(f"generated SVG for {label} is malformed") from error
    if _local_name(root.tag) != "svg":
        raise ManuscriptRenderError(f"generated SVG for {label} has no svg root")
    for element in root.iter():
        name = _local_name(element.tag)
        if name not in SVG_ALLOWED_ELEMENTS:
            raise ManuscriptRenderError(
                f"generated SVG for {label} contains unsupported element {name}"
            )
        for attribute, value in element.attrib.items():
            attribute_name = _local_name(attribute).lower()
            if attribute_name.startswith("on"):
                raise ManuscriptRenderError(
                    f"generated SVG for {label} contains an event handler"
                )
            if attribute_name == "href" and not value.startswith("#"):
                raise ManuscriptRenderError(
                    f"generated SVG for {label} contains an external reference"
                )
            if re.search(r"(?i)(?:javascript:|data:|file:|https?://)", value):
                raise ManuscriptRenderError(
                    f"generated SVG for {label} contains an unsafe URL"
                )
        if name == "style" and element.text:
            unsafe = re.search(
                r"(?i)(?:javascript:|data:|file:|https?://)", element.text
            )
            if unsafe:
                raise ManuscriptRenderError(
                    f"generated SVG for {label} contains unsafe style content"
                )
    return ET.tostring(root, encoding="unicode")


def _compile_figure_svg(
    *, source: str, manuscript_path: Path, label: str
) -> tuple[str, str]:
    latexmk = shutil.which("latexmk")
    dvisvgm = shutil.which("dvisvgm")
    if latexmk is None or dvisvgm is None:
        raise ManuscriptRenderError(
            "latexmk and dvisvgm are required to render manuscript figures"
        )
    marker = r"\begin{document}"
    if marker not in source:
        raise ManuscriptRenderError("manuscript has no document body")
    preamble = source.split(marker, 1)[0]
    drawing = _figure_source(source, label)
    isolated = (
        preamble
        + "\\usepackage[active,tightpage]{preview}\n"
        + marker
        + "\n\\begin{preview}\n"
        + drawing
        + "\n\\end{preview}\n\\end{document}\n"
    )
    environment = {**os.environ, "SOURCE_DATE_EPOCH": "0"}
    with tempfile.TemporaryDirectory(prefix="structural-exhaustion-figure-") as raw:
        temporary = Path(raw)
        tex_path = temporary / "figure.tex"
        tex_path.write_text(isolated, encoding="utf-8")
        compile_process = subprocess.run(
            [
                latexmk,
                "-pdf",
                "-interaction=nonstopmode",
                "-halt-on-error",
                f"-outdir={temporary}",
                str(tex_path),
            ],
            cwd=manuscript_path.parent,
            env=environment,
            text=True,
            capture_output=True,
            check=False,
        )
        if compile_process.returncode != 0:
            output = (compile_process.stdout + compile_process.stderr).strip()
            raise ManuscriptRenderError(
                f"LaTeX could not render figure {label}: {output[-2400:]}"
            )
        pdf_path = temporary / "figure.pdf"
        svg_path = temporary / "figure.svg"
        convert_process = subprocess.run(
            [
                dvisvgm,
                "--pdf",
                "--page=1",
                f"--output={svg_path}",
                str(pdf_path),
            ],
            cwd=manuscript_path.parent,
            env=environment,
            text=True,
            capture_output=True,
            check=False,
        )
        if convert_process.returncode != 0 or not svg_path.is_file():
            output = (convert_process.stdout + convert_process.stderr).strip()
            raise ManuscriptRenderError(
                f"dvisvgm could not render figure {label}: {output[-2400:]}"
            )
        svg = _sanitize_svg(svg_path.read_text(encoding="utf-8"), label)
    return svg, hashlib.sha256(svg.encode("utf-8")).hexdigest()


def _block_converter(
    *,
    label_kinds: dict[str, str],
    bibliography: dict[str, int],
    figure_svgs: dict[str, tuple[str, str]],
    environment_titles: dict[str, list[dict[str, Any]]],
):
    convert_inlines = _inline_converter(label_kinds, bibliography)

    def convert_many(values: object) -> list[dict[str, Any]]:
        if not isinstance(values, list):
            raise ManuscriptRenderError("pandoc block collection is malformed")
        return [convert(value) for value in values]

    def convert(node: object) -> dict[str, Any]:
        if not isinstance(node, dict):
            raise ManuscriptRenderError("pandoc block is not an object")
        kind = node.get("t")
        value = node.get("c")
        if kind in {"Para", "Plain"}:
            return {"kind": "paragraph", "inlines": convert_inlines(value)}
        if kind == "Header" and isinstance(value, list) and len(value) == 3:
            attributes = _attr(node)
            if attributes is None or not isinstance(value[0], int):
                raise ManuscriptRenderError("pandoc heading is malformed")
            return {
                "kind": "heading",
                "level": value[0],
                "label": attributes[0] or None,
                "inlines": convert_inlines(value[2]),
            }
        if kind == "Div" and isinstance(value, list) and len(value) == 2:
            attributes = _attr(node)
            if attributes is None:
                raise ManuscriptRenderError("pandoc environment is malformed")
            classes = attributes[1]
            environment = classes[0] if classes else "div"
            return {
                "kind": "environment",
                "environment": environment,
                "label": attributes[0] or None,
                "title": environment_titles.get(attributes[0]),
                "blocks": convert_many(value[1]),
            }
        if kind == "OrderedList" and isinstance(value, list) and len(value) == 2:
            attributes = value[0]
            items = value[1]
            if not isinstance(attributes, list) or not attributes or not isinstance(
                attributes[0], int
            ) or not isinstance(items, list):
                raise ManuscriptRenderError("pandoc ordered list is malformed")
            return {
                "kind": "orderedList",
                "start": attributes[0],
                "items": [convert_many(item) for item in items],
            }
        if kind == "BulletList" and isinstance(value, list):
            return {
                "kind": "bulletList",
                "items": [convert_many(item) for item in value],
            }
        if kind == "BlockQuote" and isinstance(value, list):
            return {"kind": "blockQuote", "blocks": convert_many(value)}
        if kind == "CodeBlock" and isinstance(value, list) and len(value) == 2:
            if not isinstance(value[1], str):
                raise ManuscriptRenderError("pandoc code block is malformed")
            return {"kind": "codeBlock", "text": value[1]}
        if kind == "Figure" and isinstance(value, list) and len(value) == 3:
            attributes = _attr(node)
            if attributes is None or not attributes[0]:
                raise ManuscriptRenderError("selected figure has no stable label")
            label = attributes[0]
            if label not in figure_svgs:
                raise ManuscriptRenderError(f"figure {label} has no compiled SVG")
            caption = value[1]
            if not isinstance(caption, list) or len(caption) != 2:
                raise ManuscriptRenderError(f"figure {label} has a malformed caption")
            long_caption = convert_many(caption[1])
            svg, digest = figure_svgs[label]
            return {
                "kind": "figure",
                "label": label,
                "svg": svg,
                "svgSha256": digest,
                "caption": long_caption,
            }
        raise ManuscriptRenderError(f"unsupported pandoc block node: {kind}")

    return convert_many


def render_manuscript_fragments(
    *, path: str, source_root: Path, requested_labels: list[str]
) -> dict[str, Any]:
    """Return checked label metadata, diagram nodes, and rendered fragments."""

    _unique(requested_labels, "requested manuscript labels")
    manuscript_path, source, source_bytes = _trusted_manuscript(path, source_root)
    raw_labels = LABEL_PATTERN.findall(source)
    _unique(raw_labels, f"LaTeX labels in {path}")
    unknown = [label for label in requested_labels if label not in set(raw_labels)]
    if unknown:
        raise ManuscriptRenderError(f"unknown manuscript labels: {unknown}")
    document = _run_pandoc(source, manuscript_path)
    _annotate_reference_commands(document, raw_labels)
    label_locations, label_kinds = _label_index(
        document, raw_labels, requested_labels
    )
    bibliography = _bibliography_numbers(source)
    environment_titles = _render_environment_titles(
        source=source,
        manuscript_path=manuscript_path,
        raw_labels=raw_labels,
        label_kinds=label_kinds,
        bibliography=bibliography,
    )
    nodes = sorted({
        int(value)
        for value in re.findall(r"\\textbf\{\[([0-9]+)\]\}", source)
    })
    label_lines = {
        match.group(1): source.count("\n", 0, match.start()) + 1
        for match in LABEL_PATTERN.finditer(source)
    }

    selected_blocks: dict[str, list[dict[str, Any]]] = {}
    includes_proof: dict[str, bool] = {}
    figure_labels: list[str] = []
    blocks = document["blocks"]
    for label in requested_labels:
        block_index, matched_node = label_locations[label]
        owner = blocks[block_index]
        owner_label, _owner_kind = _block_identity(owner)
        if owner_label != label or matched_node is not owner:
            raise ManuscriptRenderError(
                f"label {label} is nested in unsupported surrounding content"
            )
        fragment_blocks = [owner]
        proof = False
        if owner.get("t") == "Header":
            value = owner.get("c")
            if not isinstance(value, list) or not isinstance(value[0], int):
                raise ManuscriptRenderError(f"section label {label} is malformed")
            level = value[0]
            end = next(
                (
                    index
                    for index in range(block_index + 1, len(blocks))
                    if blocks[index].get("t") == "Header"
                    and isinstance(blocks[index].get("c"), list)
                    and blocks[index]["c"][0] <= level
                ),
                len(blocks),
            )
            fragment_blocks = blocks[block_index:end]
        elif owner.get("t") == "Div":
            if block_index + 1 < len(blocks):
                next_label, next_kind = _block_identity(blocks[block_index + 1])
                if next_kind == "proof" and not next_label:
                    fragment_blocks.append(blocks[block_index + 1])
                    proof = True
        selected_blocks[label] = fragment_blocks
        includes_proof[label] = proof
        for node in _walk(fragment_blocks):
            if node.get("t") != "Figure":
                continue
            attributes = _attr(node)
            if attributes is None or not attributes[0]:
                raise ManuscriptRenderError(
                    f"fragment {label} contains an unlabeled figure"
                )
            if attributes[0] not in figure_labels:
                figure_labels.append(attributes[0])

    figure_svgs = {
        label: _compile_figure_svg(
            source=source, manuscript_path=manuscript_path, label=label
        )
        for label in figure_labels
    }
    convert_blocks = _block_converter(
        label_kinds=label_kinds,
        bibliography=bibliography,
        figure_svgs=figure_svgs,
        environment_titles=environment_titles,
    )
    fragments: list[dict[str, Any]] = []
    for label in requested_labels:
        rendered_blocks = convert_blocks(selected_blocks[label])
        fragments.append({
            "label": label,
            "environment": label_kinds[label],
            "sourceLine": label_lines[label],
            "includesProof": includes_proof[label],
            "contentSha256": _canonical_hash(rendered_blocks),
            "blocks": rendered_blocks,
        })
    return {
        "sha256": hashlib.sha256(source_bytes).hexdigest(),
        "labels": raw_labels,
        "mathematicalObjectLabels": [
            label
            for label in raw_labels
            if label_kinds[label] in MATHEMATICAL_OBJECT_KINDS
        ],
        "nodeIds": nodes,
        "fragments": fragments,
    }
