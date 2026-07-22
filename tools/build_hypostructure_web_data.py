#!/usr/bin/env python3
"""Build the deterministic, presentation-ready Hypostructure web snapshot.

The builder accepts only the Hypostructure framework and its native example
packages.  Lean's compiled declaration catalog is authoritative for framework
declarations; source inspection is limited to module summaries, imports,
fixtures, and application topology.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import html
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import re
import subprocess
from typing import Any, Iterable


SCHEMA_VERSION = "2.0.0"
DEFAULT_RAW = Path("generated/hypostructure/web/declarations.raw.json")
DEFAULT_SNAPSHOT = Path("generated/hypostructure/web/snapshot.json")
DEFAULT_MANIFEST = Path("generated/hypostructure/web/manifest.json")
SOURCE_ROOTS = (
    Path("hypostructure/Hypostructure"),
    Path("examples/hypostructure_erdos_64_eg"),
    Path("examples/hypostructure_pde"),
)
CONTENT_ROOT = Path("web/content")
ERDOS_PAPER_TOPOLOGY = Path("migration/hypostructure/eg-node-matrix.csv")
ERDOS_NEW_KERNEL_STATUSES = {"missing", "stale", "fresh"}
ERDOS_PARITY_STATUSES = {"missing", "not_run", "checked", "mismatch", "blocked"}
ERDOS_MATH_STATUSES = {"unknown", "not_assessed", "open", "closed"}
ERDOS_WORK_STATUSES = {"unknown", "not_captured", "captured"}
ERDOS_MIGRATION_STATUSES = {
    "inventoried",
    "scaffolded",
    "typechecked",
    "parity_checked",
    "migrated_open",
    "migrated_closed",
    "published",
    "cutover",
}
ERDOS_DIAGRAM_PARTS = (
    ("I", 1, 25),
    ("II", 26, 34),
    ("III", 35, 46),
    ("IV", 47, 56),
    ("V", 57, 64),
    ("VI", 65, 77),
    ("VII", 78, 85),
    ("VIII", 86, 109),
    ("IX", 110, 124),
    ("X", 125, 144),
    ("XI", 145, 157),
)
PUBLICATION_WORDS = ("migration", "legacy", "cutover", "structural exhaustion")


CT_LAYERS = {
    "CT1": "Target realization or exact avoidance",
    "CT2": "Local deletion and criticality",
    "CT3": "Response compression and table classification",
    "CT4": "Deterministic charging and capacity",
    "CT5": "Local-witness aggregation",
    "CT6": "Ordered activity analysis",
    "CT7": "Exact context classification",
    "CT8": "Finite-type repetition and response",
    "CT9": "Label-fibre overload",
    "CT10": "Finite refinement classification",
    "CT11": "Additive-deficit localization",
    "CT12": "Well-founded structural peeling",
    "CT13": "Tiered-resource selection",
    "CT14": "Mass, capacity, and multiplicity",
    "CT15": "Target-relative rank",
    "CT16": "Whole-support closed-code exhaustion",
    "CT17": "Bounded target thickening",
}


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def stable_id(prefix: str, value: str) -> str:
    readable = re.sub(r"[^a-z0-9]+", "-", value.lower()).strip("-")
    if len(readable) > 72:
        readable = readable[:64].rstrip("-")
    digest = hashlib.sha256(value.encode()).hexdigest()[:10]
    return f"{prefix}-{readable}-{digest}"


def clean_public_text(value: str | None) -> str:
    """Remove source commentary about repository history from published prose."""
    if not value:
        return ""
    paragraphs: list[str] = []
    for paragraph in re.split(r"\n\s*\n", value.strip()):
        sentences = re.split(r"(?<=[.!?])\s+|\n+", paragraph)
        kept = [
            sentence.strip()
            for sentence in sentences
            if sentence.strip()
            and not any(word in sentence.casefold() for word in PUBLICATION_WORDS)
        ]
        if kept:
            paragraphs.append(" ".join(kept))
    return "\n\n".join(paragraphs)


class _AllowlistSanitizer(HTMLParser):
    tags = {"p", "strong", "em", "code", "pre", "ul", "ol", "li", "br"}

    def __init__(self) -> None:
        super().__init__(convert_charrefs=False)
        self.output: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag in self.tags:
            self.output.append(f"<{tag}>")

    def handle_startendtag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag == "br":
            self.output.append("<br>")

    def handle_endtag(self, tag: str) -> None:
        if tag in self.tags and tag != "br":
            self.output.append(f"</{tag}>")

    def handle_data(self, data: str) -> None:
        self.output.append(html.escape(data, quote=False))

    def handle_entityref(self, name: str) -> None:
        self.output.append(f"&{name};")

    def handle_charref(self, name: str) -> None:
        self.output.append(f"&#{name};")


def sanitize_html(value: str) -> str:
    sanitizer = _AllowlistSanitizer()
    sanitizer.feed(value)
    sanitizer.close()
    return "".join(sanitizer.output)


def _inline_markdown(value: str) -> str:
    escaped = html.escape(value, quote=False)
    escaped = re.sub(r"`([^`]+)`", r"<code>\1</code>", escaped)
    escaped = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", escaped)
    escaped = re.sub(r"(?<!\*)\*([^*]+)\*(?!\*)", r"<em>\1</em>", escaped)
    return escaped


def markdown_to_safe_html(value: str) -> str:
    value = re.sub(r"<script\b[^>]*>.*?</script\s*>", "", value, flags=re.IGNORECASE | re.DOTALL)
    value = re.sub(r"<[^>]*>", "", value)
    blocks: list[str] = []
    list_items: list[str] = []

    def flush_list() -> None:
        if list_items:
            blocks.append("<ul>" + "".join(f"<li>{item}</li>" for item in list_items) + "</ul>")
            list_items.clear()

    for paragraph in re.split(r"\n\s*\n", value.strip()):
        lines = [line.strip() for line in paragraph.splitlines() if line.strip()]
        if lines and all(line.startswith("- ") for line in lines):
            list_items.extend(_inline_markdown(line[2:]) for line in lines)
            continue
        flush_list()
        if lines:
            blocks.append(f"<p>{_inline_markdown(' '.join(lines))}</p>")
    flush_list()
    return sanitize_html("".join(blocks))


def parse_markdown_page(path: Path, page_id: str) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8")
    title_match = re.search(r"^#\s+(.+)$", text, re.MULTILINE)
    if not title_match:
        raise ValueError(f"{path}: missing H1")
    title = title_match.group(1).strip()
    after_title = text[title_match.end() :]
    heading_matches = list(re.finditer(r"^##\s+(.+)$", after_title, re.MULTILINE))
    intro_end = heading_matches[0].start() if heading_matches else len(after_title)
    intro = after_title[:intro_end].strip()
    sections: list[dict[str, Any]] = []
    for index, heading in enumerate(heading_matches):
        end = heading_matches[index + 1].start() if index + 1 < len(heading_matches) else len(after_title)
        body = after_title[heading.end() : end].strip()
        section_title = heading.group(1).strip()
        sections.append({
            "id": stable_id("section", f"{page_id}:{section_title}"),
            "title": section_title,
            "blocks": [{"kind": "prose", "html": markdown_to_safe_html(body)}],
        })
    summary = re.split(r"\n\s*\n", intro, maxsplit=1)[0].strip().replace("\n", " ")
    return {
        "id": page_id,
        "title": title,
        "summary": summary,
        "breadcrumbs": [{"label": "Home", "href": "/"}] if page_id != "home" else [],
        "sections": sections,
        "canonicalPath": "/" if page_id == "home" else f"/{page_id}",
    }


def hydrate_content_block(
    raw: dict[str, Any], content_root: Path | None = None,
    module_urls: dict[str, str] | None = None,
    declaration_urls: dict[str, str] | None = None,
) -> dict[str, Any]:
    kind = raw["kind"]
    if kind == "workflow":
        return {
            "kind": "steps",
            "items": [
                {"title": stage["label"], "body": stage["detail"]}
                for stage in raw.get("stages", [])
            ],
        }
    if kind == "steps":
        items = []
        for index, item in enumerate(raw.get("items", []), start=1):
            if isinstance(item, str):
                items.append({"title": f"Step {index}", "body": item})
            else:
                items.append({"title": item["title"], "body": item["body"], **({"href": item["href"]} if item.get("href") else {})})
        return {"kind": "steps", "items": items}
    if kind == "table":
        keys = [f"column_{index + 1}" for index in range(len(raw["columns"]))]
        return {
            "kind": "table",
            "caption": raw.get("title"),
            "columns": [{"key": key, "label": label} for key, label in zip(keys, raw["columns"])],
            "rows": [dict(zip(keys, row)) for row in raw.get("rows", [])],
        }
    if kind == "math":
        return {
            "kind": "math",
            "latex": raw["tex"],
            "display": bool(raw.get("display", True)),
            "label": raw.get("title") or raw.get("description"),
        }
    if kind == "callout":
        return {
            "kind": "callout",
            "tone": raw.get("tone", "info"),
            "title": raw["title"],
            "body": raw.get("body", ""),
            **({"items": raw["items"]} if raw.get("items") else {}),
        }
    if kind == "cards":
        def card_href(item: dict[str, Any]) -> str | None:
            if item.get("href"):
                return item["href"]
            if item.get("module"):
                href = (module_urls or {}).get(item["module"])
                if href is None:
                    raise ValueError(f"curated card references unknown module: {item['module']}")
                return href
            if item.get("declaration"):
                href = (declaration_urls or {}).get(item["declaration"])
                if href is None:
                    raise ValueError(
                        f"curated card references unknown declaration: {item['declaration']}"
                    )
                return href
            return None

        return {
            "kind": "cards",
            "columns": raw.get("columns", 3),
            "items": [
                {
                    "title": item["title"],
                    "summary": item["summary"],
                    **({"href": href} if (href := card_href(item)) else {}),
                    **({"eyebrow": item["eyebrow"]} if item.get("eyebrow") else {}),
                    **({"meta": item["meta"]} if item.get("meta") else {}),
                }
                for item in raw.get("items", [])
            ],
        }
    if kind == "code":
        code = raw.get("code")
        if raw.get("code_file"):
            if content_root is None:
                raise ValueError("curated code_file requires a content root")
            root = content_root.resolve()
            code_path = (root / raw["code_file"]).resolve()
            if root not in code_path.parents or code_path.suffix != ".lean":
                raise ValueError(f"unsafe curated code_file: {raw['code_file']}")
            code = code_path.read_text(encoding="utf-8")
        if not isinstance(code, str) or not code.strip():
            raise ValueError("curated code block has no code")
        return {
            "kind": "code",
            "language": raw.get("language", "text"),
            "code": code,
            **({"caption": raw["caption"]} if raw.get("caption") else {}),
            **({"sourceHref": raw["sourceHref"]} if raw.get("sourceHref") else {}),
        }
    if kind == "links":
        return {
            "kind": "links",
            "items": [
                {
                    "label": item["label"],
                    "href": item["href"],
                    **({"description": item["description"]} if item.get("description") else {}),
                }
                for item in raw.get("items", [])
            ],
        }
    if kind == "graph":
        return {
            "kind": "graph",
            **({"title": raw["title"]} if raw.get("title") else {}),
            **({"description": raw["description"]} if raw.get("description") else {}),
            "nodes": [
                {
                    "id": node["id"],
                    "label": node["label"],
                    "x": node["x"],
                    "y": node["y"],
                    **({"kind": node["kind"]} if node.get("kind") else {}),
                    **({"summary": node["summary"]} if node.get("summary") else {}),
                    **({"href": node["href"]} if node.get("href") else {}),
                }
                for node in raw.get("nodes", [])
            ],
            "edges": [
                {
                    "id": edge["id"],
                    "source": edge["source"],
                    "target": edge["target"],
                    **({"label": edge["label"]} if edge.get("label") else {}),
                }
                for edge in raw.get("edges", [])
            ],
            "legend": [
                {"label": item["label"], "kind": item["kind"]}
                for item in raw.get("legend", [])
            ],
        }
    raise ValueError(f"unsupported curated block kind: {kind}")


def add_curated_blocks(
    page: dict[str, Any], blocks: Iterable[dict[str, Any]], content_root: Path,
    module_urls: dict[str, str], declaration_urls: dict[str, str],
    *, prepend: bool = False,
) -> None:
    curated_sections = []
    for raw in blocks:
        curated_sections.append({
            "id": raw["id"],
            "title": raw.get("title"),
            "blocks": [hydrate_content_block(
                raw, content_root, module_urls, declaration_urls
            )],
        })
    if prepend:
        page["sections"] = curated_sections + page["sections"]
    else:
        page["sections"].extend(curated_sections)


def module_name_for_path(relative_path: Path) -> str:
    if relative_path.parts[0] == "hypostructure":
        inner = relative_path.relative_to("hypostructure").with_suffix("")
    elif relative_path.parts[1] == "hypostructure_erdos_64_eg":
        inner = relative_path.relative_to("examples/hypostructure_erdos_64_eg").with_suffix("")
    elif relative_path.parts[1] == "hypostructure_pde":
        inner = relative_path.relative_to("examples/hypostructure_pde").with_suffix("")
    else:
        raise ValueError(f"unsupported source path: {relative_path}")
    return ".".join(inner.parts)


def source_layer(relative_path: Path) -> tuple[str, str]:
    text = relative_path.as_posix()
    if "/Fixtures/" in text:
        return "fixtures", "fixture"
    if "hypostructure_erdos_64_eg" in text:
        return "erdos", "application"
    if "hypostructure_pde" in text:
        return "pde", "example"
    match = re.search(r"/Hypostructure/(CT\d+)(?:/|\.)", text)
    if match:
        return "ct", "framework"
    for layer in ("Core", "Graph", "PDE", "Routes", "Canonical"):
        if f"/Hypostructure/{layer}" in text:
            return layer.lower(), "framework"
    return "framework", "framework"


def module_doc(text: str) -> str:
    match = re.search(r"/-!\s*(.*?)\s*-/", text, re.DOTALL)
    if not match:
        return ""
    value = re.sub(r"^#\s+", "", match.group(1).strip(), flags=re.MULTILINE)
    return clean_public_text(value)


def discover_sources(root: Path) -> tuple[list[dict[str, Any]], dict[str, str], dict[str, str]]:
    files: list[Path] = []
    for source_root in SOURCE_ROOTS:
        absolute = root / source_root
        if not absolute.exists():
            raise FileNotFoundError(f"required source root not found: {source_root}")
        for path in absolute.rglob("*.lean"):
            local = path.relative_to(absolute)
            if any(part.startswith(".") or part in {"build", "cache", "node_modules"} for part in local.parts):
                continue
            if source_root == Path("examples/hypostructure_erdos_64_eg"):
                if local.name != "HypostructureErdos64EG.lean" and local.parts[0] != "HypostructureErdos64EG":
                    continue
            if source_root == Path("examples/hypostructure_pde"):
                if local.name != "HypostructurePDEExamples.lean" and local.parts[0] != "HypostructurePDEExamples":
                    continue
            if source_root == Path("hypostructure/Hypostructure") and local.parts[0] == "Canonical":
                continue
            files.append(path)
    records: list[dict[str, Any]] = []
    path_to_id: dict[str, str] = {}
    module_to_source: dict[str, str] = {}
    for path in sorted(files):
        relative = path.relative_to(root)
        relative_text = relative.as_posix()
        source_id = stable_id("source", relative_text)
        layer, kind = source_layer(relative)
        module_name = module_name_for_path(relative)
        record = {
            "id": source_id,
            "path": relative_text,
            "sha256": sha256_file(path),
            "module": module_name,
            "layer": layer,
            "kind": kind,
        }
        records.append(record)
        path_to_id[relative_text] = source_id
        module_to_source[module_name] = source_id
    return records, path_to_id, module_to_source


def raw_source_path(value: str) -> str:
    return (Path("hypostructure") / value).as_posix()


def range_line(value: Any, side: str, default: int = 1) -> int:
    if isinstance(value, dict):
        point = value.get(side)
        if isinstance(point, dict) and isinstance(point.get("line"), int):
            return max(1, point["line"])
    return default


def elaborated_signature_shape(signature: str) -> str:
    """Describe only directly observable syntax in an elaborated Lean type."""
    stripped = signature.strip()
    if not stripped:
        return "no elaborated type text was exported"
    line_count = len(stripped.splitlines())
    arrow_count = stripped.count("→")
    forall_count = stripped.count("∀")
    parts = [f"is printed on {line_count} line{'s' if line_count != 1 else ''}"]
    if stripped.startswith("∀"):
        parts.append("begins with universal quantification")
    elif stripped.startswith("{") or stripped.startswith("("):
        parts.append("begins with an explicit binder")
    else:
        parts.append("begins with its result expression")
    parts.append(
        f"contains {forall_count} universal-quantifier token"
        f"{'s' if forall_count != 1 else ''} and {arrow_count} function-arrow token"
        f"{'s' if arrow_count != 1 else ''}"
    )
    return "; ".join(parts)


def declaration_catalog_fallback(
    *, name: str, kind: str, module: str, layer: str, signature: str,
    body_available: bool, type_dependency_count: int,
    body_dependency_count: int, start_line: int, end_line: int,
    provenance: str,
) -> tuple[str, str, str]:
    """Build an honest structural description when no authored docs exist."""
    shape = elaborated_signature_shape(signature)
    origin = (
        "the compiled Lean environment"
        if provenance == "compiled_environment"
        else "the conservative native-source index"
    )
    body_record = (
        "an available body"
        if body_available
        else "no available body"
    )
    summary = (
        f"{kind.capitalize()} `{name}` in the `{layer}` layer, recorded from "
        f"{origin}; its elaborated signature {shape}."
    )
    detail = (
        f"No authored docstring is attached to `{name}`. This reference entry "
        f"therefore reports compiled or indexed structure only and does not "
        f"infer the declaration's mathematical purpose. Lean records it as a "
        f"`{kind}` in module `{module}` in the `{layer}` layer. Its elaborated "
        f"signature {shape}. The exporter records {body_record}, "
        f"{type_dependency_count} type dependencies, and "
        f"{body_dependency_count} body dependencies. Lines {start_line}–{end_line} "
        "are bound to the hash-verified published source file."
    )
    return summary, detail, shape


def compiler_generated_declaration(name: str, kind: str) -> bool:
    if kind == "recursor" or any(part.startswith("_") for part in name.split(".")):
        return True
    generated_suffixes = (
        ".casesOn", ".rec", ".recOn", ".brecOn", ".binductionOn", ".below",
        ".ibelow", ".noConfusion", ".noConfusionType", ".mk.inj",
        ".mk.injEq", ".sizeOf", ".sizeOf_spec", ".toCtorIdx", ".ctorIdx",
        ".ctorElim", ".ctorElimType",
        ".elim", ".inj", ".injEq", ".congr", ".congr_simp",
    )
    return (
        name.endswith(generated_suffixes)
        or ".match_" in name
        or re.search(r"\.eq_\d+$", name) is not None
    )


def publish_compiled_declaration(declaration: dict[str, Any]) -> bool:
    name = declaration.get("name")
    if not isinstance(name, str):
        return False
    kind = declaration.get("kind", "declaration")
    if compiler_generated_declaration(name, kind):
        return False
    return declaration.get("range") is not None or bool(declaration.get("doc_string"))


def normalize_declarations(
    raw: dict[str, Any], path_to_id: dict[str, str]
) -> tuple[list[dict[str, Any]], dict[str, str]]:
    result: list[dict[str, Any]] = []
    name_to_id: dict[str, str] = {}
    published_names = {
        declaration["name"]
        for declaration in raw.get("declarations", [])
        if publish_compiled_declaration(declaration)
    }
    for declaration in raw.get("declarations", []):
        name = declaration.get("name")
        source_file = declaration.get("source_file")
        if not isinstance(name, str) or not isinstance(source_file, str):
            raise ValueError("compiled declaration missing name or source_file")
        relative = raw_source_path(source_file)
        source_id = path_to_id.get(relative)
        if source_id is None:
            raise ValueError(f"compiled declaration references non-public source: {relative}")
        declaration_id = stable_id("declaration", name)
        name_to_id[name] = declaration_id
        start_line = range_line(declaration.get("range"), "start")
        end_line = range_line(declaration.get("range"), "end", start_line)
        docstring = clean_public_text(declaration.get("doc_string"))
        signature = declaration.get("type", "")
        source_href = f"/source/{source_id}?start={start_line}&end={max(start_line, end_line)}"
        dependencies = sorted(
            dependency
            for dependency in set(declaration.get("type_dependencies", []) + declaration.get("body_dependencies", []))
            if dependency in published_names
        )
        kind = declaration.get("kind", "declaration")
        if not publish_compiled_declaration(declaration):
            continue
        module = declaration.get("module") or "Hypostructure"
        layer = declaration.get("layer", "framework")
        body_available = bool(declaration.get("body_available"))
        type_dependencies = sorted(set(declaration.get("type_dependencies", [])))
        body_dependencies = sorted(set(declaration.get("body_dependencies", [])))
        fallback_summary, fallback_detail, signature_shape = (
            declaration_catalog_fallback(
                name=name,
                kind=kind,
                module=module,
                layer=layer,
                signature=signature,
                body_available=body_available,
                type_dependency_count=len(type_dependencies),
                body_dependency_count=len(body_dependencies),
                start_line=start_line,
                end_line=max(start_line, end_line),
                provenance="compiled_environment",
            )
        )
        result.append({
            "id": declaration_id,
            "canonical_id": declaration.get("declaration_id", name),
            "name": name,
            "short_name": name.rsplit(".", 1)[-1],
            "kind": kind,
            "module": module,
            "module_id": stable_id("module", module),
            "layer": layer,
            "signature": signature,
            "docstring": docstring,
            "source_id": source_id,
            "source_range": {"start_line": start_line, "end_line": max(start_line, end_line)},
            "selection_range": declaration.get("selection_range"),
            "body_available": body_available,
            "provenance": "compiled_environment",
            "type_dependencies": type_dependencies,
            "body_dependencies": body_dependencies,
            "url": f"/reference/declarations/{declaration_id}",
            "title": name,
            "summary": docstring or fallback_summary,
            "description": docstring or fallback_detail,
            "breadcrumbs": [
                {"label": "Reference", "href": "/reference"},
                {"label": module, "href": f"/reference/modules/{stable_id('module', module)}"},
            ],
            "sections": [
                {"id": f"{declaration_id}-signature", "title": "Elaborated type", "blocks": [{"kind": "code", "language": "lean", "code": signature, "caption": name, "sourceHref": source_href}]},
                {"id": f"{declaration_id}-documentation", "title": "Documentation", "blocks": [{"kind": "prose", "html": markdown_to_safe_html(docstring or fallback_detail)}]},
                {"id": f"{declaration_id}-catalog-facts", "title": "Catalog facts", "blocks": [{
                    "kind": "table",
                    "caption": "Compiler-exported structure",
                    "columns": [
                        {"key": "field", "label": "Field"},
                        {"key": "value", "label": "Recorded value"},
                    ],
                    "rows": [
                        {"field": "Qualified name", "value": name},
                        {"field": "Declaration kind", "value": kind},
                        {"field": "Module", "value": module},
                        {"field": "Layer", "value": layer},
                        {"field": "Elaborated signature shape", "value": signature_shape},
                        {"field": "Body metadata", "value": "available" if body_available else "not available"},
                        {"field": "Type dependencies", "value": str(len(type_dependencies))},
                        {"field": "Body dependencies", "value": str(len(body_dependencies))},
                        {"field": "Source binding", "value": f"hash-verified lines {start_line}–{max(start_line, end_line)}"},
                    ],
                }]},
                {"id": f"{declaration_id}-dependencies", "title": "Dependencies", "blocks": [{"kind": "links", "items": [{"label": dependency, "href": f"/reference/declarations/{stable_id('declaration', dependency)}"} for dependency in dependencies]}]},
            ],
            "canonicalPath": f"/reference/declarations/{declaration_id}",
        })
    result.sort(key=lambda item: item["name"])
    return result, name_to_id


DECLARATION_RE = re.compile(
    r"^(?:noncomputable\s+)?(?:protected\s+)?(def|theorem|lemma|abbrev|structure|class|inductive|opaque)\s+([^\s(:{]+)"
)


def source_declarations(
    root: Path,
    source_records: list[dict[str, Any]],
    existing_names: set[str],
) -> list[dict[str, Any]]:
    """Extract application and fixture declarations absent from the Lean catalog."""
    result: list[dict[str, Any]] = []
    for source in source_records:
        if source["kind"] == "framework" and source["layer"] != "fixtures":
            continue
        path = root / source["path"]
        lines = path.read_text(encoding="utf-8").splitlines()
        namespace: list[str] = []
        pending_doc = ""
        in_doc = False
        doc_lines: list[str] = []
        for index, line in enumerate(lines):
            stripped = line.strip()
            if stripped.startswith("/--"):
                in_doc = True
                doc_lines = [stripped[3:]]
                if "-/" in stripped[3:]:
                    in_doc = False
                    pending_doc = stripped[3:].split("-/", 1)[0].strip()
                continue
            if in_doc:
                if "-/" in stripped:
                    doc_lines.append(stripped.split("-/", 1)[0])
                    pending_doc = "\n".join(doc_lines).strip()
                    in_doc = False
                else:
                    doc_lines.append(stripped)
                continue
            if stripped.startswith("namespace "):
                namespace.extend(stripped.removeprefix("namespace ").strip().split("."))
                continue
            if stripped.startswith("end") and namespace:
                namespace.pop()
                continue
            declaration_line = re.sub(r"^(?:@\[[^]]+\]\s*)+", "", stripped)
            if declaration_line.startswith("private "):
                pending_doc = ""
                continue
            match = DECLARATION_RE.match(declaration_line)
            if not match:
                continue
            kind, short_name = match.groups()
            full_name = short_name if "." in short_name else ".".join([*namespace, short_name])
            if full_name in existing_names:
                pending_doc = ""
                continue
            signature_lines = [declaration_line]
            for following in lines[index + 1 : min(len(lines), index + 30)]:
                if ":=" in " ".join(signature_lines) or signature_lines[-1].rstrip().endswith(" where"):
                    break
                signature_lines.append(following.strip())
            signature = " ".join(signature_lines)
            signature = re.split(r"\s+:=|\s+where(?:\s|$)", signature, maxsplit=1)[0].strip()
            end_line = index + 1 + max(0, len(signature_lines) - 1)
            declaration_id = stable_id("declaration", full_name)
            display_kind = "theorem" if kind == "lemma" else kind
            body_available = True
            fallback_summary, fallback_detail, signature_shape = (
                declaration_catalog_fallback(
                    name=full_name,
                    kind=display_kind,
                    module=source["module"],
                    layer=source["layer"],
                    signature=signature,
                    body_available=body_available,
                    type_dependency_count=0,
                    body_dependency_count=0,
                    start_line=index + 1,
                    end_line=end_line,
                    provenance="source_index",
                )
            )
            docstring = clean_public_text(pending_doc)
            result.append({
                "id": declaration_id,
                "canonical_id": full_name,
                "name": full_name,
                "short_name": short_name,
                "kind": display_kind,
                "module": source["module"],
                "module_id": stable_id("module", source["module"]),
                "layer": source["layer"],
                "signature": signature,
                "docstring": clean_public_text(pending_doc),
                "source_id": source["id"],
                "source_range": {"start_line": index + 1, "end_line": end_line},
                "selection_range": None,
                "body_available": body_available,
                "provenance": "source_index",
                "type_dependencies": [],
                "body_dependencies": [],
                "url": f"/reference/declarations/{declaration_id}",
                "title": full_name,
                "summary": docstring or fallback_summary,
                "description": docstring or fallback_detail,
                "breadcrumbs": [
                    {"label": "Reference", "href": "/reference"},
                    {"label": source["module"], "href": f"/reference/modules/{stable_id('module', source['module'])}"},
                ],
                "sections": [
                    {"id": f"{declaration_id}-signature", "title": "Source signature", "blocks": [{"kind": "code", "language": "lean", "code": signature, "caption": full_name, "sourceHref": f"/source/{source['id']}?start={index + 1}&end={end_line}"}]},
                    {"id": f"{declaration_id}-documentation", "title": "Documentation", "blocks": [{"kind": "prose", "html": markdown_to_safe_html(docstring or fallback_detail)}]},
                    {"id": f"{declaration_id}-catalog-facts", "title": "Catalog facts", "blocks": [{
                        "kind": "table",
                        "caption": "Conservatively indexed source structure",
                        "columns": [
                            {"key": "field", "label": "Field"},
                            {"key": "value", "label": "Recorded value"},
                        ],
                        "rows": [
                            {"field": "Qualified name", "value": full_name},
                            {"field": "Declaration kind", "value": display_kind},
                            {"field": "Module", "value": source["module"]},
                            {"field": "Layer", "value": source["layer"]},
                            {"field": "Signature shape", "value": signature_shape},
                            {"field": "Body metadata", "value": "source definition present"},
                            {"field": "Dependency metadata", "value": "not exported by the source index"},
                            {"field": "Source binding", "value": f"hash-verified lines {index + 1}–{end_line}"},
                        ],
                    }]},
                ],
                "canonicalPath": f"/reference/declarations/{declaration_id}",
            })
            existing_names.add(full_name)
            pending_doc = ""
    return result


def build_modules(
    root: Path,
    sources: list[dict[str, Any]],
    declarations: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    declarations_by_module: dict[str, list[dict[str, Any]]] = {}
    for declaration in declarations:
        declarations_by_module.setdefault(declaration["module"], []).append(declaration)
    modules: list[dict[str, Any]] = []
    public_module_names = {source["module"] for source in sources}
    for source in sources:
        path = root / source["path"]
        text = path.read_text(encoding="utf-8")
        imports = sorted(set(re.findall(r"^import\s+([^\s]+)", text, re.MULTILINE)))
        summary = module_doc(text)
        module_id = stable_id("module", source["module"])
        module_declarations = sorted(declarations_by_module.get(source["module"], []), key=lambda item: item["name"])
        declaration_cards = [
            {
                "title": declaration["name"],
                "summary": declaration["summary"],
                "href": declaration["canonicalPath"],
                "eyebrow": declaration["kind"],
                "meta": f"{declaration['module']} · stable declaration link",
            }
            for declaration in module_declarations
        ]
        source_href = f"/source/{source['id']}"
        internal_imports = [imported for imported in imports if imported in public_module_names]
        umbrella_imports = [imported for imported in imports if imported == "Hypostructure"]
        external_imports = [imported for imported in imports if imported not in public_module_names and imported != "Hypostructure"]
        modules.append({
            "id": module_id,
            "name": source["module"],
            "title": source["module"].replace("Hypostructure.", "").replace(".", " · "),
            "layer": source["layer"],
            "kind": source["kind"],
            "summary": summary or f"Public Lean module {source['module']}.",
            "imports": imports,
            "source_id": source["id"],
            "declaration_ids": [declaration["id"] for declaration in module_declarations],
            "url": f"/reference/modules/{module_id}",
            "breadcrumbs": [{"label": "Reference", "href": "/reference"}],
            "sections": [
                {"id": f"{module_id}-overview", "title": "Module overview", "blocks": [{"kind": "prose", "html": markdown_to_safe_html(summary or f"Public Lean module `{source['module']}`.")}]},
                {"id": f"{module_id}-imports", "title": "Direct imports", "blocks": [
                    {"kind": "links", "items": [{"label": imported, "href": f"/reference/modules/{stable_id('module', imported)}"} for imported in internal_imports]},
                    {"kind": "table", "caption": "Framework umbrella imports", "columns": [{"key": "module", "label": "Module"}], "rows": [{"module": imported} for imported in umbrella_imports]},
                    {"kind": "table", "caption": "External trust-boundary imports", "columns": [{"key": "module", "label": "Module"}], "rows": [{"module": imported} for imported in external_imports]},
                ]},
                {"id": f"{module_id}-declarations", "title": "Public declarations", "summary": "Compiler-generated eliminators and internal helpers are intentionally excluded from the API-facing catalog.", "blocks": [{"kind": "cards", "items": declaration_cards, "columns": 3}]},
                {"id": f"{module_id}-source", "title": "Source", "blocks": [{"kind": "links", "items": [{"label": source["path"], "href": source_href, "description": source["sha256"]}]}]},
            ],
            "canonicalPath": f"/reference/modules/{module_id}",
        })
    return sorted(modules, key=lambda item: item["name"])


def related_ids(declarations: list[dict[str, Any]], prefix: str) -> list[str]:
    return [item["id"] for item in declarations if item["name"].startswith(prefix)]


def build_cts(
    curated: list[dict[str, Any]],
    raw: dict[str, Any],
    modules: list[dict[str, Any]],
    declarations: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    raw_cts = raw.get("ct_catalog")
    if raw_cts != [f"CT{index}" for index in range(1, 18)]:
        raise ValueError("compiled CT catalog is missing the stable CT1-CT17 sequence")
    module_by_name = {module["name"]: module for module in modules}
    declaration_by_name = {declaration["name"]: declaration for declaration in declarations}
    result = []
    for guide in curated:
        ct_id = guide["id"]
        number = int(ct_id[2:])
        prefix = f"Hypostructure.{ct_id}."
        module_ids = sorted(module["id"] for module in modules if module["name"].startswith(prefix))
        fixture_name = f"Hypostructure.Fixtures.{ct_id}"
        adapter_names = [f"Hypostructure.Graph.{ct_id}", f"Hypostructure.PDE.{ct_id}"]
        entry_module_names = [
            f"Hypostructure.{ct_id}.{suffix}"
            for suffix in ("Spec", "Capability", "Execution", "Automation")
        ]
        entry_modules = [module_by_name[name] for name in entry_module_names if name in module_by_name]
        entrypoint_names = [
            f"Hypostructure.{ct_id}.{name}"
            for name in ("Spec", "Capability", "Stage", "ExecutionResult", "execute", "run", "route")
        ]
        entrypoints = [declaration_by_name[name] for name in entrypoint_names if name in declaration_by_name]
        entrypoints.extend(
            declaration
            for name, declaration in declaration_by_name.items()
            if name.startswith(f"Hypostructure.{ct_id}.execute")
            and name.count(".") == 2
            and declaration not in entrypoints
        )
        entrypoints.sort(key=lambda declaration: declaration["name"])
        cards = []
        for name in adapter_names:
            if name in module_by_name:
                cards.append({"title": name, "summary": module_by_name[name]["summary"] or f"{ct_id} domain adapter", "href": module_by_name[name]["url"]})
        sections = [
            {"id": f"{ct_id.lower()}-contract", "title": "Contract", "blocks": [{"kind": "prose", "html": markdown_to_safe_html(guide["summary"])}]},
            {"id": f"{ct_id.lower()}-inputs", "title": "Required inputs", "blocks": [{"kind": "steps", "items": [{"title": f"Input {i}", "body": item} for i, item in enumerate(guide["inputs"], 1)]}]},
            {"id": f"{ct_id.lower()}-outcomes", "title": "Computed outcomes", "blocks": [{"kind": "steps", "items": [{"title": f"Outcome {i}", "body": item} for i, item in enumerate(guide["outcomes"], 1)]}]},
            {"id": f"{ct_id.lower()}-work", "title": "Work boundary", "blocks": [{"kind": "callout", "tone": "trust", "title": "Reference execution", "body": guide["work"]}]},
        ]
        if cards:
            sections.append({"id": f"{ct_id.lower()}-adapters", "title": "Domain adapters", "blocks": [{"kind": "cards", "items": cards, "columns": 2}]})
        sections.append({
            "id": f"{ct_id.lower()}-api-entrypoints",
            "title": "API entry points",
            "summary": "Start with the contract and capability, then call the public executor; use the complete declaration list for theorem-level details.",
            "blocks": [
                {"kind": "cards", "items": [
                    {"title": module["name"], "summary": module["summary"], "href": module["url"], "eyebrow": "Module"}
                    for module in entry_modules
                ], "columns": 4},
                {"kind": "links", "items": [
                    {"label": declaration["name"], "href": declaration["url"], "description": declaration["summary"]}
                    for declaration in entrypoints
                ]},
            ],
        })
        declaration_ids = related_ids(declarations, prefix)
        result.append({
            "id": ct_id,
            "number": number,
            "title": guide["title"],
            "summary": guide["summary"],
            "description": CT_LAYERS[ct_id],
            "inputs": guide["inputs"],
            "outcomes": guide["outcomes"],
            "work": guide["work"],
            "keywords": guide.get("keywords", []),
            "module_ids": module_ids,
            "declaration_ids": declaration_ids,
            "api_entrypoint_declaration_ids": [declaration["id"] for declaration in entrypoints],
            "fixture_module_id": module_by_name.get(fixture_name, {}).get("id"),
            "sections": sections,
            "canonicalPath": f"/core/cts/{ct_id.lower()}",
        })
    return result


def build_routes(
    raw: dict[str, Any], modules: list[dict[str, Any]], declarations: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    """Publish registry identities conservatively; attach only concrete fixture evidence."""
    module_by_name = {module["name"]: module for module in modules}
    decl_by_name = {declaration["name"]: declaration for declaration in declarations}
    concrete_profile = "CT1.residual.accumulatedLedger->CT9"
    routes: list[dict[str, Any]] = []
    for entry in raw.get("route_registry", []):
        # Domain requirement rows are not public routes. They have no typed profile.
        if entry.get("catalog_status") != "baseline":
            continue
        profile_id = entry["profile_id"]
        route_id = stable_id("route", entry["route_id"])
        is_concrete = profile_id == concrete_profile and all(
            name in decl_by_name
            for name in (
                "Hypostructure.Fixtures.RouteRegistry.transition",
                "Hypostructure.Fixtures.RouteRegistry.routed",
                "Hypostructure.Fixtures.RouteRegistry.fullLedgerPreserved",
            )
        )
        evidence = None
        if is_concrete:
            names = [
                "Hypostructure.Fixtures.RouteRegistry.transition",
                "Hypostructure.Fixtures.RouteRegistry.routed",
                "Hypostructure.Fixtures.RouteRegistry.fullLedgerPreserved",
                "Hypostructure.Fixtures.RouteRegistry.rootResidualPreserved",
                "Hypostructure.Fixtures.RouteRegistry.provenanceExact",
                "Hypostructure.Fixtures.RouteRegistry.targetExecutionExact",
            ]
            evidence = {
                "fixture_module_id": module_by_name["Hypostructure.Fixtures.RouteRegistry"]["id"],
                "declaration_ids": [decl_by_name[name]["id"] for name in names if name in decl_by_name],
                "properties": ["typed transition", "public advance", "complete predecessor preservation", "root residual preservation", "exact provenance", "target execution"],
            }
        summary = (
            "A concrete typed transition exercises discovery, target execution, provenance, and complete-ledger preservation."
            if is_concrete
            else "A stable route identity. Execution requires a separately registered typed profile and transition."
        )
        routes.append({
            "id": route_id,
            "canonical_id": entry["route_id"],
            "source_ct": entry["source_ct"],
            "target_ct": entry["target_ct"],
            "family_id": entry["family_id"],
            "profile_id": profile_id,
            "title": f"{entry['source_ct']} → {entry['target_ct']}",
            "summary": summary,
            "executable": is_concrete,
            "execution_evidence": evidence,
            "sections": [
                {"id": f"{route_id}-meaning", "title": "Route meaning", "blocks": [{"kind": "prose", "html": markdown_to_safe_html(summary)}]},
                {"id": f"{route_id}-protocol", "title": "Execution protocol", "blocks": [{"kind": "steps", "items": [
                    {"title": "Register", "body": "Bind this identity to a typed `Core.Routing.Profile` and real target capability."},
                    {"title": "Discover", "body": "Compute enabled or disabled discovery from the complete source stage."},
                    {"title": "Build target input", "body": "Derive the target executor input from discovery and the literal predecessor."},
                    {"title": "Advance", "body": "Run the target capability and extend the ledger once with exact provenance."},
                ]}]},
            ],
            "canonicalPath": f"/core/routes/{route_id}",
        })
    return sorted(routes, key=lambda route: (int(route["source_ct"][2:]), int(route["target_ct"][2:]), route["profile_id"]))


def build_examples(modules: list[dict[str, Any]]) -> list[dict[str, Any]]:
    groups = [
        ("core-fixtures", "Core fixtures", "neutral", "Hypostructure.Fixtures.", "Executable finite fixtures for shared Core and CT contracts."),
        ("graph-fixtures", "Graph fixtures", "graph", "Hypostructure.Fixtures.Graph", "Finite graph semantics, progress, boundaries, assembly, and responses."),
        ("pde-examples", "PDE examples", "pde", "HypostructurePDEExamples", "Represented finite models, coordinates, gauges, compact extraction, local-tail assembly, and Navier–Stokes registration."),
        ("erdos-application", "Erdős Problem 64", "graph", "HypostructureErdos64EG", "A dependency-ordered graph application over one accumulated proof ledger."),
    ]
    result = []
    for example_id, title, domain, prefix, summary in groups:
        selected = [module for module in modules if module["name"].startswith(prefix)]
        if example_id == "core-fixtures":
            selected = [
                module
                for module in selected
                if not module["name"].startswith("Hypostructure.Fixtures.Graph")
                and module["name"] != "Hypostructure.Fixtures.RootedReturn"
                and "PDE" not in module["name"]
            ]
        elif example_id == "graph-fixtures":
            rooted_return = next(
                (
                    module
                    for module in modules
                    if module["name"] == "Hypostructure.Fixtures.RootedReturn"
                ),
                None,
            )
            if rooted_return is not None:
                selected.append(rooted_return)
        selected.sort(key=lambda module: module["name"])
        canonical_path = f"/examples/{example_id}"
        result.append({
            "id": example_id,
            "title": title,
            "domain": domain,
            "summary": summary,
            "module_ids": [module["id"] for module in selected],
            "source_ids": [module["source_id"] for module in selected],
            "url": canonical_path,
            "breadcrumbs": [{"label": "Examples", "href": "/examples"}],
            "sections": [
                {"id": f"{example_id}-overview", "title": "What this example demonstrates", "blocks": [{"kind": "prose", "html": markdown_to_safe_html(summary)}]},
                {"id": f"{example_id}-modules", "title": "Source modules", "blocks": [{"kind": "cards", "items": [{"title": module["name"], "summary": module["summary"], "href": module["url"], "eyebrow": module["layer"]} for module in selected], "columns": 3}]},
                {"id": f"{example_id}-trust", "title": "Evidence boundary", "blocks": [{"kind": "callout", "tone": "trust", "title": "Source-derived example", "body": "Every card links to a hash-verified, content-bound Hypostructure-native source module and its declarations."}]},
            ],
            "canonicalPath": canonical_path,
        })
    return result


def build_erdos(
    root: Path, sources: list[dict[str, Any]], declarations: list[dict[str, Any]]
) -> dict[str, Any]:
    """Build the complete paper topology and attach native Lean evidence.

    The paper-derived predecessor relation and implementation evidence have
    deliberately separate authorities. The original paper is the sole source
    for mathematics and topology. The curated table contains migration
    normalizations and observed legacy CT imports; neither is promoted to a
    paper statement. Discovered native sources supply only implementation,
    declaration, executor, and axiom-audit evidence.
    """
    topology_path = root / ERDOS_PAPER_TOPOLOGY
    required_fields = {
        "node_id",
        "paper_ref",
        "direct_predecessors",
        "normalized_input",
        "normalized_outcomes",
        "observed_legacy_ct_ids",
        "new_file",
        "new_kernel",
        "parity_status",
        "math_status",
        "work_status",
        "web_evidence",
        "status",
        "blocker",
    }
    with topology_path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None or not required_fields <= set(reader.fieldnames):
            raise ValueError("Erdős migration inventory is missing required fields")
        paper_rows = [
            {field: (row.get(field) or "").strip() for field in required_fields}
            for row in reader
        ]

    paper_numbers = [int(row["node_id"]) for row in paper_rows]
    if paper_numbers != list(range(1, 158)):
        raise ValueError("Erdős paper topology must contain nodes 1 through 157 exactly once")
    for row in paper_rows:
        if not all(
            row[field]
            for field in ("paper_ref", "normalized_input", "normalized_outcomes")
        ):
            raise ValueError(f"Erdős node {row['node_id']} has an incomplete paper contract")
        vocabularies = {
            "new_kernel": ERDOS_NEW_KERNEL_STATUSES,
            "parity_status": ERDOS_PARITY_STATUSES,
            "math_status": ERDOS_MATH_STATUSES,
            "work_status": ERDOS_WORK_STATUSES,
            "status": ERDOS_MIGRATION_STATUSES,
        }
        for field, allowed in vocabularies.items():
            if row[field] not in allowed:
                raise ValueError(
                    f"invalid {field} for Erdős node {row['node_id']}: {row[field]!r}"
                )
    paper_number_set = set(paper_numbers)

    node_sources: dict[int, dict[str, Any]] = {}
    pattern = re.compile(r"/Node(\d+)\.lean$")
    for source in sources:
        match = pattern.search(source["path"])
        if match and "hypostructure_erdos_64_eg" in source["path"]:
            number = int(match.group(1))
            if number in node_sources:
                raise ValueError(f"multiple native Erdős sources for node {number}")
            node_sources[number] = source
    decl_by_module: dict[str, list[dict[str, Any]]] = {}
    for declaration in declarations:
        decl_by_module.setdefault(declaration["module"], []).append(declaration)
    nodes: list[dict[str, Any]] = []
    edges: list[dict[str, Any]] = []
    for order, row in enumerate(paper_rows):
        number = int(row["node_id"])
        incoming = [
            int(value)
            for value in row["direct_predecessors"].split("|")
            if value
        ]
        if (
            incoming != sorted(set(incoming))
            or number in incoming
            or any(predecessor not in paper_number_set for predecessor in incoming)
        ):
            raise ValueError(f"invalid direct predecessors for Erdős node {number}")

        # A handful of original branches intentionally join a later-numbered
        # node.  These assertions prevent accidental numeric-order rewrites.
        source = node_sources.get(number)
        text = (
            (root / source["path"]).read_text(encoding="utf-8")
            if source is not None
            else ""
        )
        module_declarations = (
            decl_by_module.get(source["module"], []) if source is not None else []
        )
        expected_source_path = (
            "examples/hypostructure_erdos_64_eg/HypostructureErdos64EG/"
            f"Node{number}.lean"
        )
        direct_source_matches = (
            source is not None
            and source["path"] == expected_source_path
            and row["new_file"] == expected_source_path
        )
        direct_olean = (
            root
            / "examples/hypostructure_erdos_64_eg/.lake/build/lib/lean/"
            / "HypostructureErdos64EG"
            / f"Node{number}.olean"
        )
        direct_kernel_fresh = bool(
            direct_source_matches
            and direct_olean.is_file()
            and direct_olean.stat().st_mtime_ns
            >= (root / expected_source_path).stat().st_mtime_ns
        )
        has_compiled_direct_declaration = bool(module_declarations)
        implementation_status = (
            "ported"
            if direct_kernel_fresh and has_compiled_direct_declaration
            else "paper-pending"
        )
        implementation_status_label = (
            "Ported to Hypostructure"
            if implementation_status == "ported"
            else "Original paper node not yet ported"
        )
        closed = bool(
            row["status"] == "migrated_closed"
            and row["new_kernel"] == "fresh"
            and direct_kernel_fresh
            and has_compiled_direct_declaration
        )
        executor = next(
            (
                item
                for item in module_declarations
                if item["short_name"] == f"node{number}"
                and item["kind"] in {"def", "definition"}
            ),
            None,
        )
        audits = sorted(
            set(re.findall(r"^#print axioms\s+([^\s]+)", text, re.MULTILINE))
        )
        normalized_input = row["normalized_input"]
        normalized_outcome = row["normalized_outcomes"]
        public_blocker = clean_public_text(row["blocker"])
        if row["blocker"] and not public_blocker:
            public_blocker = "Internal evidence blocker recorded."
        observed_ct_ids = [
            value
            for value in row["observed_legacy_ct_ids"].split("|")
            if value
        ]
        if len(observed_ct_ids) != len(set(observed_ct_ids)) or any(
            ct_id not in CT_LAYERS for ct_id in observed_ct_ids
        ):
            raise ValueError(f"invalid CT labels for Erdős node {number}")
        summary = normalized_outcome
        node_id = f"node-{number}"
        node_url = f"/erdos/nodes/{node_id}"
        sections = [
            {
                "id": f"{node_id}-contract",
                "title": "Original source authority",
                "blocks": [
                    {
                        "kind": "table",
                        "columns": [
                            {"key": "field", "label": "Field"},
                            {"key": "value", "label": "Value"},
                        ],
                        "rows": [
                            {"field": "Paper reference", "value": row["paper_ref"]},
                        ],
                    },
                    {
                        "kind": "callout",
                        "tone": "trust",
                        "title": "Binding requirement source",
                        "body": (
                            "Read the exact node statement, quantified requirements, "
                            "branch alternatives, and edges in original_erdos_64_proof.tex "
                            "before consulting any Lean implementation."
                        ),
                    },
                ],
            },
            {
                "id": f"{node_id}-native-status",
                "title": "Native status evidence",
                "blocks": [
                    {
                        "kind": "table",
                        "columns": [
                            {"key": "field", "label": "Field"},
                            {"key": "value", "label": "Value"},
                        ],
                        "rows": [
                            {"field": "Implementation diagram status", "value": implementation_status_label},
                            {"field": "Direct native source", "value": "Present" if direct_source_matches else "Not present"},
                            {"field": "Fresh compiled object", "value": "Present" if direct_kernel_fresh else "Not present"},
                            {"field": "Compiled declarations", "value": "Present" if has_compiled_direct_declaration else "Not present"},
                            {"field": "Blocker", "value": public_blocker or "None recorded"},
                        ],
                    },
                    {
                        "kind": "callout",
                        "tone": "trust" if implementation_status == "ported" else "warning",
                        "title": "Direct native implementation evidence",
                        "body": (
                            "This node has a direct native Hypostructure NodeX module with "
                            "fresh compiled evidence and declarations."
                            if implementation_status == "ported"
                            else "This node is still shown as a paper-side node in the "
                            "comparison diagram until a direct native Hypostructure NodeX "
                            "module supplies fresh compiled evidence and declarations."
                        ),
                    },
                ],
            },
            {
                "id": f"{node_id}-normalization",
                "title": "Working normalization",
                "blocks": [
                    {
                        "kind": "callout",
                        "tone": "info",
                        "title": "Non-authoritative inventory",
                        "body": (
                            "These normalized labels are working bookkeeping. They "
                            "cannot repair, redirect, or replace the original paper."
                        ),
                    },
                    {
                        "kind": "table",
                        "columns": [
                            {"key": "field", "label": "Field"},
                            {"key": "value", "label": "Value"},
                        ],
                        "rows": [
                            {"field": "Normalized input", "value": normalized_input},
                            {"field": "Normalized outcome", "value": normalized_outcome},
                        ],
                    },
                ],
            },
            {
                "id": f"{node_id}-predecessors",
                "title": "Direct predecessors",
                "blocks": [
                    (
                        {
                            "kind": "links",
                            "items": [
                                {
                                    "label": f"Node {predecessor}",
                                    "href": f"/erdos/nodes/node-{predecessor}",
                                }
                                for predecessor in incoming
                            ],
                        }
                        if incoming
                        else {
                            "kind": "callout",
                            "tone": "info",
                            "title": "Root node",
                            "body": "Node 1 is the sole root of the paper proof topology.",
                        }
                    )
                ],
            },
        ]
        if observed_ct_ids:
            sections.append({
                "id": f"{node_id}-capabilities",
                "title": "Observed implementation CT evidence",
                "blocks": [
                    {
                        "kind": "links",
                        "items": [
                            {
                                "label": ct_id,
                                "href": f"/core/cts/{ct_id.lower()}",
                                "description": CT_LAYERS[ct_id],
                            }
                            for ct_id in observed_ct_ids
                        ],
                    },
                    {
                        "kind": "callout",
                        "tone": "info",
                        "title": "Implementation evidence only",
                        "body": (
                            "These CT labels come from the earlier kernel-checked "
                            "NodeX.lean dependency cone. They are not assigned by the "
                            "paper and are consulted only after the original contract."
                        ),
                    },
                ],
            })
        if source is not None:
            sections.extend(
                [
                    {
                        "id": f"{node_id}-source",
                        "title": "Native implementation evidence",
                        "blocks": [
                            {
                                "kind": "cards",
                                "items": [
                                    {
                                        "title": source["module"],
                                        "summary": "Open the native Hypostructure source module.",
                                        "href": f"/source/{source['id']}",
                                        "eyebrow": "Lean source",
                                    }
                                ],
                                "columns": 2,
                            },
                            {
                                "kind": "cards",
                                "items": [
                                    {
                                        "title": item["short_name"],
                                        "summary": item["summary"],
                                        "href": item["url"],
                                        "eyebrow": item["kind"],
                                    }
                                    for item in module_declarations
                                ],
                                "columns": 3,
                            },
                        ],
                    },
                    {
                        "id": f"{node_id}-audit",
                        "title": "Trust endpoints",
                        "blocks": [
                            {
                                "kind": "callout",
                                "tone": "trust",
                                "title": "Axiom audit",
                                "body": ", ".join(audits)
                                if audits
                                else "This native node module has no explicit axiom-audit command.",
                            }
                        ],
                    },
                ]
            )
        nodes.append({
            "id": node_id,
            "number": number,
            "label": f"Node {number}",
            "summary": summary,
            "paper_ref": row["paper_ref"],
            "normalized_input": normalized_input,
            "normalized_outcomes": normalized_outcome,
            "observed_ct_ids": observed_ct_ids,
            "ct_provenance": "observed-node-import-evidence",
            "requirements_authority": "original_erdos_64_proof.tex",
            "normalization_authority": "non-authoritative-working-inventory",
            "new_kernel": row["new_kernel"],
            "parity_status": row["parity_status"],
            "math_status": row["math_status"],
            "work_status": row["work_status"],
            "status": row["status"],
            "blocker": public_blocker,
            "web_evidence": row["web_evidence"],
            "direct_kernel_fresh": direct_kernel_fresh,
            "has_compiled_direct_declaration": has_compiled_direct_declaration,
            "implementation_status": implementation_status,
            "implementation_status_label": implementation_status_label,
            "closed": closed,
            **(
                {
                    "source_id": source["id"],
                    "module_id": stable_id("module", source["module"]),
                    "declaration_ids": [
                        item["id"] for item in module_declarations
                    ],
                    "executor_declaration_id": executor["id"]
                    if executor
                    else None,
                    "axiom_audit_endpoints": audits,
                }
                if source is not None
                else {}
            ),
            "incoming": [f"node-{value}" for value in incoming],
            "position": {"x": (order % 8) * 230, "y": (order // 8) * 170},
            "url": node_url,
            "title": f"Erdős node {number}",
            "description": summary,
            "breadcrumbs": [{"label": "Erdős", "href": "/erdos"}],
            "sections": sections,
            "canonicalPath": node_url,
        })
        for predecessor in incoming:
            edges.append({
                "id": f"node-{predecessor}-to-{number}",
                "source": f"node-{predecessor}",
                "target": node_id,
                "label": "direct predecessor",
            })
    edge_pairs = {(edge["source"], edge["target"]) for edge in edges}
    required_edges = {
        ("node-66", "node-65"),
        ("node-102", "node-89"),
        ("node-59", "node-60"),
        ("node-59", "node-61"),
    }
    if not required_edges <= edge_pairs:
        raise ValueError("Erdős paper topology is missing a required non-linear edge")
    if len(edges) != 169 or len(edge_pairs) != 169:
        raise ValueError("Erdős paper topology must contain exactly 169 direct edges")
    roots = [node["id"] for node in nodes if not node["incoming"]]
    if roots != ["node-1"]:
        raise ValueError("Erdős paper topology must have node 1 as its sole root")
    closed_node_ids = {node["id"] for node in nodes if node["closed"]}
    frontier_node_ids = {
        node["id"]
        for node in nodes
        if node["id"] not in closed_node_ids
        and any(predecessor in closed_node_ids for predecessor in node["incoming"])
    }
    for node in nodes:
        node["presentation_status"] = (
            "closed"
            if node["id"] in closed_node_ids
            else "frontier"
            if node["id"] in frontier_node_ids
            else "implemented"
            if "source_id" in node
            else "missing"
        )
    implementation_legend = [
        {"label": "Ported to Hypostructure", "kind": "ported"},
        {"label": "Original paper node not yet ported", "kind": "paper-pending"},
    ]
    ported_count = sum(
        1 for node in nodes if node["implementation_status"] == "ported"
    )
    diagram_graphs: list[dict[str, Any]] = []
    nodes_by_number = {node["number"]: node for node in nodes}
    for label, first, last in ERDOS_DIAGRAM_PARTS:
        part_nodes = [
            nodes_by_number[number]
            for number in range(first, last + 1)
        ]
        part_node_ids = {node["id"] for node in part_nodes}
        columns = 6 if len(part_nodes) > 18 else 5
        diagram_graphs.append({
            "kind": "graph",
            "title": f"Original proof diagram {label}: nodes {first}–{last}",
            "description": (
                "Green nodes are already ported to the current Hypostructure "
                "implementation. Yellow nodes are present in the original paper "
                "diagram and not yet direct native Hypostructure nodes. Arrows "
                "shown here are direct predecessor edges internal to this paper "
                "diagram panel."
            ),
            "nodes": [
                {
                    "id": node["id"],
                    "label": node["label"],
                    "x": (index % columns) * 210,
                    "y": (index // columns) * 150,
                    "kind": node["implementation_status"],
                    "summary": node["summary"],
                    "href": node["url"],
                }
                for index, node in enumerate(part_nodes)
            ],
            "edges": [
                edge
                for edge in edges
                if edge["source"] in part_node_ids and edge["target"] in part_node_ids
            ],
            "legend": implementation_legend,
        })
    return {
        "id": "erdos-problem-64",
        "title": "Erdős Problem 64",
        "summary": "The complete 157-node proof topology from the immutable paper, enriched with native Hypostructure implementation evidence.",
        "nodes": nodes,
        "edges": edges,
        "root_node_ids": roots,
        "implementation_counts": {
            "ported": ported_count,
            "paper_pending": len(nodes) - ported_count,
            "total": len(nodes),
        },
        "diagram_graphs": diagram_graphs,
        "graph": {
            "kind": "graph",
            "title": "Original paper vs Hypostructure implementation",
            "description": f"All 157 nodes and 169 arrows come from the original paper topology. Green nodes have direct native Hypostructure compiled evidence; yellow nodes remain paper-side nodes in this implementation view. Current count: {ported_count} green, {len(nodes) - ported_count} yellow.",
            "nodes": [{"id": node["id"], "label": node["label"], "x": node["position"]["x"], "y": node["position"]["y"], "kind": node["implementation_status"], "summary": node["summary"], "href": node["url"]} for node in nodes],
            "edges": edges,
            "legend": implementation_legend,
        },
    }


def plain_text(value: str) -> str:
    return re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", value)).strip()


def content_block_text(block: dict[str, Any]) -> str:
    kind = block.get("kind")
    if kind == "prose":
        return plain_text(block.get("html", ""))
    if kind == "cards":
        return " ".join(
            f"{item.get('title', '')} {item.get('summary', '')} {item.get('eyebrow', '')} {item.get('meta', '')}"
            for item in block.get("items", [])
        )
    if kind == "callout":
        return f"{block.get('title', '')} {block.get('body', '')}"
    if kind == "steps":
        return " ".join(
            f"{item.get('title', '')} {item.get('body', '')}"
            for item in block.get("items", [])
        )
    if kind == "code":
        return f"{block.get('caption', '')} {block.get('code', '')}"
    if kind == "math":
        return f"{block.get('label', '')} {block.get('latex', '')}"
    if kind == "table":
        return " ".join([
            str(block.get("caption", "")),
            *(str(column.get("label", "")) for column in block.get("columns", [])),
            *(" ".join(str(value) for value in row.values()) for row in block.get("rows", [])),
        ])
    if kind == "graph":
        return " ".join([
            str(block.get("title", "")),
            str(block.get("description", "")),
            *(f"{node.get('label', '')} {node.get('summary', '')}" for node in block.get("nodes", [])),
            *(str(edge.get("label", "")) for edge in block.get("edges", [])),
        ])
    if kind == "links":
        return " ".join(
            f"{item.get('label', '')} {item.get('description', '')}"
            for item in block.get("items", [])
        )
    return ""


def build_search_documents(
    pages: dict[str, Any], cts: list[dict[str, Any]], routes: list[dict[str, Any]],
    examples: list[dict[str, Any]], modules: list[dict[str, Any]],
    declarations: list[dict[str, Any]], erdos: dict[str, Any],
) -> list[dict[str, Any]]:
    docs: list[dict[str, Any]] = []
    for page in pages.values():
        body = " ".join(
            content_block_text(block)
            for section in page["sections"]
            for block in section["blocks"]
        )
        docs.append({"id": f"page:{page['id']}", "title": page["title"], "summary": page["summary"], "body": body, "url": page["canonicalPath"], "kind": "page", "facets": {"section": page["id"]}})
    for ct in cts:
        docs.append({"id": f"ct:{ct['id']}", "title": f"{ct['id']} · {ct['title']}", "summary": ct["summary"], "body": " ".join([*ct["inputs"], *ct["outcomes"], ct["work"]]), "keywords": ct.get("keywords", []), "url": ct["canonicalPath"], "kind": "ct", "module": ct["id"], "facets": {"section": "core", "ct": ct["id"]}})
    for route in routes:
        docs.append({"id": f"route:{route['id']}", "title": route["title"], "summary": route["summary"], "body": route["profile_id"], "url": route["canonicalPath"], "kind": "route", "facets": {"section": "core", "source_ct": route["source_ct"], "target_ct": route["target_ct"]}})
    for example in examples:
        docs.append({"id": f"example:{example['id']}", "title": example["title"], "summary": example["summary"], "body": example["summary"], "url": example["url"], "kind": "example", "facets": {"section": "examples", "domain": example["domain"]}})
    for module in modules:
        docs.append({"id": f"module:{module['id']}", "title": module["name"], "summary": module["summary"] or "Lean module", "body": " ".join(module["imports"]), "url": module["url"], "kind": "module", "module": module["name"], "facets": {"layer": module["layer"], "source_kind": module["kind"]}})
    for declaration in declarations:
        docs.append({"id": f"declaration:{declaration['id']}", "title": declaration["name"], "summary": declaration["docstring"] or declaration["signature"], "body": declaration["signature"], "url": declaration["url"], "kind": "declaration", "module": declaration["module"], "facets": {"layer": declaration["layer"], "declaration_kind": declaration["kind"]}})
    for node in erdos["nodes"]:
        docs.append({
            "id": f"erdos:{node['id']}",
            "title": node["label"],
            "summary": node["summary"],
            "body": " ".join([
                node["paper_ref"],
                node["normalized_input"],
                node["normalized_outcomes"],
                *node["observed_ct_ids"],
                *node.get("axiom_audit_endpoints", []),
            ]),
            "url": node["url"],
            "kind": "erdos_node",
            "module": f"Node {node['number']}",
            "facets": {"section": "erdos"},
        })
    return sorted(docs, key=lambda item: item["id"])


def validate_publication(value: Any, path: str = "snapshot") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if any(word in key.casefold() for word in PUBLICATION_WORDS):
                raise ValueError(f"publication vocabulary in key {path}.{key}")
            validate_publication(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            validate_publication(child, f"{path}[{index}]")
    elif isinstance(value, str) and any(word in value.casefold() for word in PUBLICATION_WORDS):
        raise ValueError(f"publication vocabulary in value {path}")


def validate_snapshot(snapshot: dict[str, Any]) -> None:
    required = {"schema_version", "site", "pages", "modules", "declarations", "cts", "routes", "examples", "erdos", "sources", "search_documents", "trust"}
    missing = required - snapshot.keys()
    if missing:
        raise ValueError(f"snapshot missing keys: {sorted(missing)}")
    if set(snapshot["pages"]) != {"home", "start", "core", "graph", "pde", "examples", "erdos", "cts", "routes", "reference"}:
        raise ValueError("snapshot pages do not match the public route set")
    if [ct["id"] for ct in snapshot["cts"]] != [f"CT{index}" for index in range(1, 18)]:
        raise ValueError("snapshot CT order is not CT1-CT17")
    ids = [source["id"] for source in snapshot["sources"]]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate source IDs")
    allowed = tuple(path.as_posix() + "/" for path in SOURCE_ROOTS)
    for source in snapshot["sources"]:
        if not source["path"].startswith(allowed) or not source["path"].endswith(".lean"):
            raise ValueError(f"source outside public roots: {source['path']}")
    source_ids = set(ids)
    internal_paths = {"/search"}
    internal_paths.update(page["canonicalPath"] for page in snapshot["pages"].values())
    for collection in ("cts", "routes", "examples", "modules", "declarations"):
        internal_paths.update(record["canonicalPath"] for record in snapshot[collection])
    internal_paths.update(
        node["canonicalPath"] for node in snapshot["erdos"]["nodes"]
    )

    def validate_links(value: Any, location: str = "snapshot") -> None:
        if isinstance(value, dict):
            for key, child in value.items():
                if key in {"href", "sourceHref"} and isinstance(child, str):
                    if child.startswith("/api/v2/sources/"):
                        raise ValueError(f"{location}.{key} bypasses the in-app source route")
                    if child.startswith("/source/"):
                        source_id = child.split("?", 1)[0].removeprefix("/source/")
                        if not source_id or "/" in source_id or source_id not in source_ids:
                            raise ValueError(f"{location}.{key} references an unknown source")
                    elif child.startswith("/"):
                        internal_path = child.split("?", 1)[0].split("#", 1)[0]
                        if internal_path not in internal_paths:
                            raise ValueError(
                                f"{location}.{key} references an unknown internal route: {child}"
                            )
                validate_links(child, f"{location}.{key}")
        elif isinstance(value, list):
            for index, child in enumerate(value):
                validate_links(child, f"{location}[{index}]")

    validate_links(snapshot)
    def require_page_view(record: dict[str, Any], location: str) -> None:
        for field in ("id", "title", "summary"):
            if not isinstance(record.get(field), str) or not record[field].strip():
                raise ValueError(f"{location} has no nonempty {field}")
        if not isinstance(record.get("sections"), list):
            raise ValueError(f"{location} has no sections array")

    for page_id, page in snapshot["pages"].items():
        require_page_view(page, f"pages.{page_id}")
    for collection in ("cts", "routes", "examples", "modules", "declarations"):
        for index, record in enumerate(snapshot[collection]):
            require_page_view(record, f"{collection}[{index}]")
    for index, node in enumerate(snapshot["erdos"]["nodes"]):
        require_page_view(node, f"erdos.nodes[{index}]")
    declaration_paths = {record["canonicalPath"] for record in snapshot["declarations"]}
    for index, declaration in enumerate(snapshot["declarations"]):
        for section in declaration["sections"]:
            if not section["id"].endswith("-dependencies"):
                continue
            for block in section["blocks"]:
                for item in block.get("items", []):
                    if item.get("href") not in declaration_paths:
                        raise ValueError(
                            f"declarations[{index}] links an unpublished dependency: {item.get('href')}"
                        )
    for index, document in enumerate(snapshot["search_documents"]):
        for field in ("id", "title", "url", "kind"):
            if not isinstance(document.get(field), str) or not document[field]:
                raise ValueError(f"search_documents[{index}] has no {field}")
    validate_publication(snapshot)


def run_compiled_export(root: Path, raw_path: Path) -> None:
    exporter = root / "hypostructure/Hypostructure/Canonical/WebExport.lean"
    if not exporter.exists():
        raise FileNotFoundError("compiled declaration exporter is missing: hypostructure/Hypostructure/Canonical/WebExport.lean")
    env = os.environ.copy()
    env["HYPOSTRUCTURE_WEB_DECLARATIONS_EXPORT"] = os.path.relpath(raw_path, root / "hypostructure")
    command = ["lake", "env", "lean", "Hypostructure/Canonical/WebExport.lean"]
    completed = subprocess.run(command, cwd=root / "hypostructure", env=env, text=True, capture_output=True)
    if completed.returncode:
        raise RuntimeError(
            "compiled declaration export failed; run `cd hypostructure && "
            "HYPOSTRUCTURE_WEB_DECLARATIONS_EXPORT=../generated/hypostructure/web/declarations.raw.json "
            "lake env lean Hypostructure/Canonical/WebExport.lean`\n" + completed.stderr
        )
    if not raw_path.exists():
        raise RuntimeError("compiled declaration exporter completed without producing its JSON artifact")


def build_snapshot(root: Path, raw_path: Path) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    raw = json.loads(raw_path.read_text(encoding="utf-8"))
    if raw.get("artifact_type") != "hypostructure_declaration_catalog":
        raise ValueError("unexpected declaration catalog artifact_type")
    sources, path_to_id, _module_to_source = discover_sources(root)
    declarations, name_to_id = normalize_declarations(raw, path_to_id)
    public_compiled_declaration_count = len(declarations)
    declarations.extend(source_declarations(root, sources, set(name_to_id)))
    declarations.sort(key=lambda item: item["name"])
    modules = build_modules(root, sources, declarations)
    module_urls = {module["name"]: module["url"] for module in modules}
    declaration_urls = {
        declaration["name"]: declaration["url"] for declaration in declarations
    }

    content_root = root / CONTENT_ROOT
    page_blocks = json.loads((content_root / "blocks.json").read_text(encoding="utf-8"))
    pages: dict[str, Any] = {}
    for page_id in ("home", "start", "core", "graph", "pde", "examples", "erdos", "cts", "routes", "reference"):
        page = parse_markdown_page(content_root / "pages" / f"{page_id}.md", page_id)
        add_curated_blocks(
            page, page_blocks.get(page_id, []), content_root,
            module_urls, declaration_urls,
            prepend=page_id in {"home", "start", "graph", "pde"},
        )
        pages[page_id] = page
    pages["cts"]["canonicalPath"] = "/core/cts"
    pages["cts"]["breadcrumbs"] = [{"label": "Core", "href": "/core"}]
    pages["routes"]["canonicalPath"] = "/core/routes"
    pages["routes"]["breadcrumbs"] = [{"label": "Core", "href": "/core"}]
    curated_cts = json.loads((content_root / "cts.json").read_text(encoding="utf-8"))
    cts = build_cts(curated_cts, raw, modules, declarations)
    routes = build_routes(raw, modules, declarations)
    examples = build_examples(modules)
    erdos = build_erdos(root, sources, declarations)

    pages["cts"]["sections"].append({
        "id": "ct-catalog",
        "title": "All CT contracts",
        "blocks": [{"kind": "cards", "columns": 3, "items": [
            {"title": f"{ct['id']} · {ct['title']}", "summary": ct["summary"], "href": ct["canonicalPath"], "meta": ct["work"]}
            for ct in cts
        ]}],
    })
    pages["routes"]["sections"].extend([
        {"id": "route-counts", "title": "Route evidence", "blocks": [{"kind": "stats", "items": [
            {"label": "Stable identities", "value": len(routes)},
            {"label": "Concrete fixture executions", "value": sum(1 for route in routes if route["executable"])},
        ]}]},
        {"id": "route-catalog", "title": "Registered route identities", "blocks": [{"kind": "cards", "columns": 3, "items": [
            {"title": route["title"], "summary": route["summary"], "href": route["canonicalPath"], "meta": route["profile_id"]}
            for route in routes
        ]}]},
    ])
    pages["reference"]["sections"].extend([
        {"id": "reference-counts", "title": "Compiled catalog", "blocks": [{"kind": "stats", "items": [
            {"label": "Modules", "value": len(modules)},
            {"label": "Declarations", "value": len(declarations)},
            {"label": "Source files", "value": len(sources)},
        ]}]},
        {"id": "module-index", "title": "Module index", "blocks": [{"kind": "cards", "columns": 3, "items": [
            {"title": module["name"], "summary": module["summary"], "href": module["url"], "eyebrow": module["layer"], "meta": f"{len(module['declaration_ids'])} declarations"}
            for module in modules
        ]}]},
    ])
    pages["examples"]["sections"].append({
        "id": "example-catalog", "title": "Compiled examples", "blocks": [{"kind": "cards", "columns": 2, "items": [
            {"title": example["title"], "summary": example["summary"], "href": example["canonicalPath"], "eyebrow": example["domain"]}
            for example in examples
        ]}],
    })
    pages["erdos"]["sections"].append({
        "id": "erdos-paper-comparison",
        "title": "Original paper diagrams vs current implementation",
        "summary": (
            "These panels reuse the original proof-diagram grouping. Green nodes "
            "are already direct native Hypostructure implementations; yellow nodes "
            "are paper nodes not yet ported into the current implementation."
        ),
        "blocks": [
            {
                "kind": "stats",
                "items": [
                    {
                        "label": "Ported nodes",
                        "value": str(erdos["implementation_counts"]["ported"]),
                        "detail": "Direct native Hypostructure nodes with fresh compiled evidence.",
                    },
                    {
                        "label": "Paper nodes not yet ported",
                        "value": str(erdos["implementation_counts"]["paper_pending"]),
                        "detail": "Nodes present in the original proof diagrams and still yellow here.",
                    },
                    {
                        "label": "Original paper nodes",
                        "value": str(erdos["implementation_counts"]["total"]),
                        "detail": "Complete node set in the proof dependency topology.",
                    },
                ],
            },
            *erdos["diagram_graphs"],
        ],
    })
    pages["erdos"]["sections"].append(
        {"id": "erdos-topology", "title": "Full proof topology", "blocks": [erdos["graph"]]}
    )
    for label, first, last in ERDOS_DIAGRAM_PARTS:
        part_nodes = [
            node for node in erdos["nodes"] if first <= node["number"] <= last
        ]
        pages["erdos"]["sections"].append({
            "id": f"erdos-node-index-{label.lower()}",
            "title": f"Part {label} · Nodes {first}–{last}",
            "blocks": [{
                "kind": "cards",
                "columns": 3,
                "items": [
                    {
                        "title": node["label"],
                        "summary": node["summary"],
                        "href": node["canonicalPath"],
                        "meta": " · ".join([
                            f"{len(node['incoming'])} direct predecessors",
                            *node["observed_ct_ids"],
                        ]),
                    }
                    for node in part_nodes
                ],
            }],
        })

    verification = {
        "state": "verified",
        "label": "Verified Hypostructure sources",
        "summary": "Framework declarations come from the compiled Lean environment. Native fixture and application endpoints are conservatively source-indexed, and every source range is hash-verified and content-bound to the published snapshot.",
        "details": [
            {"label": "Declarations", "value": str(len(declarations))},
            {"label": "Source modules", "value": str(len(sources))},
            {"label": "CT contracts", "value": "17"},
        ],
    }
    snapshot: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "site": {
            "name": "Hypostructure",
            "tagline": "Typed proof programs for finite and represented mathematics",
            "navigation": [
                {"label": "Welcome", "href": "/"}, {"label": "Start", "href": "/start"},
                {"label": "Core", "href": "/core"}, {"label": "Graph", "href": "/graph"},
                {"label": "PDE", "href": "/pde"}, {"label": "Examples", "href": "/examples"},
                {"label": "Erdős", "href": "/erdos"}, {"label": "Reference", "href": "/reference"},
            ],
            "searchEnabled": True,
            "verification": verification,
        },
        "pages": pages,
        "modules": modules,
        "declarations": declarations,
        "cts": cts,
        "routes": routes,
        "examples": examples,
        "erdos": erdos,
        "sources": sources,
        "search_documents": [],
        "trust": {
            "state": "verified",
            "catalog": "compiled_lean_environment",
            "namespace": "Hypostructure",
            "source_hashes": "sha256",
            "declaration_count": len(declarations),
            "raw_compiled_declaration_count": len(raw["declarations"]),
            "public_compiled_declaration_count": public_compiled_declaration_count,
            "source_indexed_declaration_count": len(declarations) - public_compiled_declaration_count,
        },
    }
    snapshot["search_documents"] = build_search_documents(pages, cts, routes, examples, modules, declarations, erdos)
    validate_snapshot(snapshot)
    return snapshot, sources


def write_artifacts(root: Path, snapshot_path: Path, manifest_path: Path, snapshot: dict[str, Any], sources: list[dict[str, Any]]) -> None:
    snapshot_path.parent.mkdir(parents=True, exist_ok=True)
    snapshot_bytes = canonical_bytes(snapshot)
    snapshot_path.write_bytes(snapshot_bytes)
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "snapshot_sha256": sha256_bytes(snapshot_bytes),
        "counts": {
            "pages": len(snapshot["pages"]),
            "sources": len(sources),
            "modules": len(snapshot["modules"]),
            "declarations": len(snapshot["declarations"]),
            "cts": len(snapshot["cts"]),
            "routes": len(snapshot["routes"]),
            "examples": len(snapshot["examples"]),
            "erdos_nodes": len(snapshot["erdos"]["nodes"]),
            "search_documents": len(snapshot["search_documents"]),
        },
        "sources": [{"id": source["id"], "path": source["path"], "sha256": source["sha256"]} for source in sources],
    }
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_bytes(canonical_bytes(manifest))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--raw-declarations", type=Path, default=DEFAULT_RAW)
    parser.add_argument("--snapshot", type=Path, default=DEFAULT_SNAPSHOT)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--skip-declaration-export", action="store_true", help="Use an existing compiled declaration artifact.")
    return parser.parse_args()


def resolve(root: Path, path: Path) -> Path:
    return path if path.is_absolute() else root / path


def display_path(root: Path, path: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return path.as_posix()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    raw_path = resolve(root, args.raw_declarations)
    snapshot_path = resolve(root, args.snapshot)
    manifest_path = resolve(root, args.manifest)
    if not args.skip_declaration_export:
        run_compiled_export(root, raw_path)
    elif not raw_path.exists():
        raise FileNotFoundError(f"compiled declaration artifact does not exist: {raw_path}")
    snapshot, sources = build_snapshot(root, raw_path)
    write_artifacts(root, snapshot_path, manifest_path, snapshot, sources)
    print(f"Wrote {display_path(root, snapshot_path)} ({len(snapshot['declarations'])} declarations)")
    print(f"Wrote {display_path(root, manifest_path)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
