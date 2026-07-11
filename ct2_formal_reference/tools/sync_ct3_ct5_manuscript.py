#!/usr/bin/env python3
"""Replace the CT3--CT17 primary sections with their formal API excerpts."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = ROOT.parent
MANUSCRIPT = REPOSITORY / "framework/branch_closure_methodology_extended.tex"

SECTIONS = [
    ("CT3", r"\subsection{CT3", r"\subsection*{External-type compression in practice}"),
    ("CT4", r"\subsection{CT4", r"\subsection*{Charging schemes in practice}"),
    ("CT5", r"\subsection{CT5", r"\subsection*{Local-to-global bookkeeping in practice}"),
    ("CT6", r"\subsection{CT6", r"\subsection*{Active/dormant dichotomy in practice}"),
    ("CT7", r"\subsection{CT7", r"\subsection*{Exchange trichotomy in practice}"),
    ("CT8", r"\subsection{CT8", r"\subsection*{Finite-state pumping in practice}"),
    ("CT9", r"\subsection{CT9", r"\subsection*{Overload exhaustion in practice}"),
    ("CT10", r"\subsection{CT10", r"\subsection*{Default refinement in practice}"),
    ("CT11", r"\subsection{CT11", r"\subsection*{Localization in practice}"),
    ("CT12", r"\subsection{CT12", r"\subsection{CT13"),
    ("CT13", r"\subsection{CT13", r"\subsection*{Tiered charging in practice}"),
    ("CT14", r"\subsection{CT14", r"\subsection*{Aggregate closure in practice}"),
    ("CT15", r"\subsection{CT15", r"\subsection*{Rank forcing in practice}"),
    ("CT16", r"\subsection{CT16", r"\subsection*{Whole-object exact types in practice}"),
    ("CT17", r"\subsection{CT17", r"\subsection*{Target thickening in practice}"),
]


def replace(text: str, start: str, end: str, replacement: str) -> str:
    begin = text.index(start)
    finish = text.index(end, begin)
    return text[:begin] + replacement.rstrip() + "\n\n\n" + text[finish:]


def main() -> int:
    text = MANUSCRIPT.read_text(encoding="utf-8")
    for tactic_id, start, end in SECTIONS:
        excerpt = (ROOT / f"docs/{tactic_id.lower()}_source_excerpt.tex").read_text(encoding="utf-8")
        text = replace(text, start, end, excerpt)
    MANUSCRIPT.write_text(text, encoding="utf-8")
    print("Synchronized machine-centric CT3 through CT17 manuscript sections")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
