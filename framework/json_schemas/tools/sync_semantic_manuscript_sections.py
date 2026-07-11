#!/usr/bin/env python3
"""Copy semantic CT1--CT17 sections into the numbered manuscript mirror."""
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[1]
MAIN = PACKAGE.parent / "branch_closure_methodology_extended.tex"
MIRROR = PACKAGE / "source/branch_closure_methodology_extended_numbered.tex"

SECTIONS = [
    (r"\subsection{CT1", r"\subsection*{Local target tests in practice}"),
    (r"\subsection{CT2", r"\subsection*{Minimality and replacement in practice}"),
    (r"\subsection{CT3", r"\subsection*{External-type compression in practice}"),
    (r"\subsection{CT4", r"\subsection*{Charging schemes in practice}"),
    (r"\subsection{CT5", r"\subsection*{Local-to-global bookkeeping in practice}"),
    (r"\subsection{CT6", r"\subsection*{Active/dormant dichotomy in practice}"),
    (r"\subsection{CT7", r"\subsection*{Exchange trichotomy in practice}"),
    (r"\subsection{CT8", r"\subsection*{Finite-state pumping in practice}"),
    (r"\subsection{CT9", r"\subsection*{Overload exhaustion in practice}"),
    (r"\subsection{CT10", r"\subsection*{Default refinement in practice}"),
    (r"\subsection{CT11", r"\subsection*{Localization in practice}"),
    (r"\subsection{CT12", r"\subsection{CT13"),
    (r"\subsection{CT13", r"\subsection*{Tiered charging in practice}"),
    (r"\subsection{CT14", r"\subsection*{Aggregate closure in practice}"),
    (r"\subsection{CT15", r"\subsection*{Rank forcing in practice}"),
    (r"\subsection{CT16", r"\subsection*{Whole-object exact types in practice}"),
    (r"\subsection{CT17", r"\subsection*{Target thickening in practice}"),
]


def section(text: str, start: str, end: str) -> str:
    begin = text.index(start)
    finish = text.index(end, begin)
    return text[begin:finish]


def replace_section(target: str, source: str, start: str, end: str) -> str:
    begin = target.index(start)
    finish = target.index(end, begin)
    return target[:begin] + section(source, start, end) + target[finish:]


def main() -> int:
    source = MAIN.read_text(encoding="utf-8")
    target = MIRROR.read_text(encoding="utf-8")
    for start, end in SECTIONS:
        target = replace_section(target, source, start, end)
    MIRROR.write_text(target, encoding="utf-8")
    print("Synchronized semantic CT1 through CT17 manuscript sections")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
