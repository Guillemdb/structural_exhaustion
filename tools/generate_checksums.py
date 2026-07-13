#!/usr/bin/env python3
"""Write deterministic SHA-256 checksums for source and generated artifacts."""

from __future__ import annotations

import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "SHA256SUMS"
EXCLUDED_PARTS = {
    ".agents",
    ".git",
    ".lake",
    ".ruff_cache",
    "build",
    "node_modules",
    "__pycache__",
    ".pytest_cache",
    ".venv",
}
EXCLUDED_SUFFIXES = {".aux", ".fdb_latexmk", ".fls", ".log", ".out", ".pdf", ".toc"}
EXCLUDED_FILES = {OUTPUT}


def included(path: Path) -> bool:
    relative = path.relative_to(ROOT)
    return (
        path.is_file()
        and path not in EXCLUDED_FILES
        and not EXCLUDED_PARTS.intersection(relative.parts)
        and path.suffix not in EXCLUDED_SUFFIXES
    )


def main() -> int:
    paths = sorted((path for path in ROOT.rglob("*") if included(path)), key=lambda path: path.relative_to(ROOT).as_posix())
    lines = [
        f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.relative_to(ROOT).as_posix()}"
        for path in paths
    ]
    OUTPUT.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Wrote SHA256SUMS for {len(paths)} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
