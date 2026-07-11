#!/usr/bin/env python3
"""Regenerate SHA256SUMS for tracked reference artifacts."""
from __future__ import annotations

import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "SHA256SUMS"
EXCLUDED_PARTS = {".lake", ".venv", ".pytest_cache", "__pycache__"}
EXCLUDED_FILES = {"SHA256SUMS", "lake-manifest.json"}


def included(path: Path) -> bool:
    relative = path.relative_to(ROOT)
    return (
        path.is_file()
        and path.name not in EXCLUDED_FILES
        and not any(part in EXCLUDED_PARTS for part in relative.parts)
    )


def main() -> int:
    lines = []
    for path in sorted((path for path in ROOT.rglob("*") if included(path)), key=lambda item: item.as_posix()):
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        lines.append(f"{digest}  ./{path.relative_to(ROOT).as_posix()}")
    OUTPUT.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Wrote SHA256SUMS for {len(lines)} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
