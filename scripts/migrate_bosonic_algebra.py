from __future__ import annotations

import shutil
from pathlib import Path

# One-shot, deliberately breaking directory migration for #348.
ROOT = Path(__file__).resolve().parents[1]
SQ = ROOT / "LeanCondensedMatter" / "SecondQuantization" / "Bosonic"
TARGET = SQ / "Algebra"

OLD_DIRS = (
    SQ / "Foundations",
    SQ / "OperatorAlgebra",
)

REPLACEMENTS = {
    "LeanCondensedMatter.SecondQuantization.Bosonic.Foundations.":
        "LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.",
    "LeanCondensedMatter.SecondQuantization.Bosonic.OperatorAlgebra.":
        "LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.",
    "Bosonic/Foundations/": "Bosonic/Algebra/",
    "Bosonic/OperatorAlgebra/": "Bosonic/Algebra/",
    "Bosonic/Foundations": "Bosonic/Algebra",
    "Bosonic/OperatorAlgebra": "Bosonic/Algebra",
}

TEXT_SUFFIXES = {".lean", ".md", ".tex", ".py", ".yml", ".yaml"}


def move_modules() -> None:
    TARGET.mkdir(parents=True, exist_ok=True)
    for old_dir in OLD_DIRS:
        if not old_dir.is_dir():
            raise RuntimeError(f"missing migration source: {old_dir.relative_to(ROOT)}")
        for source in sorted(old_dir.glob("*.lean")):
            destination = TARGET / source.name
            if destination.exists():
                raise RuntimeError(
                    f"migration collision: {destination.relative_to(ROOT)} already exists"
                )
            shutil.move(str(source), str(destination))
        old_dir.rmdir()


def rewrite_references() -> None:
    for path in ROOT.rglob("*"):
        if not path.is_file() or path.suffix not in TEXT_SUFFIXES:
            continue
        if ".git" in path.parts or ".lake" in path.parts:
            continue
        original = path.read_text(encoding="utf-8")
        updated = original
        for old, new in REPLACEMENTS.items():
            updated = updated.replace(old, new)
        if path == SQ / "Algebra.lean":
            updated = updated.replace(
                "The underlying declarations remain split into small proof files under `Foundations/` and\n"
                "`OperatorAlgebra/`; consumers normally import this module instead of those internal groups.",
                "The underlying declarations live in small proof files under `Algebra/`; consumers normally\n"
                "import this module instead of those internal files.",
            )
        if updated != original:
            path.write_text(updated, encoding="utf-8")


def validate_layout() -> None:
    for old_dir in OLD_DIRS:
        if old_dir.exists():
            raise RuntimeError(f"obsolete directory remains: {old_dir.relative_to(ROOT)}")
    stale = []
    for path in ROOT.rglob("*"):
        if not path.is_file() or path.suffix not in TEXT_SUFFIXES:
            continue
        if ".git" in path.parts or ".lake" in path.parts:
            continue
        text = path.read_text(encoding="utf-8")
        if "Bosonic.Foundations" in text or "Bosonic.OperatorAlgebra" in text:
            stale.append(str(path.relative_to(ROOT)))
    if stale:
        raise RuntimeError("obsolete bosonic module paths remain:\n" + "\n".join(stale))


if __name__ == "__main__":
    move_modules()
    rewrite_references()
    validate_layout()
