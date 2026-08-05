from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_files,
    relative as relative_to,
    repository_root,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
QUANTUM = ROOT / "LeanCondensedMatter" / "QuantumTheory"

# Q4 guards public physical scalar definitions. Proof declarations are intentionally outside the
# scanner, so proof-local `Complex.re`, `.re`, and `Complex.reCLM` remain ordinary proof tools.
PUBLIC_DEFINITION_START = re.compile(
    r"^(?P<indent>[ \t]*)"
    r"(?P<modifiers>(?:(?:noncomputable|protected|unsafe|private)\s+)*)"
    r"(?P<kind>def|abbrev)\s+"
    r"(?P<name>[A-Za-z0-9_'.]+)\b",
    re.MULTILINE,
)
TOP_LEVEL_LINE = re.compile(r"^(?=\S)", re.MULTILINE)
REAL_SCALAR_CODOMAIN = re.compile(
    r":\s*(?:ℝ|NNReal|ENNReal|ℝ≥0|ℝ≥0∞)(?=\s|$|\)|,|:=)"
)
DIRECT_REAL_PROJECTION = re.compile(r"(?:\.\s*re\b|\bComplex\.re\b)")


@dataclass(frozen=True)
class PublicDefinition:
    path: Path
    name: str
    line: int
    header: str
    body: str


# Keep this list empty unless an existing public API must temporarily retain a mathematically
# justified projection. Every entry needs a declaration-specific rationale and is checked for
# staleness, so the allowlist cannot silently grow into a directory-wide exemption.
DIRECT_REAL_PROJECTION_ALLOWLIST: dict[tuple[str, str], str] = {}


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def public_definitions(path: Path) -> list[PublicDefinition]:
    code = strip_lean_comments(path.read_text(encoding="utf-8"))
    definitions: list[PublicDefinition] = []

    for match in PUBLIC_DEFINITION_START.finditer(code):
        if match.group("indent"):
            continue

        modifiers = match.group("modifiers").split()
        if "private" in modifiers:
            continue

        assignment = code.find(":=", match.end())
        if assignment < 0:
            continue

        # A declaration header and its `:=` must belong to the same top-level command. This avoids
        # accidentally pairing an equation-style definition with a later declaration.
        intervening_top_level = TOP_LEVEL_LINE.search(code, match.end(), assignment)
        if intervening_top_level is not None:
            continue

        next_top_level = TOP_LEVEL_LINE.search(code, assignment + 2)
        end = next_top_level.start() if next_top_level is not None else len(code)
        definitions.append(
            PublicDefinition(
                path=path,
                name=match.group("name"),
                line=code.count("\n", 0, match.start()) + 1,
                header=code[match.end():assignment],
                body=code[assignment + 2:end],
            )
        )

    return definitions


def direct_real_projection(definition: PublicDefinition) -> bool:
    return (
        REAL_SCALAR_CODOMAIN.search(definition.header) is not None
        and DIRECT_REAL_PROJECTION.search(definition.body) is not None
    )


def run_parser_self_tests() -> list[str]:
    fixture = """
noncomputable def lossless (z : selfAdjoint ℂ) : ℝ :=
  Complex.selfAdjointEquiv z

def projected (z : ℂ) : ℝ :=
  z.re

private def privateProjected (z : ℂ) : ℝ :=
  z.re

theorem proofLocal (z : ℂ) : z.re = z.re := by
  rfl

def projectedNNReal (z : ℂ) : NNReal :=
  ⟨Complex.re z, by positivity⟩

def complexDefinition (z : ℂ) : ℂ :=
  z.re
"""
    path = Path("SelfTest.lean")
    code = strip_lean_comments(fixture)
    found: list[PublicDefinition] = []

    for match in PUBLIC_DEFINITION_START.finditer(code):
        if match.group("indent") or "private" in match.group("modifiers").split():
            continue
        assignment = code.find(":=", match.end())
        if assignment < 0:
            continue
        intervening_top_level = TOP_LEVEL_LINE.search(code, match.end(), assignment)
        if intervening_top_level is not None:
            continue
        next_top_level = TOP_LEVEL_LINE.search(code, assignment + 2)
        end = next_top_level.start() if next_top_level is not None else len(code)
        found.append(
            PublicDefinition(
                path=path,
                name=match.group("name"),
                line=code.count("\n", 0, match.start()) + 1,
                header=code[match.end():assignment],
                body=code[assignment + 2:end],
            )
        )

    rejected = {definition.name for definition in found if direct_real_projection(definition)}
    expected = {"projected", "projectedNNReal"}
    if rejected != expected:
        return [
            "physical scalar audit parser self-test failed: "
            f"expected {sorted(expected)}, found {sorted(rejected)}"
        ]
    return []


def main() -> int:
    errors = run_parser_self_tests()
    seen_allowlist_entries: set[tuple[str, str]] = set()

    for path in lean_files(QUANTUM):
        for definition in public_definitions(path):
            if not direct_real_projection(definition):
                continue

            key = (relative(path), definition.name)
            if key in DIRECT_REAL_PROJECTION_ALLOWLIST:
                seen_allowlist_entries.add(key)
                continue

            errors.append(
                "public real-valued definition projects a complex expression directly with `.re`: "
                f"{relative(path)}:{definition.line}: {definition.name}"
            )

    stale_entries = set(DIRECT_REAL_PROJECTION_ALLOWLIST) - seen_allowlist_entries
    for path, name in sorted(stale_entries):
        errors.append(
            "stale physical scalar projection allowlist entry: "
            f"{path}: {name}"
        )

    return finish_audit(
        errors,
        failure_heading="QuantumTheory physical scalar boundary audit failed:",
        success_message="QuantumTheory physical scalar boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
