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
EQUATION_BODY_START = re.compile(r"^\s+\|", re.MULTILINE)
REAL_SCALAR_RESULT = re.compile(
    r"^(?:.*→\s*)?(?:ℝ|Real|NNReal|ENNReal|ℝ≥0|ℝ≥0∞)$"
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


def split_public_definitions(code: str, path: Path) -> list[PublicDefinition]:
    definitions: list[PublicDefinition] = []

    for match in PUBLIC_DEFINITION_START.finditer(code):
        if match.group("indent"):
            continue

        modifiers = match.group("modifiers").split()
        if "private" in modifiers:
            continue

        next_top_level = TOP_LEVEL_LINE.search(code, match.end())
        end = next_top_level.start() if next_top_level is not None else len(code)
        command = code[match.end():end]

        assignment = command.find(":=")
        if assignment >= 0:
            header = command[:assignment]
            body = command[assignment + 2:]
        else:
            equation = EQUATION_BODY_START.search(command)
            if equation is None:
                continue
            header = command[:equation.start()]
            body = command[equation.start():]

        definitions.append(
            PublicDefinition(
                path=path,
                name=match.group("name"),
                line=code.count("\n", 0, match.start()) + 1,
                header=header,
                body=body,
            )
        )

    return definitions


def public_definitions(path: Path) -> list[PublicDefinition]:
    code = strip_lean_comments(path.read_text(encoding="utf-8"))
    return split_public_definitions(code, path)


def has_explicit_real_scalar_result(header: str) -> bool:
    if ":" not in header:
        return False

    result = " ".join(header.rsplit(":", 1)[1].split())
    while result.startswith("(") and result.endswith(")"):
        result = result[1:-1].strip()
    return REAL_SCALAR_RESULT.fullmatch(result) is not None


def direct_real_projection(definition: PublicDefinition) -> bool:
    return (
        has_explicit_real_scalar_result(definition.header)
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

def projectedFunction (z : ℂ) : Bool → ℝ :=
  fun _ => z.re

def projectedByEquation (z : ℂ) : Bool → ℝ
  | true => z.re
  | false => 0

def complexDefinition (z : ℂ) : ℂ :=
  z.re
"""
    found = split_public_definitions(strip_lean_comments(fixture), Path("SelfTest.lean"))
    rejected = {definition.name for definition in found if direct_real_projection(definition)}
    expected = {
        "projected",
        "projectedNNReal",
        "projectedFunction",
        "projectedByEquation",
    }
    if rejected != expected:
        return [
            "physical scalar audit parser self-test failed: "
            f"expected {sorted(expected)}, found {sorted(rejected)}"
        ]
    return []


def main() -> int:
    errors = run_parser_self_tests()
    seen_allowlist_entries: set[tuple[str, str]] = set()

    for key, rationale in DIRECT_REAL_PROJECTION_ALLOWLIST.items():
        if not rationale.strip():
            errors.append(
                "physical scalar projection allowlist entry lacks a rationale: "
                f"{key[0]}: {key[1]}"
            )

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
