from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

from architecture_audit_common import (
    ImportBoundary,
    check_import_boundaries,
    finish_audit,
    lean_files,
    lean_imports,
    relative as relative_to,
    repository_root,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
SQ = LEAN / "SecondQuantization"
OWNERS = {"Common", "Fermionic", "Bosonic"}

SECOND_QUANTIZATION = "LeanCondensedMatter.SecondQuantization"
FERMIONIC = f"{SECOND_QUANTIZATION}.Fermionic"
BOSONIC = f"{SECOND_QUANTIZATION}.Bosonic"

DEPENDENCY_BOUNDARIES = (
    ImportBoundary(
        SQ / "Common",
        (FERMIONIC, BOSONIC),
        "SecondQuantization.Common must remain statistics-independent",
    ),
    ImportBoundary(
        LEAN / "Analysis",
        (SECOND_QUANTIZATION,),
        "Analysis must remain upstream of SecondQuantization",
    ),
    ImportBoundary(
        LEAN / "Combinatorics",
        (SECOND_QUANTIZATION,),
        "Combinatorics must remain upstream of SecondQuantization",
    ),
    ImportBoundary(
        LEAN / "QuantumTheory",
        (SECOND_QUANTIZATION,),
        "QuantumTheory must remain upstream of SecondQuantization",
    ),
)

NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_'.]+)\s*$")
SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+([A-Za-z0-9_'.]+))?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_'.]+))?\s*$")
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(abbrev|axiom|class|def|inductive|instance|lemma|opaque|structure|theorem)\b"
    r"\s*([^\s:({\[]+)?"
)
STATISTIC_NAME_RE = re.compile(r"(?:Boson|Bosonic|Fermion|Fermionic)")

# Pairing weights are combinatorial data hosted under the Common thermal tree.
ALLOWED_EXTERNAL_DECLARATIONS = {
    (
        "LeanCondensedMatter/SecondQuantization/Common/Thermal/"
        "BlochDeDominicis/PairingWeight.lean",
        "Pairing.weight",
        "Combinatorics",
    ),
}


@dataclass
class Frame:
    kind: str
    name: str | None
    namespace_parts: tuple[str, ...] = ()


@dataclass
class Finding:
    owner: str
    path: Path
    line: int
    kind: str
    name: str
    namespace: str


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def current_namespace(stack: list[Frame]) -> tuple[str, ...]:
    parts: list[str] = []
    for frame in stack:
        if frame.kind == "namespace":
            parts.extend(frame.namespace_parts)
    return tuple(parts)


def close_scope(stack: list[Frame], name: str | None, path: Path, line_no: int) -> None:
    if not stack:
        raise RuntimeError(f"unmatched end in {relative(path)}:{line_no}")

    if name is None:
        stack.pop()
        return

    target = tuple(name.split("."))
    if len(target) > 1:
        before = current_namespace(stack)
        if len(before) < len(target) or before[-len(target):] != target:
            raise RuntimeError(
                f"qualified end `{name}` does not match namespace `{'.'.join(before)}` "
                f"in {relative(path)}:{line_no}"
            )
        removed: list[str] = []
        while stack and len(removed) < len(target):
            frame = stack.pop()
            if frame.kind == "namespace":
                removed[0:0] = frame.namespace_parts
        if tuple(removed[-len(target):]) != target:
            raise RuntimeError(
                f"could not close qualified namespace `{name}` in {relative(path)}:{line_no}"
            )
        return

    for index in range(len(stack) - 1, -1, -1):
        frame = stack[index]
        frame_matches = frame.name == name or (
            frame.kind == "namespace"
            and frame.namespace_parts
            and frame.namespace_parts[-1] == name
        )
        if frame_matches:
            del stack[index:]
            return

    raise RuntimeError(f"unmatched named end `{name}` in {relative(path)}:{line_no}")


def audit_file(path: Path) -> tuple[list[Finding], list[Finding]]:
    rel = path.relative_to(SQ)
    owner = rel.parts[0] if rel.parts and rel.parts[0] in OWNERS else "Root"
    expected = ("SecondQuantization", owner) if owner in OWNERS else ("SecondQuantization",)
    text = strip_lean_comments(path.read_text(encoding="utf-8"))
    stack: list[Frame] = []
    misplaced: list[Finding] = []
    statistic_names: list[Finding] = []

    for line_no, line in enumerate(text.splitlines(), start=1):
        if match := NAMESPACE_RE.match(line):
            raw = match.group(1)
            stack.append(Frame("namespace", raw, tuple(raw.split("."))))
            continue
        if match := SECTION_RE.match(line):
            stack.append(Frame("section", match.group(1)))
            continue
        if match := END_RE.match(line):
            close_scope(stack, match.group(1), path, line_no)
            continue
        if match := DECL_RE.match(line):
            kind = match.group(1)
            name = match.group(2) or "<anonymous>"
            namespace_parts = current_namespace(stack)
            namespace = ".".join(namespace_parts) or "<root>"
            finding = Finding(owner, path, line_no, kind, name, namespace)
            if namespace_parts[: len(expected)] != expected:
                misplaced.append(finding)
            if owner == "Common" and STATISTIC_NAME_RE.search(name):
                statistic_names.append(finding)

    if stack:
        scopes = ", ".join(f"{frame.kind}:{frame.name or '<anonymous>'}" for frame in stack)
        raise RuntimeError(f"unclosed scopes in {relative(path)}: {scopes}")

    return misplaced, statistic_names


def collect_namespace_findings() -> tuple[list[Finding], list[Finding]]:
    misplaced: list[Finding] = []
    statistic_names: list[Finding] = []

    for path in lean_files(SQ):
        file_misplaced, file_statistics = audit_file(path)
        misplaced.extend(file_misplaced)
        statistic_names.extend(file_statistics)

    misplaced = [
        finding
        for finding in misplaced
        if (relative(finding.path), finding.name, finding.namespace)
        not in ALLOWED_EXTERNAL_DECLARATIONS
    ]
    return misplaced, statistic_names


def check_dependency_direction(errors: list[str]) -> None:
    check_import_boundaries(errors, DEPENDENCY_BOUNDARIES, root=ROOT)


def check_declaration_namespaces(errors: list[str]) -> None:
    misplaced, statistic_names = collect_namespace_findings()
    for finding in misplaced:
        errors.append(
            "declaration outside path-owned namespace: "
            f"{relative(finding.path)}:{finding.line}: "
            f"{finding.kind} {finding.name} in {finding.namespace}"
        )
    for finding in statistic_names:
        errors.append(
            "statistics-specific declaration name in Common: "
            f"{relative(finding.path)}:{finding.line}: {finding.name}"
        )


def check_entry_point(errors: list[str]) -> None:
    entry = SQ.with_suffix(".lean")
    if not entry.is_file():
        errors.append(f"missing canonical entry point: {relative(entry)}")

    root_module = ROOT / "LeanCondensedMatter.lean"
    if SECOND_QUANTIZATION not in lean_imports(root_module):
        errors.append(
            "repository root does not import canonical entry point: "
            f"{SECOND_QUANTIZATION}"
        )


def main() -> int:
    errors: list[str] = []
    check_dependency_direction(errors)
    check_declaration_namespaces(errors)
    check_entry_point(errors)
    return finish_audit(
        errors,
        failure_heading="SecondQuantization architecture audit failed:",
        success_message="SecondQuantization architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
