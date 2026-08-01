from __future__ import annotations

import re
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SQ = ROOT / "LeanCondensedMatter" / "SecondQuantization"
OWNERS = {"Common", "Fermionic", "Bosonic"}

NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_'.]+)\s*$")
SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+([A-Za-z0-9_'.]+))?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_'.]+))?\s*$")
DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(abbrev|axiom|class|def|inductive|instance|lemma|opaque|structure|theorem)\b"
    r"\s*([^\s:({\[]+)?"
)
STATISTIC_NAME_RE = re.compile(r"(?:Boson|Bosonic|Fermion|Fermionic)")


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


def strip_comments(text: str) -> str:
    """Remove Lean line and nested block comments while preserving newlines."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    escaped = False

    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""

        if depth:
            if ch == "/" and nxt == "-":
                depth += 1
                out.extend("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            out.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if ch == '"':
            in_string = True
            out.append(ch)
            i += 1
        elif ch == "/" and nxt == "-":
            depth = 1
            out.extend("  ")
            i += 2
        elif ch == "-" and nxt == "-":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        else:
            out.append(ch)
            i += 1

    return "".join(out)


def current_namespace(stack: list[Frame]) -> tuple[str, ...]:
    parts: list[str] = []
    for frame in stack:
        if frame.kind == "namespace":
            parts.extend(frame.namespace_parts)
    return tuple(parts)


def close_scope(stack: list[Frame], name: str | None, path: Path, line_no: int) -> None:
    if not stack:
        raise RuntimeError(f"unmatched end in {path.relative_to(ROOT)}:{line_no}")

    if name is None:
        stack.pop()
        return

    target = tuple(name.split("."))
    if len(target) > 1:
        before = current_namespace(stack)
        if len(before) < len(target) or before[-len(target):] != target:
            raise RuntimeError(
                f"qualified end `{name}` does not match namespace `{'.'.join(before)}` "
                f"in {path.relative_to(ROOT)}:{line_no}"
            )
        removed: list[str] = []
        while stack and len(removed) < len(target):
            frame = stack.pop()
            if frame.kind == "namespace":
                removed[0:0] = frame.namespace_parts
        if tuple(removed[-len(target):]) != target:
            raise RuntimeError(
                f"could not close qualified namespace `{name}` in {path.relative_to(ROOT)}:{line_no}"
            )
        return

    for index in range(len(stack) - 1, -1, -1):
        frame = stack[index]
        frame_matches = frame.name == name or (
            frame.kind == "namespace" and frame.namespace_parts and frame.namespace_parts[-1] == name
        )
        if frame_matches:
            del stack[index:]
            return

    raise RuntimeError(f"unmatched named end `{name}` in {path.relative_to(ROOT)}:{line_no}")


def audit_file(path: Path) -> tuple[list[Finding], list[Finding]]:
    rel = path.relative_to(SQ)
    owner = rel.parts[0] if rel.parts and rel.parts[0] in OWNERS else "Root"
    expected = ("SecondQuantization", owner) if owner in OWNERS else ("SecondQuantization",)
    text = strip_comments(path.read_text(encoding="utf-8"))
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
            if STATISTIC_NAME_RE.search(name):
                statistic_names.append(finding)

    if stack:
        scopes = ", ".join(f"{f.kind}:{f.name or '<anonymous>'}" for f in stack)
        raise RuntimeError(f"unclosed scopes in {path.relative_to(ROOT)}: {scopes}")

    return misplaced, statistic_names


def render(findings: list[Finding], title: str) -> None:
    print(f"## {title}")
    print()
    if not findings:
        print("None.")
        print()
        return

    by_owner: dict[str, list[Finding]] = defaultdict(list)
    for finding in findings:
        by_owner[finding.owner].append(finding)

    for owner in sorted(by_owner):
        print(f"### {owner} ({len(by_owner[owner])})")
        print()
        for finding in sorted(by_owner[owner], key=lambda f: (str(f.path), f.line, f.name)):
            rel = finding.path.relative_to(ROOT)
            print(
                f"- `{rel}:{finding.line}` — `{finding.kind} {finding.name}` "
                f"in `{finding.namespace}`"
            )
        print()


def main() -> int:
    misplaced: list[Finding] = []
    statistic_names: list[Finding] = []
    file_counts = Counter()

    for path in sorted(SQ.rglob("*.lean")):
        owner = path.relative_to(SQ).parts[0]
        file_counts[owner if owner in OWNERS else "Root"] += 1
        file_misplaced, file_statistics = audit_file(path)
        misplaced.extend(file_misplaced)
        statistic_names.extend(file_statistics)

    print("# SecondQuantization namespace audit")
    print()
    print("Scanned files:")
    for owner, count in sorted(file_counts.items()):
        print(f"- {owner}: {count}")
    print()
    print(f"Misplaced declarations: **{len(misplaced)}**")
    print(f"Statistic-encoded declaration names: **{len(statistic_names)}**")
    print()
    render(misplaced, "Declarations outside their path-owned namespace")
    render(statistic_names, "Declaration names containing a statistic suffix")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
