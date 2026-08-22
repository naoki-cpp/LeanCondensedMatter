from __future__ import annotations

import re
import sys
from collections.abc import Iterable, Iterator
from dataclasses import dataclass
from pathlib import Path

IMPORT_RE = re.compile(r"^\s*import\s+([^\s]+)\s*$")


@dataclass(frozen=True)
class ImportBoundary:
    """A source tree and the downstream module prefixes it must not import."""

    source_root: Path
    forbidden_prefixes: tuple[str, ...]
    description: str


def repository_root(script_file: str | Path) -> Path:
    """Return the repository root for a script stored directly under ``scripts/``."""
    return Path(script_file).resolve().parents[1]


def relative(root: Path, path: Path) -> str:
    """Render a repository-relative path for stable diagnostics."""
    return str(path.relative_to(root))


def files_matching(root: Path, pattern: str) -> Iterator[Path]:
    """Yield matching files in deterministic repository order."""
    if root.exists():
        yield from sorted(root.rglob(pattern))


def lean_files(root: Path) -> Iterator[Path]:
    yield from files_matching(root, "*.lean")


def numbered_lines(path: Path) -> Iterator[tuple[int, str]]:
    """Yield UTF-8 text lines with one-based line numbers."""
    yield from enumerate(path.read_text(encoding="utf-8").splitlines(), start=1)


def strip_lean_comments(text: str) -> str:
    """Remove Lean line and nested block comments while preserving lines and strings."""
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


def lean_files_matching(root: Path, pattern: re.Pattern[str]) -> list[Path]:
    """Return Lean files whose comment-stripped source matches a compiled pattern."""
    matches: list[Path] = []
    for path in lean_files(root):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if pattern.search(code):
            matches.append(path)
    return matches


def numbered_imports(path: Path) -> Iterator[tuple[int, str]]:
    """Yield direct Lean imports with source line numbers after removing comments."""
    code = strip_lean_comments(path.read_text(encoding="utf-8"))
    for line_no, line in enumerate(code.splitlines(), start=1):
        if match := IMPORT_RE.match(line):
            yield line_no, match.group(1)


def lean_imports(path: Path) -> tuple[str, ...]:
    """Return direct Lean imports after removing comments."""
    return tuple(imported for _, imported in numbered_imports(path))


def module_matches_prefix(module: str, prefix: str) -> bool:
    """Match a Lean module prefix without conflating siblings such as Foo and FooExtra."""
    return module == prefix or module.startswith(prefix + ".")


def require_files(
    errors: list[str],
    paths: Iterable[Path],
    *,
    root: Path,
    description: str,
) -> None:
    """Require canonical owner files to exist."""
    for path in paths:
        if not path.is_file():
            errors.append(f"missing {description}: {relative(root, path)}")


def require_import(
    errors: list[str],
    path: Path,
    imported: str,
    *,
    root: Path,
    description: str = "module",
) -> None:
    """Require one direct Lean import from an existing source file."""
    if not path.is_file():
        errors.append(f"missing {description}: {relative(root, path)}")
        return
    if imported not in lean_imports(path):
        errors.append(f"{relative(root, path)} must import `{imported}`")


def forbid_import_prefixes(
    errors: list[str],
    path: Path,
    prefixes: str | tuple[str, ...],
    *,
    root: Path,
    description: str,
) -> None:
    """Reject direct imports into forbidden downstream dependency prefixes."""
    normalized = (prefixes,) if isinstance(prefixes, str) else prefixes
    for line_no, imported in numbered_imports(path):
        if any(module_matches_prefix(imported, prefix) for prefix in normalized):
            errors.append(
                f"{description}: {relative(root, path)}:{line_no} imports forbidden module `{imported}`"
            )


def check_import_boundaries(
    errors: list[str],
    boundaries: Iterable[ImportBoundary],
    *,
    root: Path,
) -> None:
    """Apply declarative import boundaries to every Lean file in each source tree."""
    for boundary in boundaries:
        if not boundary.source_root.is_dir():
            errors.append(
                f"missing dependency source tree for {boundary.description}: "
                f"{relative(root, boundary.source_root)}"
            )
            continue
        for path in lean_files(boundary.source_root):
            forbid_import_prefixes(
                errors,
                path,
                boundary.forbidden_prefixes,
                root=root,
                description=boundary.description,
            )


def finish_audit(
    errors: list[str],
    *,
    failure_heading: str,
    success_message: str,
) -> int:
    """Print diagnostics in the shared audit format and return a process status."""
    if errors:
        print(failure_heading, file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print(success_message)
    return 0
