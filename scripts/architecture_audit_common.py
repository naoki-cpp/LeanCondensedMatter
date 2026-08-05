from __future__ import annotations

import sys
from collections.abc import Iterable, Iterator
from pathlib import Path


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


def check_absent_paths(
    errors: list[str],
    paths: Iterable[Path],
    *,
    root: Path,
    description: str,
) -> None:
    """Append one diagnostic for every path that should no longer exist."""
    for path in paths:
        if path.exists():
            errors.append(f"{description}: {relative(root, path)}")


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
