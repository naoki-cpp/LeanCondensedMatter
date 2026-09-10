#!/usr/bin/env python3
"""Find typed `have` proofs that Lean can replace with a shorter existing proof.

For each `have ... : T := by` block, this script replaces only that proof body
in a temporary copy and recompiles the file with `lake env lean`.  Reported
candidates are therefore kernel-checked in the original local context.

The conservative first pass probes `exact?`, `apply? <;> assumption`, and
`simp?`.  Source files are never modified.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence

for _stream in (sys.stdout, sys.stderr):
    if hasattr(_stream, "reconfigure"):
        _stream.reconfigure(encoding="utf-8", errors="replace")

REPO_ROOT = Path(__file__).resolve().parent.parent
PROBE_ROOT = REPO_ROOT / ".lake" / "proof-reuse-audit"

HAVE_BY_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?P<kind>haveI|have)\b(?P<header>.*):=\s*by\s*(?:--.*)?$"
)
TRY_THIS_RE = re.compile(r"Try this:\s*(?P<suggestion>.+?)\s*$")
PROBES = {
    "exact": "exact?",
    "apply": "apply? <;> assumption",
    "simp": "simp?",
}


@dataclass(frozen=True)
class ProofBlock:
    start_line: int
    end_line: int
    start_index: int
    end_index: int
    indent: str
    body_lines: int


@dataclass(frozen=True)
class Finding:
    file: str
    start_line: int
    end_line: int
    original_body_lines: int
    mode: str
    suggestion: str


def indent_width(text: str) -> int:
    width = 0
    for char in text:
        if char == " ":
            width += 1
        elif char == "\t":
            width += 4
        else:
            break
    return width


def significant(text: str) -> bool:
    stripped = text.strip()
    return bool(stripped) and not stripped.startswith(("--", "/-"))


def find_typed_have_blocks(source: str, min_body_lines: int) -> list[ProofBlock]:
    """Find single-line, explicitly typed `have`/`haveI` proof headers."""
    lines = source.splitlines(keepends=True)
    blocks: list[ProofBlock] = []

    for i, line in enumerate(lines):
        match = HAVE_BY_RE.match(line.rstrip("\r\n"))
        if match is None or ":" not in match.group("header"):
            continue

        base_indent = indent_width(match.group("indent"))
        j = i + 1
        while j < len(lines):
            current = lines[j]
            if not current.strip():
                j += 1
                continue
            if indent_width(current) <= base_indent:
                break
            j += 1

        body_lines = sum(1 for item in lines[i + 1 : j] if significant(item))
        if body_lines < min_body_lines:
            continue

        blocks.append(
            ProofBlock(
                start_line=i + 1,
                end_line=j,
                start_index=i,
                end_index=j,
                indent=match.group("indent"),
                body_lines=body_lines,
            )
        )

    return blocks


def replace_block(source: str, block: ProofBlock, tactic: str) -> str:
    lines = source.splitlines(keepends=True)
    newline = "\r\n" if lines[block.start_index].endswith("\r\n") else "\n"
    replacement = f"{block.indent}  {tactic}{newline}"
    return "".join(
        lines[: block.start_index + 1] + [replacement] + lines[block.end_index :]
    )


def parse_suggestion(output: str) -> str | None:
    found = [
        match.group("suggestion").strip()
        for line in output.splitlines()
        if (match := TRY_THIS_RE.search(line))
    ]
    return found[-1] if found else None


def run_lean(path: Path, timeout: float) -> tuple[int, str, bool]:
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
        )
        return proc.returncode, proc.stdout + proc.stderr, False
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout or ""
        stderr = exc.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode("utf-8", errors="replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode("utf-8", errors="replace")
        return 124, stdout + stderr, True


def run_probe(source: str, label: str, timeout: float) -> tuple[int, str, bool]:
    PROBE_ROOT.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=f"{label}-", dir=PROBE_ROOT) as temp_dir:
        path = Path(temp_dir) / "Probe.lean"
        path.write_text(source, encoding="utf-8")
        return run_lean(path, timeout)


def first_error(output: str) -> str:
    lines = output.splitlines()
    for i, line in enumerate(lines):
        if ": error:" in line or line.startswith("error:"):
            tail = [item for item in lines[i + 1 : i + 5] if not item.startswith("trace:")]
            return "\n".join([line, *tail]).strip()
    return "\n".join(lines[:5]).strip()


def audit_file(
    path: Path,
    *,
    modes: Sequence[str],
    min_body_lines: int,
    max_candidates: int | None,
    timeout: float,
    baseline: bool,
) -> tuple[list[Finding], list[str]]:
    relative = str(path.relative_to(REPO_ROOT))
    source = path.read_text(encoding="utf-8")
    blocks = find_typed_have_blocks(source, min_body_lines)
    if max_candidates is not None:
        blocks = blocks[:max_candidates]

    diagnostics: list[str] = []
    if baseline:
        code, output, timed_out = run_lean(path, timeout)
        if timed_out:
            return [], [f"{relative}: baseline compile timed out after {timeout:g}s"]
        if code != 0:
            detail = first_error(output)
            message = f"{relative}: baseline compile failed; skipped"
            if detail:
                message += f"\n{detail}"
            return [], [message]

    findings: list[Finding] = []
    for block in blocks:
        for mode in modes:
            tactic = PROBES[mode]
            modified = replace_block(source, block, tactic)
            code, output, timed_out = run_probe(
                modified, f"line-{block.start_line}-{mode}", timeout
            )
            if timed_out:
                diagnostics.append(f"{relative}:{block.start_line}: {mode} probe timed out")
                continue
            if code != 0:
                continue

            findings.append(
                Finding(
                    file=relative,
                    start_line=block.start_line,
                    end_line=block.end_line,
                    original_body_lines=block.body_lines,
                    mode=mode,
                    suggestion=parse_suggestion(output) or tactic,
                )
            )
            break

    return findings, diagnostics


def resolve_files(values: Sequence[str]) -> list[Path]:
    files: list[Path] = []
    for value in values:
        path = Path(value)
        if not path.is_absolute():
            path = REPO_ROOT / path
        path = path.resolve()
        try:
            path.relative_to(REPO_ROOT)
        except ValueError as exc:
            raise ValueError(f"path is outside repository: {value}") from exc
        if not path.is_file():
            raise ValueError(f"file does not exist: {value}")
        if path.suffix != ".lean":
            raise ValueError(f"not a Lean file: {value}")
        files.append(path)
    return files


def parse_modes(value: str) -> tuple[str, ...]:
    modes = tuple(item.strip() for item in value.split(",") if item.strip())
    unknown = [mode for mode in modes if mode not in PROBES]
    if unknown:
        raise argparse.ArgumentTypeError(
            f"unknown mode(s): {', '.join(unknown)}; choose from {', '.join(PROBES)}"
        )
    if not modes:
        raise argparse.ArgumentTypeError("at least one mode is required")
    return modes


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(
        description="Kernel-check shorter replacements for typed `have` proof blocks."
    )
    result.add_argument("files", nargs="+", help="repo-relative .lean files")
    result.add_argument(
        "--modes",
        type=parse_modes,
        default=tuple(PROBES),
        help="comma-separated probes in priority order (default: exact,apply,simp)",
    )
    result.add_argument(
        "--min-body-lines",
        type=int,
        default=2,
        help="minimum significant lines in the original proof body (default: 2)",
    )
    result.add_argument("--max-candidates", type=int)
    result.add_argument(
        "--timeout",
        type=float,
        default=30.0,
        help="per-compilation timeout in seconds (default: 30)",
    )
    result.add_argument(
        "--no-baseline",
        action="store_true",
        help="skip compiling the unmodified file first",
    )
    result.add_argument("--json", action="store_true", help="emit JSON")
    return result


def main(argv: Sequence[str] | None = None) -> int:
    args_parser = parser()
    args = args_parser.parse_args(argv)

    if args.min_body_lines < 1:
        args_parser.error("--min-body-lines must be at least 1")
    if args.max_candidates is not None and args.max_candidates < 1:
        args_parser.error("--max-candidates must be at least 1")
    if args.timeout <= 0:
        args_parser.error("--timeout must be positive")

    try:
        files = resolve_files(args.files)
    except ValueError as exc:
        args_parser.error(str(exc))

    findings: list[Finding] = []
    diagnostics: list[str] = []
    for path in files:
        file_findings, file_diagnostics = audit_file(
            path,
            modes=args.modes,
            min_body_lines=args.min_body_lines,
            max_candidates=args.max_candidates,
            timeout=args.timeout,
            baseline=not args.no_baseline,
        )
        findings.extend(file_findings)
        diagnostics.extend(file_diagnostics)

    if args.json:
        print(
            json.dumps(
                {
                    "findings": [asdict(item) for item in findings],
                    "diagnostics": diagnostics,
                },
                ensure_ascii=False,
                indent=2,
            )
        )
    else:
        for item in diagnostics:
            print(item, file=sys.stderr)
        for item in findings:
            print(
                f"{item.file}:{item.start_line}-{item.end_line}: "
                f"{item.mode} can replace {item.original_body_lines} body line(s)"
            )
            print(f"  {item.suggestion}")
        if not findings and not diagnostics:
            print("No proof-reuse candidates found.")

    return 1 if diagnostics else 0


if __name__ == "__main__":
    sys.exit(main())
