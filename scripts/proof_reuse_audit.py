#!/usr/bin/env python3
"""Find proof regions that Lean can replace with a shorter existing proof.

The audit scans theorem/lemma/example proof bodies and explicitly typed
`have ... : T := by` / `haveI ... : T := by` blocks. It probes both complete
`have` bodies and contiguous top-level tactic intervals. For every candidate,
only the selected source range is replaced in a temporary copy, and the whole
file is recompiled with `lake env lean`.

Reported replacements are therefore kernel-checked in the original local
context. The conservative probes are `exact?`, `apply? <;> assumption`, and
`simp?`. Source files are never modified.
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
BY_END_RE = re.compile(r":=\s*by\s*(?:--.*)?$")
DECL_START_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?:(?:private|protected|noncomputable)\s+)*"
    r"(?P<kind>theorem|lemma|example)\b"
)
TRY_THIS_RE = re.compile(r"Try this:\s*(?P<suggestion>.+?)\s*$")
PROBES = {
    "exact": "exact?",
    "apply": "apply? <;> assumption",
    "simp": "simp?",
}


@dataclass(frozen=True)
class ProofBlock:
    kind: str
    header_start_line: int
    body_start_line: int
    end_line: int
    header_start_index: int
    body_start_index: int
    end_index: int
    base_indent: int
    body_indent: str
    body_lines: int


@dataclass(frozen=True)
class TacticChunk:
    start_line: int
    end_line: int
    start_index: int
    end_index: int
    indent: str
    significant_lines: int


@dataclass(frozen=True)
class Region:
    scope: str
    block_kind: str
    start_line: int
    end_line: int
    start_index: int
    end_index: int
    indent: str
    original_lines: int
    tactic_count: int


@dataclass(frozen=True)
class Finding:
    file: str
    scope: str
    block_kind: str
    start_line: int
    end_line: int
    original_lines: int
    tactic_count: int
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


def leading_indent(text: str) -> str:
    return text[: len(text) - len(text.lstrip(" \t"))]


def significant(text: str) -> bool:
    stripped = text.strip()
    return bool(stripped) and not stripped.startswith(("--", "/-", "-/"))


def block_end(lines: list[str], body_start: int, base_indent: int) -> int:
    j = body_start
    while j < len(lines):
        current = lines[j]
        if not current.strip():
            j += 1
            continue
        if indent_width(current) <= base_indent:
            break
        j += 1
    return j


def body_metadata(
    lines: list[str], body_start: int, end_index: int, min_body_lines: int
) -> tuple[str, int] | None:
    body_indices = [
        i for i in range(body_start, end_index) if significant(lines[i])
    ]
    if len(body_indices) < min_body_lines:
        return None
    min_index = min(body_indices, key=lambda i: indent_width(lines[i]))
    return leading_indent(lines[min_index]), len(body_indices)


def find_typed_have_blocks(source: str, min_body_lines: int) -> list[ProofBlock]:
    """Find single-line, explicitly typed `have`/`haveI` proof headers."""
    lines = source.splitlines(keepends=True)
    blocks: list[ProofBlock] = []

    for i, line in enumerate(lines):
        match = HAVE_BY_RE.match(line.rstrip("\r\n"))
        if match is None or ":" not in match.group("header"):
            continue

        base_indent = indent_width(match.group("indent"))
        body_start = i + 1
        end_index = block_end(lines, body_start, base_indent)
        metadata = body_metadata(lines, body_start, end_index, min_body_lines)
        if metadata is None:
            continue
        body_indent, body_lines = metadata
        blocks.append(
            ProofBlock(
                kind=match.group("kind"),
                header_start_line=i + 1,
                body_start_line=body_start + 1,
                end_line=end_index,
                header_start_index=i,
                body_start_index=body_start,
                end_index=end_index,
                base_indent=base_indent,
                body_indent=body_indent,
                body_lines=body_lines,
            )
        )

    return blocks


def declaration_start(
    lines: list[str], by_line_index: int, max_header_lines: int = 80
) -> tuple[int, str, int] | None:
    lower = max(0, by_line_index - max_header_lines + 1)
    for i in range(by_line_index, lower - 1, -1):
        match = DECL_START_RE.match(lines[i])
        if match is not None:
            return i, match.group("kind"), indent_width(match.group("indent"))
        if i != by_line_index and BY_END_RE.search(lines[i].rstrip("\r\n")):
            break
    return None


def find_declaration_blocks(source: str, min_body_lines: int) -> list[ProofBlock]:
    """Find theorem/lemma/example `:= by` bodies, including multiline headers."""
    lines = source.splitlines(keepends=True)
    blocks: list[ProofBlock] = []
    seen_headers: set[int] = set()

    for i, line in enumerate(lines):
        text = line.rstrip("\r\n")
        if not BY_END_RE.search(text) or HAVE_BY_RE.match(text) is not None:
            continue
        start = declaration_start(lines, i)
        if start is None:
            continue
        header_start, kind, base_indent = start
        if header_start in seen_headers:
            continue
        seen_headers.add(header_start)

        body_start = i + 1
        end_index = block_end(lines, body_start, base_indent)
        metadata = body_metadata(lines, body_start, end_index, min_body_lines)
        if metadata is None:
            continue
        body_indent, body_lines = metadata
        blocks.append(
            ProofBlock(
                kind=kind,
                header_start_line=header_start + 1,
                body_start_line=body_start + 1,
                end_line=end_index,
                header_start_index=header_start,
                body_start_index=body_start,
                end_index=end_index,
                base_indent=base_indent,
                body_indent=body_indent,
                body_lines=body_lines,
            )
        )

    return blocks


def find_proof_blocks(source: str, min_body_lines: int) -> list[ProofBlock]:
    blocks = [
        *find_typed_have_blocks(source, min_body_lines),
        *find_declaration_blocks(source, min_body_lines),
    ]
    return sorted(
        blocks,
        key=lambda block: (block.body_start_index, block.end_index, block.kind),
    )


def top_level_tactic_chunks(source: str, block: ProofBlock) -> list[TacticChunk]:
    lines = source.splitlines(keepends=True)
    body_indices = [
        i
        for i in range(block.body_start_index, block.end_index)
        if significant(lines[i])
    ]
    if not body_indices:
        return []

    top_indent = min(indent_width(lines[i]) for i in body_indices)
    starts = [i for i in body_indices if indent_width(lines[i]) == top_indent]
    chunks: list[TacticChunk] = []
    for position, start in enumerate(starts):
        end = starts[position + 1] if position + 1 < len(starts) else block.end_index
        significant_lines = sum(1 for i in range(start, end) if significant(lines[i]))
        chunks.append(
            TacticChunk(
                start_line=start + 1,
                end_line=end,
                start_index=start,
                end_index=end,
                indent=leading_indent(lines[start]),
                significant_lines=significant_lines,
            )
        )
    return chunks


def whole_have_region(block: ProofBlock) -> Region | None:
    if block.kind not in {"have", "haveI"}:
        return None
    return Region(
        scope="block",
        block_kind=block.kind,
        start_line=block.body_start_line,
        end_line=block.end_line,
        start_index=block.body_start_index,
        end_index=block.end_index,
        indent=block.body_indent,
        original_lines=block.body_lines,
        tactic_count=0,
    )


def interval_regions(
    source: str,
    block: ProofBlock,
    *,
    min_tactics: int,
    max_span_tactics: int | None,
    max_intervals: int | None,
) -> list[Region]:
    chunks = top_level_tactic_chunks(source, block)
    if len(chunks) < min_tactics:
        return []

    regions: list[Region] = []
    for start in range(len(chunks)):
        for stop in range(start + min_tactics, len(chunks) + 1):
            tactic_count = stop - start
            if max_span_tactics is not None and tactic_count > max_span_tactics:
                break
            if start == 0 and stop == len(chunks):
                # Complete typed-have bodies are already covered by block probes.
                # Declaration bodies have no separate block probe, so keep them.
                if block.kind in {"have", "haveI"}:
                    continue
            first = chunks[start]
            last = chunks[stop - 1]
            regions.append(
                Region(
                    scope="interval",
                    block_kind=block.kind,
                    start_line=first.start_line,
                    end_line=last.end_line,
                    start_index=first.start_index,
                    end_index=last.end_index,
                    indent=first.indent,
                    original_lines=sum(
                        chunk.significant_lines for chunk in chunks[start:stop]
                    ),
                    tactic_count=tactic_count,
                )
            )

    # Prefer the largest compressions first; ties prefer earlier source ranges.
    regions.sort(key=lambda item: (-item.tactic_count, item.start_index, item.end_index))
    if max_intervals is not None:
        regions = regions[:max_intervals]
    return regions


def replace_region(source: str, region: Region, tactic: str) -> str:
    lines = source.splitlines(keepends=True)
    if region.start_index >= len(lines):
        return source
    newline = "\r\n" if lines[region.start_index].endswith("\r\n") else "\n"
    replacement = f"{region.indent}{tactic}{newline}"
    return "".join(lines[: region.start_index] + [replacement] + lines[region.end_index :])


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


def candidate_regions(
    source: str,
    blocks: Sequence[ProofBlock],
    *,
    scan_intervals: bool,
    min_tactics: int,
    max_span_tactics: int | None,
    max_intervals_per_block: int | None,
) -> list[Region]:
    regions: list[Region] = []
    seen: set[tuple[int, int]] = set()
    for block in blocks:
        whole = whole_have_region(block)
        if whole is not None:
            key = (whole.start_index, whole.end_index)
            if key not in seen:
                regions.append(whole)
                seen.add(key)
        if not scan_intervals:
            continue
        for region in interval_regions(
            source,
            block,
            min_tactics=min_tactics,
            max_span_tactics=max_span_tactics,
            max_intervals=max_intervals_per_block,
        ):
            key = (region.start_index, region.end_index)
            if key in seen:
                continue
            regions.append(region)
            seen.add(key)
    return regions


def audit_file(
    path: Path,
    *,
    modes: Sequence[str],
    min_body_lines: int,
    max_blocks: int | None,
    timeout: float,
    baseline: bool,
    scan_intervals: bool,
    min_tactics: int,
    max_span_tactics: int | None,
    max_intervals_per_block: int | None,
    max_findings: int | None,
) -> tuple[list[Finding], list[str]]:
    relative = str(path.relative_to(REPO_ROOT))
    source = path.read_text(encoding="utf-8")
    blocks = find_proof_blocks(source, min_body_lines)
    if max_blocks is not None:
        blocks = blocks[:max_blocks]

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

    regions = candidate_regions(
        source,
        blocks,
        scan_intervals=scan_intervals,
        min_tactics=min_tactics,
        max_span_tactics=max_span_tactics,
        max_intervals_per_block=max_intervals_per_block,
    )

    findings: list[Finding] = []
    for region in regions:
        if max_findings is not None and len(findings) >= max_findings:
            break
        for mode in modes:
            tactic = PROBES[mode]
            modified = replace_region(source, region, tactic)
            label = f"line-{region.start_line}-{region.end_line}-{mode}"
            code, output, timed_out = run_probe(modified, label, timeout)
            if timed_out:
                diagnostics.append(
                    f"{relative}:{region.start_line}-{region.end_line}: {mode} probe timed out"
                )
                continue
            if code != 0:
                continue

            findings.append(
                Finding(
                    file=relative,
                    scope=region.scope,
                    block_kind=region.block_kind,
                    start_line=region.start_line,
                    end_line=region.end_line,
                    original_lines=region.original_lines,
                    tactic_count=region.tactic_count,
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
        description="Kernel-check shorter replacements for proof blocks and tactic intervals."
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
        help="minimum significant lines in a proof body (default: 2)",
    )
    result.add_argument(
        "--max-blocks",
        type=int,
        help="inspect at most this many proof blocks in each file",
    )
    result.add_argument(
        "--no-intervals",
        action="store_true",
        help="probe only complete typed-have bodies, not tactic intervals",
    )
    result.add_argument(
        "--min-tactics",
        type=int,
        default=2,
        help="minimum top-level tactics in an interval (default: 2)",
    )
    result.add_argument(
        "--max-span-tactics",
        type=int,
        default=6,
        help="maximum top-level tactics in an interval (default: 6)",
    )
    result.add_argument(
        "--max-intervals-per-block",
        type=int,
        default=12,
        help="maximum interval probes per proof block before tactic modes (default: 12)",
    )
    result.add_argument(
        "--max-findings",
        type=int,
        help="stop after this many successful replacements in each file",
    )
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
    if args.max_blocks is not None and args.max_blocks < 1:
        args_parser.error("--max-blocks must be at least 1")
    if args.min_tactics < 2:
        args_parser.error("--min-tactics must be at least 2")
    if args.max_span_tactics is not None and args.max_span_tactics < args.min_tactics:
        args_parser.error("--max-span-tactics must be at least --min-tactics")
    if args.max_intervals_per_block is not None and args.max_intervals_per_block < 1:
        args_parser.error("--max-intervals-per-block must be at least 1")
    if args.max_findings is not None and args.max_findings < 1:
        args_parser.error("--max-findings must be at least 1")
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
            max_blocks=args.max_blocks,
            timeout=args.timeout,
            baseline=not args.no_baseline,
            scan_intervals=not args.no_intervals,
            min_tactics=args.min_tactics,
            max_span_tactics=args.max_span_tactics,
            max_intervals_per_block=args.max_intervals_per_block,
            max_findings=args.max_findings,
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
            if item.scope == "interval":
                size = f"{item.tactic_count} top-level tactic(s), {item.original_lines} line(s)"
            else:
                size = f"{item.original_lines} proof line(s)"
            print(
                f"{item.file}:{item.start_line}-{item.end_line}: "
                f"{item.scope}/{item.block_kind} {item.mode} can replace {size}"
            )
            print(f"  {item.suggestion}")
        if not findings and not diagnostics:
            print("No proof-reuse candidates found.")

    return 1 if diagnostics else 0


if __name__ == "__main__":
    sys.exit(main())
