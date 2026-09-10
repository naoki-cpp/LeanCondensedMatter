#!/usr/bin/env python3
"""Find proof regions replaceable by concrete, replay-verified Lean suggestions.

For each candidate source region, the audit first runs a search tactic (`exact?`,
`apply?`, or `simp?`) in a temporary copy. It extracts the concrete `Try this:`
replacement emitted by Lean, substitutes that replacement into a fresh copy,
and recompiles the whole file.

Only an admission-free second compilation decides whether a finding is
reported. In particular, search tactics are never treated as proof, and
suggestions containing holes, `sorry`, or search scaffolding are rejected.
When the generated theorem catalog is available, project-theorem reuse is
identified and preferred over generic theorem reuse and automation-only
compression. Source files are never modified.
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
DEFAULT_CATALOG = REPO_ROOT / "docs" / "generated" / "theorems.json"

HAVE_BY_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?P<kind>haveI|have)\b(?P<header>.*):=\s*by\s*(?:--.*)?$"
)
BY_END_RE = re.compile(r":=\s*by\s*(?:--.*)?$")
DECL_START_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?:(?:private|protected|noncomputable)\s+)*"
    r"(?P<kind>theorem|lemma|example)\b"
)
ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")
SUGGESTION_LABEL_RE = re.compile(r"^\[(?:apply|exact|simp)\]\s*")
DIAGNOSTIC_RE = re.compile(r"^.*\.lean:\d+:\d+(?::\s|$)")
FORBIDDEN_SUGGESTION_RE = re.compile(
    r"(?<![\w'])\?_\b|(?<![\w'])sorry\b|(?<![\w'])admit\b|"
    r"\bby\?|\bexact\?|\bapply\?|\bsimp\?"
)
SORRY_WARNING_RE = re.compile(
    r"declaration\s+uses\s+['`]?sorry['`]?|declaration\s+contains\s+['`]?sorry['`]?",
    re.IGNORECASE,
)
DECL_TOKEN_RE = re.compile(
    r"^(?:exact|apply|refine)\s+\(?@?(?P<name>[^\s()\[\]{},]+)"
)
USING_TOKEN_RE = re.compile(
    r"\busing\s+\(?@?(?P<name>[^\s()\[\]{},]+)"
)
MODE_PRIORITY = {"exact": 0, "apply": 1, "simp": 2}

# Search is separate from verification. `apply?` may print candidates with
# remaining goals, so only a concrete, admission-free replay is accepted.
PROBES = {
    "exact": "exact?",
    "apply": "apply?",
    "simp": "simp?",
}


@dataclass(frozen=True)
class ProofBlock:
    kind: str
    body_start_line: int
    end_line: int
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
class ProjectTheoremIndex:
    names: frozenset[str]
    unique_suffixes: dict[str, str]
    path: str
    loaded: bool

    def resolve(self, candidate: str | None) -> str | None:
        if candidate is None:
            return None
        candidate = candidate.strip()
        if candidate in self.names:
            return candidate
        return self.unique_suffixes.get(candidate)


@dataclass(frozen=True)
class VerifiedCandidate:
    mode: str
    replacement: str
    kind: str
    candidate_origin: str
    candidate_name: str | None


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
    replacement: str
    kind: str
    candidate_origin: str
    candidate_name: str | None
    verified: bool = True
    admission_free: bool = True


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
    body_indices = [i for i in range(body_start, end_index) if significant(lines[i])]
    if len(body_indices) < min_body_lines:
        return None
    min_index = min(body_indices, key=lambda i: indent_width(lines[i]))
    return leading_indent(lines[min_index]), len(body_indices)


def find_typed_have_blocks(source: str, min_body_lines: int) -> list[ProofBlock]:
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
                body_start_line=body_start + 1,
                end_line=end_index,
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
                body_start_line=body_start + 1,
                end_line=end_index,
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
        blocks, key=lambda block: (block.body_start_index, block.end_index, block.kind)
    )


def top_level_tactic_chunks(source: str, block: ProofBlock) -> list[TacticChunk]:
    lines = source.splitlines(keepends=True)
    body_indices = [
        i for i in range(block.body_start_index, block.end_index) if significant(lines[i])
    ]
    if not body_indices:
        return []
    top_indent = min(indent_width(lines[i]) for i in body_indices)
    starts = [i for i in body_indices if indent_width(lines[i]) == top_indent]
    chunks: list[TacticChunk] = []
    for position, start in enumerate(starts):
        end = starts[position + 1] if position + 1 < len(starts) else block.end_index
        chunks.append(
            TacticChunk(
                start_line=start + 1,
                end_line=end,
                start_index=start,
                end_index=end,
                indent=leading_indent(lines[start]),
                significant_lines=sum(
                    1 for i in range(start, end) if significant(lines[i])
                ),
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
            if (
                start == 0
                and stop == len(chunks)
                and block.kind in {"have", "haveI"}
            ):
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
    regions.sort(key=lambda item: (-item.tactic_count, item.start_index, item.end_index))
    return regions if max_intervals is None else regions[:max_intervals]


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
            if key not in seen:
                regions.append(region)
                seen.add(key)
    return regions


def replace_region(source: str, region: Region, tactic: str) -> str:
    lines = source.splitlines(keepends=True)
    newline = "\r\n" if lines[region.start_index].endswith("\r\n") else "\n"
    replacement = f"{region.indent}{tactic}{newline}"
    return "".join(lines[: region.start_index] + [replacement] + lines[region.end_index :])


def parse_suggestions(output: str) -> list[str]:
    """Extract concrete `Try this:` tactics from Lean terminal output."""
    lines = ANSI_RE.sub("", output).splitlines()
    suggestions: list[str] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        marker = line.find("Try this:")
        if marker < 0:
            i += 1
            continue

        pieces: list[str] = []
        rest = line[marker + len("Try this:") :].strip()
        if rest:
            pieces.append(rest)
        i += 1

        while i < len(lines):
            current = lines[i]
            stripped = current.strip()
            if not stripped:
                break
            if "Try this:" in current or DIAGNOSTIC_RE.match(current):
                break
            if stripped.startswith("-- Remaining subgoals:") or stripped.startswith("-- ⊢"):
                break
            if stripped.startswith("--"):
                break
            if current[:1].isspace():
                pieces.append(stripped)
                i += 1
                continue
            break

        if pieces:
            pieces[0] = SUGGESTION_LABEL_RE.sub("", pieces[0]).strip()
            candidate = " ".join(piece for piece in pieces if piece).strip()
            if candidate and candidate not in suggestions:
                suggestions.append(candidate)
        if i < len(lines) and not lines[i].strip():
            i += 1

    return suggestions


def suggestion_is_admission_free(suggestion: str) -> bool:
    return FORBIDDEN_SUGGESTION_RE.search(suggestion) is None


def replay_is_admission_free(output: str) -> bool:
    return SORRY_WARNING_RE.search(ANSI_RE.sub("", output)) is None


def suggested_decl_name(replacement: str) -> str | None:
    replacement = replacement.strip()
    match = DECL_TOKEN_RE.search(replacement)
    if match is None:
        match = USING_TOKEN_RE.search(replacement)
    if match is None:
        return None
    return match.group("name").rstrip(".;:")


def _unique_suffixes(names: Sequence[str]) -> dict[str, str]:
    owners: dict[str, set[str]] = {}
    for name in names:
        parts = name.split(".")
        for i in range(len(parts)):
            suffix = ".".join(parts[i:])
            owners.setdefault(suffix, set()).add(name)
    return {
        suffix: next(iter(matches))
        for suffix, matches in owners.items()
        if len(matches) == 1
    }


def load_project_theorem_index(path: Path) -> ProjectTheoremIndex:
    display_path = str(path.relative_to(REPO_ROOT)) if path.is_relative_to(REPO_ROOT) else str(path)
    if not path.is_file():
        return ProjectTheoremIndex(frozenset(), {}, display_path, False)
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"could not read theorem catalog {display_path}: {exc}") from exc
    if not isinstance(payload, list):
        raise ValueError(f"theorem catalog {display_path} must contain a JSON array")
    names = sorted(
        {
            entry["name"]
            for entry in payload
            if isinstance(entry, dict) and isinstance(entry.get("name"), str)
        }
    )
    return ProjectTheoremIndex(
        frozenset(names), _unique_suffixes(names), display_path, True
    )


def classify_candidate(
    mode: str, replacement: str, theorem_index: ProjectTheoremIndex
) -> VerifiedCandidate:
    raw_name = suggested_decl_name(replacement)
    project_name = theorem_index.resolve(raw_name)
    if mode == "simp":
        return VerifiedCandidate(
            mode=mode,
            replacement=replacement,
            kind="automation_compression",
            candidate_origin="automation",
            candidate_name=None,
        )
    return VerifiedCandidate(
        mode=mode,
        replacement=replacement,
        kind="theorem_reuse",
        candidate_origin="project" if project_name is not None else "unknown",
        candidate_name=project_name if project_name is not None else raw_name,
    )


def candidate_rank(candidate: VerifiedCandidate) -> tuple[int, int]:
    if candidate.kind == "theorem_reuse" and candidate.candidate_origin == "project":
        return (0, MODE_PRIORITY[candidate.mode])
    if candidate.kind == "theorem_reuse":
        return (1, MODE_PRIORITY[candidate.mode])
    return (2, MODE_PRIORITY[candidate.mode])


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


def ordered_modes(modes: Sequence[str]) -> tuple[str, ...]:
    return tuple(sorted(modes, key=lambda mode: MODE_PRIORITY[mode]))


def audit_file(
    path: Path,
    *,
    modes: Sequence[str],
    theorem_index: ProjectTheoremIndex,
    min_body_lines: int,
    max_blocks: int | None,
    timeout: float,
    baseline: bool,
    scan_intervals: bool,
    min_tactics: int,
    max_span_tactics: int | None,
    max_intervals_per_block: int | None,
    max_findings: int | None,
    max_suggestions_per_search: int,
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

        verified: list[VerifiedCandidate] = []
        for mode in ordered_modes(modes):
            # Once theorem reuse exists, automation cannot outrank it.
            if mode == "simp" and any(item.kind == "theorem_reuse" for item in verified):
                break

            search_source = replace_region(source, region, PROBES[mode])
            label = f"line-{region.start_line}-{region.end_line}-{mode}-search"
            code, output, timed_out = run_probe(search_source, label, timeout)
            if timed_out:
                diagnostics.append(
                    f"{relative}:{region.start_line}-{region.end_line}: "
                    f"{mode} search timed out"
                )
                continue
            if code != 0:
                continue

            suggestions = parse_suggestions(output)[:max_suggestions_per_search]
            for suggestion in suggestions:
                if not suggestion_is_admission_free(suggestion):
                    continue
                replay_source = replace_region(source, region, suggestion)
                replay_label = f"line-{region.start_line}-{region.end_line}-{mode}-replay"
                replay_code, replay_output, replay_timed_out = run_probe(
                    replay_source, replay_label, timeout
                )
                if replay_timed_out:
                    diagnostics.append(
                        f"{relative}:{region.start_line}-{region.end_line}: "
                        f"{mode} replay timed out"
                    )
                    continue
                if replay_code != 0 or not replay_is_admission_free(replay_output):
                    continue

                candidate = classify_candidate(mode, suggestion, theorem_index)
                verified.append(candidate)
                break

            if any(
                item.kind == "theorem_reuse" and item.candidate_origin == "project"
                for item in verified
            ):
                break

        if not verified:
            continue
        best = min(verified, key=candidate_rank)
        findings.append(
            Finding(
                file=relative,
                scope=region.scope,
                block_kind=region.block_kind,
                start_line=region.start_line,
                end_line=region.end_line,
                original_lines=region.original_lines,
                tactic_count=region.tactic_count,
                mode=best.mode,
                replacement=best.replacement,
                kind=best.kind,
                candidate_origin=best.candidate_origin,
                candidate_name=best.candidate_name,
            )
        )

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


def resolve_catalog(value: str) -> Path:
    path = Path(value)
    if not path.is_absolute():
        path = REPO_ROOT / path
    return path.resolve()


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
        description="Find concrete, admission-free, replay-verified Lean proof replacements."
    )
    result.add_argument("files", nargs="+", help="repo-relative .lean files")
    result.add_argument(
        "--modes",
        type=parse_modes,
        default=tuple(PROBES),
        help="comma-separated search modes (default: exact,apply,simp)",
    )
    result.add_argument(
        "--catalog",
        default=str(DEFAULT_CATALOG.relative_to(REPO_ROOT)),
        help="generated theorem catalog used to identify project theorem reuse",
    )
    result.add_argument("--min-body-lines", type=int, default=2)
    result.add_argument("--max-blocks", type=int)
    result.add_argument("--no-intervals", action="store_true")
    result.add_argument("--min-tactics", type=int, default=2)
    result.add_argument("--max-span-tactics", type=int, default=6)
    result.add_argument("--max-intervals-per-block", type=int, default=12)
    result.add_argument("--max-findings", type=int)
    result.add_argument(
        "--max-suggestions-per-search",
        type=int,
        default=4,
        help="maximum concrete suggestions replayed for each search (default: 4)",
    )
    result.add_argument("--timeout", type=float, default=30.0)
    result.add_argument("--no-baseline", action="store_true")
    result.add_argument("--json", action="store_true")
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
    if args.max_suggestions_per_search < 1:
        args_parser.error("--max-suggestions-per-search must be at least 1")
    if args.timeout <= 0:
        args_parser.error("--timeout must be positive")

    try:
        files = resolve_files(args.files)
        theorem_index = load_project_theorem_index(resolve_catalog(args.catalog))
    except ValueError as exc:
        args_parser.error(str(exc))

    findings: list[Finding] = []
    diagnostics: list[str] = []
    for path in files:
        file_findings, file_diagnostics = audit_file(
            path,
            modes=args.modes,
            theorem_index=theorem_index,
            min_body_lines=args.min_body_lines,
            max_blocks=args.max_blocks,
            timeout=args.timeout,
            baseline=not args.no_baseline,
            scan_intervals=not args.no_intervals,
            min_tactics=args.min_tactics,
            max_span_tactics=args.max_span_tactics,
            max_intervals_per_block=args.max_intervals_per_block,
            max_findings=args.max_findings,
            max_suggestions_per_search=args.max_suggestions_per_search,
        )
        findings.extend(file_findings)
        diagnostics.extend(file_diagnostics)

    if args.json:
        print(
            json.dumps(
                {
                    "catalog": {
                        "path": theorem_index.path,
                        "loaded": theorem_index.loaded,
                        "project_theorems": len(theorem_index.names),
                    },
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
                size = (
                    f"{item.tactic_count} top-level tactic(s), "
                    f"{item.original_lines} line(s)"
                )
            else:
                size = f"{item.original_lines} proof line(s)"
            print(
                f"{item.file}:{item.start_line}-{item.end_line}: "
                f"{item.kind}/{item.candidate_origin} "
                f"{item.scope}/{item.block_kind} {item.mode} can replace {size}"
            )
            if item.candidate_name is not None:
                print(f"  candidate: {item.candidate_name}")
            print(f"  {item.replacement}")
            print("  verified by replay: yes (admission-free)")
        if not findings and not diagnostics:
            print("No proof-reuse candidates found.")

    return 1 if diagnostics else 0


if __name__ == "__main__":
    sys.exit(main())
