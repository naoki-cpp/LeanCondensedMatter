#!/usr/bin/env python3
"""Rank Lean theorem proofs by source-line span (not kernel complexity).

Run: python3 scripts/rank_proofs.py --top 40
Only theorem/lemma declarations with tactic proofs are ranked.
The source scanner ignores nested block comments, line comments and strings.
"""

import argparse
import csv
import re
import sys
from pathlib import Path

COMMAND = re.compile(
    r"(?m)^(?:(?:@\[[^\n\]]*\])\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|local)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|example|structure|class|inductive|"
    r"namespace|section|end|variable|open|attribute|set_option|export|"
    r"notation|infix|infixl|infixr|prefix|postfix|macro|syntax|elab|"
    r"initialize|mutual|omit|include|#\w+)\b"
    r"(?:\s+([^\s(:={]+))?"
)
PROOF = re.compile(r":=\s*by\b")


def mask_noncode(source: str) -> str:
    """Hide comments and strings while preserving character positions and line breaks."""
    result = list(source)
    i = 0
    depth = 0
    quoted = False
    line_comment = False
    while i < len(source):
        c = source[i]
        pair = source[i:i+2]
        if c == "\n":
            line_comment = False
        if depth:
            if pair == "/-":
                depth += 1
                width = 2
            elif pair == "-/":
                depth -= 1
                width = 2
            else:
                width = 1
        elif line_comment:
            width = 1
        elif quoted:
            if c == "\\":
                width = min(2, len(source) - i)
            else:
                if c == '"':
                    quoted = False
                width = 1
        elif pair == "/-":
            depth = 1
            width = 2
        elif pair == "--":
            line_comment = True
            width = 2
        elif c == '"':
            quoted = True
            width = 1
        else:
            i += 1
            continue
        for j in range(i, i + width):
            if source[j] != "\n":
                result[j] = " "
        i += width
    return "".join(result)


def entries(path: Path, root: Path):
    source = path.read_text(encoding="utf-8")
    masked = mask_noncode(source)
    commands = list(COMMAND.finditer(masked))
    for index, command in enumerate(commands):
        kind, name = command.group(1), command.group(2)
        if kind not in ("theorem", "lemma") or not name:
            continue
        boundary = commands[index + 1].start() if index + 1 < len(commands) else len(source)
        match = PROOF.search(masked, command.end(), boundary)
        if match is None:
            continue
        proof_start = masked.count("\n", 0, match.start()) + 1
        proof = masked[match.start():boundary].rstrip()
        if not proof:
            continue
        proof_end = proof_start + proof.count("\n")
        yield (proof_end - proof_start + 1, str(path.relative_to(root)),
               name, proof_start, proof_end)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--top", type=int, default=40, help="0 lists all proofs")
    parser.add_argument("--csv", action="store_true", help="CSV output for further auditing")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()
    source_root = root / "LeanCondensedMatter"
    if not source_root.is_dir():
        parser.error(f"Lean source tree not found: {source_root}")
    ranked = sorted(
        (entry for path in source_root.rglob("*.lean") for entry in entries(path, root)),
        key=lambda entry: (-entry[0], entry[1], entry[3]),
    )
    selected = ranked if args.top == 0 else ranked[:args.top]
    writer = csv.writer(sys.stdout)
    if args.csv:
        writer.writerow(("proof_lines", "file", "theorem", "start", "end"))
        writer.writerows(selected)
    else:
        print(f"Ranked {len(ranked)} tactic-style theorem/lemma proofs in {source_root}")
        for n, file, theorem, start, end in selected:
            print(f"{n:4d}  {file}:{start}-{end}  {theorem}")


if __name__ == "__main__":
    main()
