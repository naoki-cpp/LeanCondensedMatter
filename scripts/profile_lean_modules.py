#!/usr/bin/env python3
"""Advisory declaration-body cost survey using Lean's native heartbeat profiler."""

import argparse
import csv
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = "LeanCondensedMatter"
SHARD_SIZE = 40
THRESHOLDS = {"1", "10", "100", "1000"}
BODY = re.compile(
    r"\s*\[Elab\.definition\.value\]\s+\[(\d+(?:\.\d+)?)\]\s+✅️?\s+(\S+)"
)
RANK_FIELDS = ["module", "declaration", "raw_ticks", "heartbeats"]
STATUS_FIELDS = ["module", "status", "detail"]


def write_tsv(path, fields, rows):
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, delimiter="\t")
        writer.writeheader()
        writer.writerows(rows)


def read_tsv(path):
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def plan(scope, smoke):
    if not re.fullmatch(r"LeanCondensedMatter(?:\.[A-Za-z_][A-Za-z0-9_]*)*", scope):
        raise ValueError("Scope must be a dotted project module or namespace prefix")
    tracked = subprocess.check_output(
        ["git", "ls-files", "-z", "--", ROOT + ".lean", ROOT], text=True
    )
    modules = sorted(
        path[:-5].replace("/", ".")
        for path in tracked.split("\0")
        if path.endswith(".lean")
        and (path == ROOT + ".lean" or path.startswith(ROOT + "/"))
    )
    if smoke:
        modules = [
            ROOT + ".Analysis.PowerSeries.Normalization",
            ROOT + ".Combinatorics.FiniteSumModEq",
        ]
        if not all(Path(m.replace(".", "/") + ".lean").is_file() for m in modules):
            raise ValueError("A survey smoke-test module is missing")
    else:
        modules = [m for m in modules if m == scope or m.startswith(scope + ".")]
    if not modules:
        raise ValueError("No tracked Lean modules match scope")
    shard_size = 1 if smoke else SHARD_SIZE
    matrix = {
        "include": [
            {"shard": i // shard_size + 1, "modules": modules[i:i + shard_size]}
            for i in range(0, len(modules), shard_size)
        ]
    }
    return matrix


def profile(modules, threshold, output):
    if threshold not in THRESHOLDS:
        raise ValueError("Unsupported heartbeat threshold")
    output.mkdir(parents=True, exist_ok=True)
    logs = output / "logs"
    logs.mkdir(exist_ok=True)
    statuses, rows = [], []
    for module in modules:
        source = module.replace(".", "/") + ".lean"
        log = logs / (module + ".log")
        status, detail = "ok", ""
        try:
            with log.open("w", encoding="utf-8") as handle:
                result = subprocess.run(
                    ["lake", "env", "lean", "-DrelaxedAutoImplicit=false",
                     "-DmaxSynthPendingDepth=3", "-DElab.async=false",
                     "-Dtrace.profiler=true", "-Dtrace.profiler.useHeartbeats=true",
                     f"-Dtrace.profiler.threshold={int(threshold) * 1000}", source],
                    stdout=handle, stderr=subprocess.STDOUT, timeout=180, check=False,
                )
            if result.returncode:
                status, detail = "failed", f"exit {result.returncode}"
        except subprocess.TimeoutExpired:
            status, detail = "timeout", "180 seconds"
        except OSError as exc:
            status, detail = "failed", type(exc).__name__
        if status == "ok":
            counts = {}
            with log.open(encoding="utf-8", errors="replace") as handle:
                for line in handle:
                    match = BODY.fullmatch(line.rstrip("\n"))
                    if match:
                        ticks, name = int(float(match[1])), match[2]
                        counts[name] = max(counts.get(name, 0), ticks)
            rows.extend(
                {"module": module, "declaration": name, "raw_ticks": ticks,
                 "heartbeats": f"{ticks / 1000:.3f}"}
                for name, ticks in counts.items()
            )
        statuses.append({"module": module, "status": status, "detail": detail})
        print(f"{module}: {status} {detail}", flush=True)
        # Preserve completed measurements even if a later file or job fails.
        write_tsv(output / "coverage.tsv", STATUS_FIELDS, statuses)
        write_tsv(output / "heartbeat-ranking.tsv", RANK_FIELDS, rows)
    return all(row["status"] == "ok" for row in statuses)


def merge(matrix, threshold, artifacts, output, summary):
    expected = {m for entry in matrix["include"] for m in entry["modules"]}
    statuses, counts = {}, {}
    for path in sorted(artifacts.glob("native-profiler-survey-shard-*/coverage.tsv")):
        for row in read_tsv(path):
            if row["module"] not in expected or row["module"] in statuses:
                raise ValueError("Unexpected or duplicate module coverage")
            statuses[row["module"]] = row
        ranking = path.with_name("heartbeat-ranking.tsv")
        if not ranking.is_file():
            for row in read_tsv(path):
                statuses[row["module"]]["status"] = "missing-ranking"
            continue
        for row in read_tsv(ranking):
            key = (row["module"], row["declaration"])
            ticks = int(row["raw_ticks"])
            counts[key] = max(counts.get(key, 0), ticks)
    for module in expected - statuses.keys():
        statuses[module] = {"module": module, "status": "missing", "detail": "No shard result"}
    rows = [
        {"module": module, "declaration": name, "raw_ticks": ticks,
         "heartbeats": f"{ticks / 1000:.3f}"}
        for (module, name), ticks in sorted(counts.items(), key=lambda item: (-item[1], item[0]))
        if statuses.get(module, {}).get("status") == "ok"
    ]
    output.mkdir(parents=True, exist_ok=True)
    write_tsv(output / "coverage.tsv", STATUS_FIELDS, [statuses[m] for m in sorted(expected)])
    write_tsv(output / "heartbeat-ranking.tsv", RANK_FIELDS, rows)
    (output / "metadata.json").write_text(json.dumps({
        "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "heartbeat_threshold": int(threshold),
        "expected_modules": len(expected),
        "profiled_modules": sum(row["status"] == "ok" for row in statuses.values()),
    }, indent=2) + "\n", encoding="utf-8")
    ok = sum(row["status"] == "ok" for row in statuses.values())
    with summary.open("a", encoding="utf-8") as handle:
        handle.write(f"## Native Lean heartbeat survey\n\n"
                     f"Profiled modules: **{ok}/{len(expected)}**; "
                     f"reported declaration bodies: **{len(rows)}**.\n\n"
                     f"Threshold: above {threshold} user heartbeats. "
                     "Only successful Elab.definition.value spans are ranked, "
                     "using the maximum per module and declaration. "
                     "Statement elaboration, unreported spans, and wall time are excluded. "
                     "A module with no matching spans is not a proof of zero cost.\n\n")
        handle.write("| Heartbeats | Module | Declaration |\n|---:|---|---|\n")
        for row in rows[:50]:
            handle.write(f"| {row['heartbeats']} | {row['module']} | {row['declaration']} |\n")
        if ok != len(expected):
            handle.write("\nIncomplete survey; see coverage.tsv for missing or failed modules.\n")
    return ok == len(expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("plan")
    p.add_argument("--scope", default=ROOT)
    p.add_argument("--smoke", action="store_true")
    p = sub.add_parser("profile")
    p.add_argument("--output", type=Path, required=True)
    p = sub.add_parser("merge")
    p.add_argument("--artifacts", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "plan":
        print(json.dumps(plan(args.scope, args.smoke), separators=(",", ":")))
        return 0
    threshold = os.environ["HEARTBEAT_THRESHOLD"]
    if args.command == "profile":
        return 0 if profile(json.loads(os.environ["SURVEY_MODULES"]), threshold, args.output) else 1
    return 0 if merge(
        json.loads(os.environ["SURVEY_MATRIX"]), threshold,
        args.artifacts, args.output, Path(os.environ["GITHUB_STEP_SUMMARY"]),
    ) else 1


if __name__ == "__main__":
    sys.exit(main())
