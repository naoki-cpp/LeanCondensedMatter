from __future__ import annotations

import argparse
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"


@dataclass(frozen=True)
class ArchitectureCheck:
    name: str
    script: str
    scope: str


# This manifest is the explicit CI allowlist for source architecture checks. Local analysis scripts
# may also use a check_*.py name without being promoted automatically into CI. Dependency DAGs and
# uniform source contracts live in shared specifications under scripts/architecture/. Scopes are
# optional local filters and must not become a second architecture model. A checker with scope
# `all` participates in both focused scopes.
CHECKS: tuple[ArchitectureCheck, ...] = (
    ArchitectureCheck("declarative architecture graphs", "check_architecture_graphs.py", "core"),
    ArchitectureCheck("declarative source contracts", "check_source_contracts.py", "all"),
    ArchitectureCheck("transport physical hierarchy", "check_transport_hierarchy.py", "core"),
    ArchitectureCheck("diagrammatics umbrella boundaries", "check_diagrammatics_umbrella_boundaries.py", "second-quantization"),
)

SCOPES = ("core", "second-quantization", "all")


def validate_manifest() -> list[str]:
    errors: list[str] = []
    seen_scripts: set[str] = set()

    for check in CHECKS:
        if check.script in seen_scripts:
            errors.append(f"duplicate architecture check registration: {check.script}")
        seen_scripts.add(check.script)

        path = SCRIPTS / check.script
        if not path.is_file():
            errors.append(f"registered architecture check does not exist: scripts/{check.script}")

        if check.scope not in SCOPES:
            errors.append(f"unknown architecture check scope `{check.scope}` for {check.script}")

    return errors


def selected_checks(scope: str) -> tuple[ArchitectureCheck, ...]:
    if scope == "all":
        return CHECKS
    return tuple(check for check in CHECKS if check.scope in (scope, "all"))


def run_checks(scope: str) -> int:
    checks = selected_checks(scope)
    failures: list[ArchitectureCheck] = []

    for index, check in enumerate(checks, start=1):
        print(f"[{index}/{len(checks)}] {check.name} ({check.script})", flush=True)
        if subprocess.run([sys.executable, str(SCRIPTS / check.script)]).returncode != 0:
            failures.append(check)

    if failures:
        print("Architecture checks failed:", file=sys.stderr)
        for check in failures:
            print(f"- {check.name}: scripts/{check.script}", file=sys.stderr)
        return 1

    print(f"Architecture checks passed ({len(checks)} checks, scope={scope}).")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Run LeanCondensedMatter architecture checks.")
    parser.add_argument(
        "--scope",
        choices=SCOPES,
        default="all",
        help="optional local filter (default: all)",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="list registered checks for the selected scope without running them",
    )
    args = parser.parse_args()

    manifest_errors = validate_manifest()
    if manifest_errors:
        print("Architecture check manifest is invalid:", file=sys.stderr)
        for error in manifest_errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    if args.list:
        for check in selected_checks(args.scope):
            print(f"{check.scope}: {check.script} -- {check.name}")
        return 0

    return run_checks(args.scope)


if __name__ == "__main__":
    raise SystemExit(main())
