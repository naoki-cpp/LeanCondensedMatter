from __future__ import annotations

import argparse
import runpy
import sys
import traceback
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"


@dataclass(frozen=True)
class ArchitectureCheck:
    name: str
    script: str
    scope: str


# This manifest owns architecture-audit registration only. Dependency DAGs and uniform source
# contracts live in shared specifications under scripts/architecture/. Scopes are optional local
# filters and must not become a second architecture model. A checker with scope `all` participates
# in both focused scopes.
CHECKS: tuple[ArchitectureCheck, ...] = (
    ArchitectureCheck("declarative architecture graphs", "check_architecture_graphs.py", "core"),
    ArchitectureCheck("declarative source contracts", "check_source_contracts.py", "all"),
    ArchitectureCheck("transport physical hierarchy", "check_transport_hierarchy.py", "core"),
    ArchitectureCheck("diagrammatics layer architecture", "check_diagrammatics_layer_architecture.py", "second-quantization"),
)

SCOPES = ("core", "second-quantization", "all")

# `check_*.py` is reserved for checks that should normally participate in architecture CI.
# Keep explicit exceptions here so adding a new checker cannot silently bypass the registry.
NON_ARCHITECTURE_CHECK_SCRIPTS = {
    "check_and_fix_warnings.py",
    "check_architecture.py",
}


def architecture_script_candidates() -> set[str]:
    return {
        path.name
        for path in SCRIPTS.glob("check_*.py")
        if path.name not in NON_ARCHITECTURE_CHECK_SCRIPTS
    }


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

    for script in sorted(architecture_script_candidates() - seen_scripts):
        errors.append(f"unregistered architecture check: scripts/{script}")

    return errors


def selected_checks(scope: str) -> tuple[ArchitectureCheck, ...]:
    if scope == "all":
        return CHECKS
    return tuple(check for check in CHECKS if check.scope in (scope, "all"))


def load_checker_main(check: ArchitectureCheck) -> Callable[[], int | None]:
    path = SCRIPTS / check.script
    namespace = runpy.run_path(
        str(path),
        run_name=f"_architecture_check_{path.stem}",
    )
    main_fn = namespace.get("main")
    if not callable(main_fn):
        raise TypeError(f"scripts/{check.script} must expose callable main()")
    return main_fn


def system_exit_code(check: ArchitectureCheck, exc: SystemExit) -> int:
    if exc.code is None:
        return 0
    if isinstance(exc.code, int):
        return exc.code
    print(
        f"scripts/{check.script} exited with non-integer status: {exc.code}",
        file=sys.stderr,
    )
    return 1


def checker_exit_code(check: ArchitectureCheck) -> int:
    try:
        result = load_checker_main(check)()
    except SystemExit as exc:
        return system_exit_code(check, exc)
    except Exception:
        traceback.print_exc()
        return 1

    if result is None:
        return 0
    if isinstance(result, int):
        return result

    print(
        f"scripts/{check.script} main() returned unsupported result: {result!r}",
        file=sys.stderr,
    )
    return 1


def run_checks(scope: str) -> int:
    checks = selected_checks(scope)
    failures: list[ArchitectureCheck] = []

    for index, check in enumerate(checks, start=1):
        print(f"[{index}/{len(checks)}] {check.name} ({check.script})", flush=True)
        if checker_exit_code(check) != 0:
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
