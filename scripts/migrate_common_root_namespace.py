from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LIBRARY = ROOT / "LeanCondensedMatter"
SQ = LIBRARY / "SecondQuantization"
COMMON = SQ / "Common"
AUDIT = ROOT / "scripts" / "audit_second_quantization_namespaces.py"
ARCHITECTURE = ROOT / "scripts" / "check_second_quantization_architecture.py"
ROADMAP = ROOT / "notes" / "roadmaps" / "second-quantization-refactor.md"
LEDGER = ROOT / "notes" / "migrations" / "common-canonical-namespace.md"

TARGET_FILES = (
    COMMON / "Algebra" / "OneParticleSpace.lean",
    COMMON / "Algebra" / "Statistics.lean",
    COMMON / "Diagrammatics" / "Leg.lean",
)

PUBLIC_NAMES = (
    "localLegOfLeg_legOfVertexLocal",
    "vertexOfLeg_legOfVertexLocal",
    "orderedQuarticLegEquiv",
    "quarticVertexEquiv",
    "legOfVertexLocal",
    "localLegOfLeg",
    "quarticLegEquiv",
    "vertexOfLeg",
    "modeCount",
    "Statistics",
)

IDENT_CHARS = "A-Za-z0-9_."


def wrap_in_common(path: Path) -> None:
    original = path.read_text(encoding="utf-8")
    if "namespace SecondQuantization\nnamespace Common" in original:
        return

    opening = "namespace SecondQuantization\n"
    if original.count(opening) != 1:
        raise RuntimeError(f"unexpected root namespace layout in {path.relative_to(ROOT)}")
    updated = original.replace(opening, opening + "namespace Common\n", 1)

    closing = "\nend SecondQuantization"
    position = updated.rfind(closing)
    if position < 0:
        raise RuntimeError(f"missing root namespace close in {path.relative_to(ROOT)}")
    updated = updated[:position] + "\nend Common\n" + updated[position:]
    path.write_text(updated, encoding="utf-8")


def replace_unqualified(text: str, old: str, new: str) -> str:
    pattern = re.compile(rf"(?<![{IDENT_CHARS}]){re.escape(old)}(?![A-Za-z0-9_])")
    return pattern.sub(new, text)


def migrate_external_callers() -> None:
    for path in sorted(LIBRARY.rglob("*.lean")):
        original = path.read_text(encoding="utf-8")
        updated = original

        for name in PUBLIC_NAMES:
            updated = updated.replace(
                f"SecondQuantization.{name}", f"SecondQuantization.Common.{name}"
            )

        if not path.is_relative_to(COMMON):
            for name in PUBLIC_NAMES:
                updated = replace_unqualified(updated, name, f"Common.{name}")

        if path == COMMON / "Thermal" / "BlochDeDominicis" / "PairingWeight.lean":
            updated = updated.replace(
                "SecondQuantization.Statistics", "SecondQuantization.Common.Statistics"
            )

        if updated != original:
            path.write_text(updated, encoding="utf-8")


def update_audit_checker() -> None:
    original = AUDIT.read_text(encoding="utf-8")
    updated = original

    constant_marker = 'STATISTIC_NAME_RE = re.compile(r"(?:Boson|Bosonic|Fermion|Fermionic)")\n'
    constant_replacement = constant_marker + '''ALLOWED_EXTERNAL_DECLARATIONS = {
    (
        "LeanCondensedMatter/SecondQuantization/Common/Thermal/"
        "BlochDeDominicis/PairingWeight.lean",
        "Pairing.weight",
        "Combinatorics",
    ),
}
'''
    if constant_marker not in updated:
        raise RuntimeError("namespace audit constant layout changed")
    updated = updated.replace(constant_marker, constant_replacement, 1)

    main_start = updated.index("def main() -> int:\n")
    main_replacement = '''def collect_findings() -> tuple[list[Finding], list[Finding], Counter]:
    misplaced: list[Finding] = []
    statistic_names: list[Finding] = []
    file_counts = Counter()

    for path in sorted(SQ.rglob("*.lean")):
        owner = path.relative_to(SQ).parts[0]
        file_counts[owner if owner in OWNERS else "Root"] += 1
        file_misplaced, file_statistics = audit_file(path)
        misplaced.extend(file_misplaced)
        statistic_names.extend(file_statistics)

    misplaced = [
        finding
        for finding in misplaced
        if (
            str(finding.path.relative_to(ROOT)),
            finding.name,
            finding.namespace,
        )
        not in ALLOWED_EXTERNAL_DECLARATIONS
    ]
    return misplaced, statistic_names, file_counts


def main() -> int:
    misplaced, statistic_names, file_counts = collect_findings()

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
    return 1 if misplaced or statistic_names else 0


if __name__ == "__main__":
    raise SystemExit(main())
'''
    updated = updated[:main_start] + main_replacement
    AUDIT.write_text(updated, encoding="utf-8")


def update_architecture_guard() -> None:
    original = ARCHITECTURE.read_text(encoding="utf-8")
    updated = original

    import_marker = "from pathlib import Path\n"
    import_replacement = import_marker + "\nfrom audit_second_quantization_namespaces import collect_findings\n"
    if import_marker not in updated:
        raise RuntimeError("architecture guard import layout changed")
    updated = updated.replace(import_marker, import_replacement, 1)

    function_marker = "def check_entry_point(errors: list[str]) -> None:\n"
    function_replacement = '''def check_declaration_namespaces(errors: list[str]) -> None:
    misplaced, statistic_names, _ = collect_findings()
    for finding in misplaced:
        errors.append(
            "declaration outside path-owned namespace: "
            f"{relative(finding.path)}:{finding.line}: "
            f"{finding.kind} {finding.name} in {finding.namespace}"
        )
    for finding in statistic_names:
        errors.append(
            "statistic-encoded declaration name: "
            f"{relative(finding.path)}:{finding.line}: {finding.name}"
        )


def check_entry_point(errors: list[str]) -> None:
'''
    if function_marker not in updated:
        raise RuntimeError("architecture guard function layout changed")
    updated = updated.replace(function_marker, function_replacement, 1)

    call_marker = "    check_fermionic_namespace(errors)\n    check_entry_point(errors)\n"
    call_replacement = (
        "    check_fermionic_namespace(errors)\n"
        "    check_declaration_namespaces(errors)\n"
        "    check_entry_point(errors)\n"
    )
    if call_marker not in updated:
        raise RuntimeError("architecture guard main layout changed")
    updated = updated.replace(call_marker, call_replacement, 1)

    ARCHITECTURE.write_text(updated, encoding="utf-8")


def update_documentation() -> None:
    for path in sorted((ROOT / "notes").rglob("*.md")):
        original = path.read_text(encoding="utf-8")
        updated = original.replace(
            "SecondQuantization.Statistics", "SecondQuantization.Common.Statistics"
        )
        for name in PUBLIC_NAMES:
            updated = updated.replace(f"`{name}", f"`Common.{name}")
        if updated != original:
            path.write_text(updated, encoding="utf-8")

    roadmap = ROADMAP.read_text(encoding="utf-8")
    completed_marker = "### Discrete fermionic Dyson ownership\n"
    completed_section = '''### Common declaration namespaces

The remaining path-owned declarations in the root `SecondQuantization` namespace now live under
`SecondQuantization.Common`:

- `Common.Statistics` and its exchange-sign API;
- `Common.modeCount`;
- the quartic-leg indexing equivalences and projections in `Common.Diagrammatics.Leg`.

`Combinatorics.Pairing.weight` remains in `Combinatorics` intentionally because it extends the
combinatorial pairing type with a physics-supplied weight. The namespace audit records this as the
single explicit cross-namespace extension.

'''
    if completed_marker not in roadmap:
        raise RuntimeError("roadmap completed-section marker changed")
    roadmap = roadmap.replace(completed_marker, completed_section + completed_marker, 1)

    old_r1 = '''### R1 — declaration namespaces

Move declarations that still live directly in `SecondQuantization` into exactly one of:

```lean
SecondQuantization.Common
SecondQuantization.Fermionic
SecondQuantization.Bosonic
```

The migration must update every in-repository caller in the same PR. No root-namespace forwarding
aliases should remain.
'''
    new_r1 = '''### R1 — declaration namespaces

Complete. Every declaration owned by a `Common`, `Fermionic`, or `Bosonic` module is now in the
matching namespace. The CI namespace audit rejects future path/namespace mismatches and
statistic-encoded declaration names. The only allowlisted exception is the intentional extension
`Combinatorics.Pairing.weight`.
'''
    if old_r1 not in roadmap:
        raise RuntimeError("roadmap R1 block changed")
    ROADMAP.write_text(roadmap.replace(old_r1, new_r1), encoding="utf-8")

    LEDGER.parent.mkdir(parents=True, exist_ok=True)
    LEDGER.write_text(
        '''# Common canonical namespace migration

The following root declarations were moved without compatibility aliases:

```text
SecondQuantization.Statistics
  -> SecondQuantization.Common.Statistics

SecondQuantization.modeCount
  -> SecondQuantization.Common.modeCount

SecondQuantization.orderedQuarticLegEquiv
  -> SecondQuantization.Common.orderedQuarticLegEquiv
SecondQuantization.quarticVertexEquiv
  -> SecondQuantization.Common.quarticVertexEquiv
SecondQuantization.quarticLegEquiv
  -> SecondQuantization.Common.quarticLegEquiv
SecondQuantization.vertexOfLeg
  -> SecondQuantization.Common.vertexOfLeg
SecondQuantization.localLegOfLeg
  -> SecondQuantization.Common.localLegOfLeg
SecondQuantization.legOfVertexLocal
  -> SecondQuantization.Common.legOfVertexLocal
```

The associated quartic-leg inverse lemmas moved with the definitions. All in-repository callers use
the new names. `Combinatorics.Pairing.weight` intentionally remains in `Combinatorics` as an
extension of the pairing type, while its statistics argument is now
`SecondQuantization.Common.Statistics`.
''',
        encoding="utf-8",
    )


def validate() -> None:
    errors: list[str] = []

    for path in TARGET_FILES:
        text = path.read_text(encoding="utf-8")
        if "namespace SecondQuantization\nnamespace Common" not in text:
            errors.append(f"missing Common namespace in {path.relative_to(ROOT)}")

    for path in sorted(LIBRARY.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        if "SecondQuantization.Statistics" in text:
            errors.append(f"legacy qualified Statistics reference in {path.relative_to(ROOT)}")
        if path.is_relative_to(COMMON):
            continue
        for name in PUBLIC_NAMES:
            pattern = re.compile(rf"(?<![{IDENT_CHARS}]){re.escape(name)}(?![A-Za-z0-9_])")
            if pattern.search(text):
                errors.append(f"unqualified `{name}` outside Common in {path.relative_to(ROOT)}")

    if errors:
        raise RuntimeError("Common namespace migration incomplete:\n" + "\n".join(errors))


def main() -> None:
    for path in TARGET_FILES:
        wrap_in_common(path)
    migrate_external_callers()
    update_audit_checker()
    update_architecture_guard()
    update_documentation()
    validate()


if __name__ == "__main__":
    main()
