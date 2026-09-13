#!/usr/bin/env python3
"""Merge proof-guided theorem replacement findings into the generated theorem catalog."""

from __future__ import annotations

import json
from pathlib import Path

CATALOG_PATH = Path("docs/generated/theorems.json")
REPLACEMENTS_PATH = Path("docs/generated/theorem-replacements.json")
MARKDOWN_PATH = Path("docs/generated/theorems.md")


def load_json(path: Path):
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def main() -> None:
    catalog = load_json(CATALOG_PATH)
    findings = load_json(REPLACEMENTS_PATH)

    by_name = {entry["name"]: entry for entry in catalog}
    if len(by_name) != len(catalog):
        raise RuntimeError("theorem catalog contains duplicate declaration names")

    finding_targets = set()
    replacement_rows: list[tuple[str, list[str]]] = []
    defeq_rows: list[tuple[str, list[str]]] = []

    for finding in findings:
        target = finding["target"]
        if target in finding_targets:
            raise RuntimeError(f"duplicate replacement finding for {target}")
        finding_targets.add(target)

        entry = by_name.get(target)
        if entry is None:
            raise RuntimeError(f"replacement finding target is absent from theorem catalog: {target}")

        defeq = sorted(set(finding.get("definitionallyEquivalentTo", [])))
        replacements = sorted(
            {
                candidate["name"]
                for candidate in finding.get("replacementCandidates", [])
                if candidate["name"] != entry.get("directWrapperOf")
            }
        )

        unknown = [name for name in defeq + replacements if name not in by_name]
        if unknown:
            raise RuntimeError(
                f"replacement finding for {target} references unknown declarations: {unknown}"
            )

        entry["definitionallyEquivalentTo"] = defeq
        entry["replacementCandidates"] = replacements
        entry["replacementCandidateCount"] = len(replacements)

        if defeq:
            defeq_rows.append((target, defeq))
        if replacements:
            replacement_rows.append((target, replacements))

    missing_findings = sorted(set(by_name) - finding_targets)
    if missing_findings:
        raise RuntimeError(
            "replacement audit is missing theorem catalog entries: " + ", ".join(missing_findings[:10])
        )

    with CATALOG_PATH.open("w", encoding="utf-8") as handle:
        json.dump(catalog, handle, ensure_ascii=False, indent=2)
        handle.write("\n")

    with MARKDOWN_PATH.open("a", encoding="utf-8") as handle:
        handle.write("\n## Proof-guided theorem replacement review queue\n\n")
        handle.write(
            "This advisory queue contains source-declared project theorems whose compiled proof "
            "already depends on another project theorem that Lean can replay as a direct "
            "specialization. Existing direct-wrapper relations are omitted here.\n\n"
        )
        handle.write(f"Definitionally equivalent proof-dependency targets: {len(defeq_rows)}\n\n")
        handle.write(f"Replacement-candidate targets: {len(replacement_rows)}\n\n")
        for target, replacements in replacement_rows:
            rendered = ", ".join(f"`{name}`" for name in replacements)
            handle.write(f"- `{target}` → {rendered}\n")

    print(
        "Merged theorem replacement audit: "
        f"{len(defeq_rows)} defeq targets; "
        f"{len(replacement_rows)} replacement targets"
    )


if __name__ == "__main__":
    main()
