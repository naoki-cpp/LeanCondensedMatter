"""Produce a non-blocking retained-theorem re-audit report from compiled catalog data.

A low consumer count or a direct wrapper is a review signal, never a deletion rule.
The optional comparison is against previously published graph-data, not a record
of when each declaration was last semantically reviewed.
"""

import argparse
import json
from pathlib import Path

EVIDENCE_FIELDS = (
    "statement", "module", "compiledConsumers", "simpLemma", "directWrapperOf",
    "terminal", "projectAxioms", "externalAxioms",
    "definitionallyEquivalentTo", "replacementCandidates",
    "mathlibDefinitionallyEquivalentTo", "mathlibReplacementCandidates",
    "directWrapperTargetModule", "crossModuleDirectWrapper",
)


def audit(current, previous=None):
    """Return the full advisory queues and reproducible evidence changes."""
    current_by_name = {entry["name"]: entry for entry in current}
    if len(current_by_name) != len(current):
        raise ValueError("duplicate theorem names in current catalog")
    if previous is not None:
        previous_by_name = {entry["name"]: entry for entry in previous}
        if len(previous_by_name) != len(previous):
            raise ValueError("duplicate theorem names in previous catalog")
    else:
        previous_by_name = None

    retained = [row for row in current if row.get("retainedMention")]
    retained.sort(key=lambda row: row["name"])
    no_signal = []
    zero_consumer = []
    zero_consumer_wrappers = []
    changed = []
    newly_retained = []
    replacement_candidates = []
    for row in retained:
        count = row["compiledConsumerCount"]
        has_signal = bool(row["terminal"] or count <= 1 or row.get("directWrapperOf"))
        if not has_signal:
            no_signal.append(row["name"])
        if count == 0:
            zero_consumer.append(row["name"])
            if row.get("directWrapperOf"):
                zero_consumer_wrappers.append(row["name"])
        candidates = {
            field: row.get(field) or []
            for field in (
                "definitionallyEquivalentTo", "replacementCandidates",
                "mathlibDefinitionallyEquivalentTo", "mathlibReplacementCandidates",
            )
            if row.get(field)
        }
        if candidates:
            replacement_candidates.append({"name": row["name"], "candidates": candidates})
        if previous_by_name is not None:
            old = previous_by_name.get(row["name"])
            if old is None or not old.get("retainedMention"):
                newly_retained.append(row["name"])
            else:
                fields = [field for field in EVIDENCE_FIELDS if row.get(field) != old.get(field)]
                if fields:
                    changed.append({"name": row["name"], "fields": fields})

    no_longer_retained = []
    newly_without_signal = []
    if previous_by_name is not None:
        no_longer_retained = sorted(
            name for name, row in previous_by_name.items()
            if row.get("retainedMention") and not current_by_name.get(name, {}).get("retainedMention")
        )
        old_no_signal = {
            row["name"] for row in previous
            if row.get("retainedMention") and not (
                row["terminal"] or row["compiledConsumerCount"] <= 1 or row.get("directWrapperOf")
            )
        }
        newly_without_signal = sorted(set(no_signal) - old_no_signal)

    return {
        "retainedCount": len(retained),
        "structuralReauditCount": len(retained) - len(no_signal),
        "withoutStructuralSignal": no_signal,
        "zeroCompiledConsumers": zero_consumer,
        "zeroConsumerDirectWrappers": zero_consumer_wrappers,
        "retainedReplacementCandidates": replacement_candidates,
        "baselineAvailable": previous_by_name is not None,
        "changedReviewEvidence": changed,
        "newlyRetained": newly_retained,
        "noLongerRetained": no_longer_retained,
        "newlyWithoutStructuralSignal": newly_without_signal,
    }


def markdown(report, max_items=20):
    """Short GitHub Actions job summary; JSON includes complete queues."""
    lines = [
        "## Retained theorem re-audit (advisory)",
        "",
        "Structural signals are **review prompts**, not evidence that a theorem is unused or deletable.",
        "Compiled consumers can omit source-level uses erased by elaboration or simplification.",
        "",
        f"- Retained theorems: **{report['retainedCount']}**",
        f"- Still carrying a structural review signal: **{report['structuralReauditCount']}**",
        f"- No longer carrying a structural review signal: **{len(report['withoutStructuralSignal'])}**",
        f"- Zero compiled consumers: **{len(report['zeroCompiledConsumers'])}**",
        f"- Zero-consumer direct wrappers: **{len(report['zeroConsumerDirectWrappers'])}**",
        f"- Retained theorems with candidate replacements: **{len(report['retainedReplacementCandidates'])}**",
        "",
    ]

    def append_names(title, names):
        lines.extend([f"### {title} ({len(names)})", ""])
        for name in names[:max_items]:
            lines.append(f"- `{name}`")
        if len(names) > max_items:
            lines.append(f"- ... and {len(names) - max_items} more (see retained-audit.json)")
        if not names:
            lines.append("- None")
        lines.append("")

    append_names("Retained entries without a current structural signal", report["withoutStructuralSignal"])
    append_names("Zero-consumer direct wrappers to assess semantically", report["zeroConsumerDirectWrappers"])
    replacements = report["retainedReplacementCandidates"]
    lines.extend([f"### Retained theorems with replacement candidates ({len(replacements)})", ""])
    for item in replacements[:max_items]:
        targets = sorted({name for values in item["candidates"].values() for name in values})
        lines.append(f"- `{item['name']}` → {', '.join(targets)}")
    if len(replacements) > max_items:
        lines.append(f"- ... and {len(replacements) - max_items} more (see retained-audit.json)")
    if not replacements:
        lines.append("- None")
    lines.append("")

    if report["baselineAvailable"]:
        lines.extend([
            "### Since the last published graph-data snapshot",
            "",
            "This comparison is **not** a last-reviewed baseline; it detects compiled evidence changes",
            "since the graph-data branch was last published.",
            "",
        ])
        changed = report["changedReviewEvidence"]
        lines.append(f"- Retained declarations with changed review evidence: **{len(changed)}**")
        lines.append(f"- Newly retained declarations: **{len(report['newlyRetained'])}**")
        lines.append(f"- No longer retained: **{len(report['noLongerRetained'])}**")
        lines.append(f"- Newly without a structural signal: **{len(report['newlyWithoutStructuralSignal'])}**")
        lines.append("")
        for item in changed[:max_items]:
            lines.append(f"- `{item['name']}`: {', '.join(item['fields'])}")
        if len(changed) > max_items:
            lines.append(f"- ... and {len(changed) - max_items} more (see retained-audit.json)")
        lines.append("")
    else:
        lines.extend([
            "### Snapshot comparison unavailable", "",
            "The current structural queues remain valid, but evidence changes cannot be inferred.", "",
        ])
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("catalog", type=Path)
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--markdown", type=Path, required=True)
    parser.add_argument("--json", type=Path, required=True)
    args = parser.parse_args()
    current = json.loads(args.catalog.read_text(encoding="utf-8"))
    previous = (json.loads(args.baseline.read_text(encoding="utf-8"))
                if args.baseline is not None and args.baseline.is_file() else None)
    report = audit(current, previous)
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.markdown.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    args.markdown.write_text(markdown(report) + "\n", encoding="utf-8")
    print(f"Retained audit: {report['retainedCount']} retained; "
          f"{len(report['withoutStructuralSignal'])} no-signal entries; "
          f"{len(report['changedReviewEvidence'])} evidence changes "
          f"(baseline available: {report['baselineAvailable']})")


if __name__ == "__main__":
    main()
