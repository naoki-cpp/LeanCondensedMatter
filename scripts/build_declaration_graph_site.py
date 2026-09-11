from __future__ import annotations

import json
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SITE_SOURCE = ROOT / "docs-site"
CATALOG = ROOT / "docs" / "generated" / "theorems.json"
OUTPUT = ROOT / "site"

REQUIRED_FIELDS = {
    "name",
    "module",
    "statement",
    "dependencies",
    "dependents",
    "compiledConsumers",
    "compiledConsumerCount",
    "singleCompiledConsumer",
    "terminal",
    "directWrapperOf",
}


def validate_catalog(catalog: object) -> list[dict[str, object]]:
    if not isinstance(catalog, list):
        raise SystemExit("theorem catalog must be a JSON array")

    validated: list[dict[str, object]] = []
    for index, entry in enumerate(catalog):
        if not isinstance(entry, dict):
            raise SystemExit(f"catalog entry {index} is not an object")
        missing = REQUIRED_FIELDS.difference(entry)
        if missing:
            fields = ", ".join(sorted(missing))
            raise SystemExit(f"catalog entry {index} is missing fields: {fields}")
        validated.append(entry)
    return validated


def main() -> int:
    if not CATALOG.is_file():
        raise SystemExit(
            "missing docs/generated/theorems.json; run `lake env lean scripts/TheoremCatalog.lean` first"
        )

    catalog = validate_catalog(json.loads(CATALOG.read_text(encoding="utf-8")))

    if OUTPUT.exists():
        shutil.rmtree(OUTPUT)
    (OUTPUT / "data").mkdir(parents=True)

    for filename in ("index.html", "site.css", "graph.js"):
        source = SITE_SOURCE / filename
        if not source.is_file():
            raise SystemExit(f"missing graph site source: {source.relative_to(ROOT)}")
        shutil.copy2(source, OUTPUT / filename)

    shutil.copy2(CATALOG, OUTPUT / "data" / "theorems.json")

    edge_count = sum(len(entry["dependencies"]) for entry in catalog)
    print(
        f"Built declaration graph site with {len(catalog)} theorem nodes "
        f"and {edge_count} dependency edges in {OUTPUT.relative_to(ROOT)}/"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
