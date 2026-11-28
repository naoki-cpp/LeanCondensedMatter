"""Generate the legacy audit and a declaration graph over every project source module.

Run in CI with Lean/Lake installed. The public umbrella remains the audit boundary;
the Explorer imports all source modules in a temporary copy of the collector.
"""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import tempfile

from export_module_import_graph import export_modules


ROOT = Path(__file__).resolve().parents[1]


def collector_source(source, modules):
    imports = "\n".join(f"import {name}" for name in sorted(set(modules)))
    anchor = "import LeanCondensedMatter\n"
    assert source.count(anchor) == 1, "collector import boundary changed"
    return source.replace(anchor, imports + "\n", 1)


def generate():
    modules = [row["name"] for row in export_modules()["modules"]]
    source = collector_source((ROOT / "scripts/TheoremCatalog.lean").read_text(encoding="utf-8"), modules)
    environment = os.environ.copy()
    environment["LCM_CATALOG_MODE"] = "audit"
    subprocess.run(["lake", "env", "lean", "scripts/TheoremCatalog.lean"],
                   cwd=ROOT, env=environment, check=True)
    # Source modules outside the public umbrella may not yet have compiled artifacts.
    subprocess.run(["lake", "build", *["+" + name for name in modules]], cwd=ROOT, check=True)
    environment["LCM_CATALOG_MODE"] = "declarations"
    with tempfile.TemporaryDirectory(prefix="declaration-catalog-", dir=ROOT / "scripts") as directory:
        collector = Path(directory) / "AllDeclarations.lean"
        collector.write_text(source, encoding="utf-8")
        subprocess.run(["lake", "env", "lean", str(collector.relative_to(ROOT))],
                       cwd=ROOT, env=environment, check=True)


def compact_json(value):
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def export_explorer_data(declarations, destination):
    """Keep searchable metadata in the index and structured statements in module shards."""
    details = {}
    index = []
    for declaration in declarations:
        row = dict(declaration)
        statement = row.pop("structuredStatement", None)
        if statement is not None:
            details.setdefault(row["module"], {})[row["name"]] = statement
        index.append(row)

    directory = destination / "declaration-details"
    directory.mkdir(parents=True, exist_ok=True)
    modules = {}
    for module, statements in sorted(details.items()):
        payload = compact_json(statements)
        filename = sha256(payload).hexdigest() + ".json"
        (directory / filename).write_bytes(payload)
        modules[module] = "declaration-details/" + filename

    # Content-addressed shard names let clients detect a publication change
    # instead of accidentally combining incompatible declaration snapshots.
    (destination / "declaration-index.json").write_bytes(compact_json({
        "version": 1, "modules": modules, "declarations": index,
    }))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--export-explorer", type=Path, metavar="DESTINATION")
    args = parser.parse_args()
    try:
        if args.export_explorer is None:
            generate()
        else:
            declarations = json.loads((ROOT / "docs/generated/declarations.json").read_text(
                encoding="utf-8"))
            export_explorer_data(declarations, args.export_explorer)
    except subprocess.CalledProcessError as error:
        # The child already prints its diagnostics; avoid repeating every module argument.
        raise SystemExit(error.returncode) from None
