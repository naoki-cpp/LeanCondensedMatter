"""Generate the legacy audit and a declaration graph over every project source module.

Run in CI with Lean/Lake installed. The public umbrella remains the audit boundary;
the Explorer imports all source modules in a temporary copy of the collector.
"""

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


if __name__ == "__main__":
    generate()
