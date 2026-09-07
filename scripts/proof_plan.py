#!/usr/bin/env python3

import argparse
import json
from pathlib import Path
from typing import Any


def fail(message: str) -> None:
    raise SystemExit(message)


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        fail(f"missing file: {path}")
    except json.JSONDecodeError as exc:
        fail(f"{path}: invalid JSON: {exc}")


def plan_files(root: Path) -> list[Path]:
    if root.is_file():
        return [root]
    if not root.is_dir():
        fail(f"missing proof-plan path: {root}")
    files = sorted(root.rglob("*.json"))
    if not files:
        fail(f"no proof plans found under {root}")
    return files


def validate_plan(path: Path, raw: Any) -> dict[str, Any]:
    if not isinstance(raw, dict):
        fail(f"{path}: top level must be an object")
    if raw.get("version") != 1:
        fail(f"{path}: unsupported or missing version (expected 1)")
    name = raw.get("name")
    nodes = raw.get("nodes")
    if not isinstance(name, str) or not name:
        fail(f"{path}: name must be a non-empty string")
    if not isinstance(nodes, list) or not nodes:
        fail(f"{path}: nodes must be a non-empty array")

    by_id: dict[str, dict[str, Any]] = {}
    theorem_names: set[str] = set()
    normalized_nodes: list[dict[str, Any]] = []
    for index, node in enumerate(nodes):
        where = f"{path}: nodes[{index}]"
        if not isinstance(node, dict):
            fail(f"{where}: node must be an object")
        node_id = node.get("id")
        theorem = node.get("theorem")
        statement = node.get("statement")
        dependencies = node.get("dependsOn", [])
        meaning = node.get("meaning", "")
        if not isinstance(node_id, str) or not node_id:
            fail(f"{where}: id must be a non-empty string")
        if node_id in by_id:
            fail(f"{path}: duplicate node id: {node_id}")
        if not isinstance(theorem, str) or not theorem:
            fail(f"{where}: theorem must be a non-empty string")
        if theorem in theorem_names:
            fail(f"{path}: duplicate theorem name: {theorem}")
        if not isinstance(statement, str) or not statement.strip():
            fail(f"{where}: statement must be a non-empty Lean type")
        if not isinstance(dependencies, list) or any(
            not isinstance(dep, str) or not dep for dep in dependencies
        ):
            fail(f"{where}: dependsOn must be an array of non-empty node ids")
        if len(set(dependencies)) != len(dependencies):
            fail(f"{where}: dependsOn contains duplicates")
        if node_id in dependencies:
            fail(f"{where}: a node cannot depend on itself")
        if not isinstance(meaning, str):
            fail(f"{where}: meaning must be a string")

        normalized = {
            "id": node_id,
            "theorem": theorem,
            "statement": statement.strip(),
            "dependsOn": dependencies,
            "meaning": meaning.strip(),
        }
        normalized_nodes.append(normalized)
        by_id[node_id] = normalized
        theorem_names.add(theorem)

    for node in normalized_nodes:
        for dependency in node["dependsOn"]:
            if dependency not in by_id:
                fail(f"{path}: node {node['id']} depends on missing node {dependency}")

    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(node_id: str, stack: list[str]) -> None:
        if node_id in visiting:
            cycle_start = stack.index(node_id)
            cycle = stack[cycle_start:] + [node_id]
            fail(f"{path}: dependency cycle: {' -> '.join(cycle)}")
        if node_id in visited:
            return
        visiting.add(node_id)
        stack.append(node_id)
        for dependency in by_id[node_id]["dependsOn"]:
            visit(dependency, stack)
        stack.pop()
        visiting.remove(node_id)
        visited.add(node_id)

    for node_id in by_id:
        visit(node_id, [])

    return {"name": name, "path": str(path), "nodes": normalized_nodes}


def load_catalog(path: Path) -> dict[str, dict[str, Any]]:
    raw = load_json(path)
    if not isinstance(raw, list):
        fail(f"{path}: theorem catalog must be an array")
    catalog: dict[str, dict[str, Any]] = {}
    for index, entry in enumerate(raw):
        if not isinstance(entry, dict):
            fail(f"{path}: entry {index} must be an object")
        name = entry.get("name")
        if not isinstance(name, str) or not name:
            fail(f"{path}: entry {index} has no theorem name")
        catalog[name] = entry
    return catalog


def compute_state(plan: dict[str, Any], catalog: dict[str, dict[str, Any]]) -> dict[str, Any]:
    nodes = plan["nodes"]
    proved = {node["id"] for node in nodes if node["theorem"] in catalog}

    state_nodes: list[dict[str, Any]] = []
    frontier: list[str] = []
    for node in nodes:
        unresolved = [dep for dep in node["dependsOn"] if dep not in proved]
        if node["id"] in proved:
            status = "proved"
        elif unresolved:
            status = "blocked"
        else:
            status = "open"
            frontier.append(node["id"])
        state_nodes.append(
            {
                **node,
                "status": status,
                "blockedBy": unresolved,
                "compiledDependencies": (
                    catalog[node["theorem"]].get("dependencies", [])
                    if status == "proved"
                    else []
                ),
            }
        )

    inconsistent = [
        node["id"]
        for node in state_nodes
        if node["status"] == "proved" and node["blockedBy"]
    ]
    if inconsistent:
        fail(
            f"{plan['path']}: proved nodes have unproved planned dependencies: "
            + ", ".join(inconsistent)
        )

    return {
        "name": plan["name"],
        "path": plan["path"],
        "counts": {
            "nodes": len(nodes),
            "proved": sum(node["status"] == "proved" for node in state_nodes),
            "open": sum(node["status"] == "open" for node in state_nodes),
            "blocked": sum(node["status"] == "blocked" for node in state_nodes),
        },
        "frontier": frontier,
        "nodes": state_nodes,
    }


def lean_source(states: list[dict[str, Any]]) -> str:
    lines = [
        "import LeanCondensedMatter",
        "",
        "set_option linter.style.header false",
        "",
        "open Filter QuantumTheory.Transport",
        "",
        "namespace LeanCondensedMatter.ProofPlanCheck",
        "",
    ]
    for plan in states:
        lines.append(f"-- {plan['name']}")
        for node in plan["nodes"]:
            statement = node["statement"]
            if node["status"] == "proved":
                lines.extend(
                    [
                        f"example : {statement} := by",
                        f"  exact {node['theorem']}",
                    ]
                )
            else:
                lines.append(f"#check ({statement})")
            lines.append("")
    lines.append("end LeanCondensedMatter.ProofPlanCheck")
    lines.append("")
    return "\n".join(lines)


def markdown_summary(states: list[dict[str, Any]]) -> str:
    lines = ["## Planned proof DAG", ""]
    for plan in states:
        counts = plan["counts"]
        lines.extend(
            [
                f"### {plan['name']}",
                "",
                (
                    f"Nodes: {counts['nodes']} · Proved: {counts['proved']} · "
                    f"Open: {counts['open']} · Blocked: {counts['blocked']}"
                ),
                "",
            ]
        )
        if plan["frontier"]:
            lines.append("Frontier:")
            for node_id in plan["frontier"]:
                node = next(node for node in plan["nodes"] if node["id"] == node_id)
                lines.append(f"- `{node_id}` — `{node['theorem']}`")
        else:
            lines.append("Frontier: none")
        lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Resolve planned theorem DAGs against the compiled theorem catalog."
    )
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--plans", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--lean-check", type=Path, required=True)
    args = parser.parse_args()

    catalog = load_catalog(args.catalog)
    plans = [validate_plan(path, load_json(path)) for path in plan_files(args.plans)]
    states = [compute_state(plan, catalog) for plan in plans]

    args.output.write_text(
        json.dumps({"version": 1, "plans": states}, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    args.summary.write_text(markdown_summary(states), encoding="utf-8")
    args.lean_check.write_text(lean_source(states), encoding="utf-8")


if __name__ == "__main__":
    main()
