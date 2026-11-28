import { declarationCounts } from "./declaration-model.js";

export const PROJECT_NAME = "LeanCondensedMatter";
const prefix = PROJECT_NAME + ".";

export function modulePath(name) {
  if (name === PROJECT_NAME) return [];
  return (name.startsWith(prefix) ? name.slice(prefix.length) : name).split(".").filter(Boolean);
}

export function buildDeclarationHierarchy(entries, modules = []) {
  const root = makeNode(PROJECT_NAME, "");
  const byModule = new Map();
  const byName = new Map();

  function makeNode(name, path, parent = null) {
    return { name, path, fullName: path ? prefix + path : PROJECT_NAME, parent,
      children: new Map(), declarations: [], moduleCount: 1 };
  }

  function ensure(name) {
    let node = root;
    for (const part of modulePath(name)) {
      if (!node.children.has(part)) {
        const path = node.path ? node.path + "." + part : part;
        const child = makeNode(part, path, node);
        node.children.set(part, child);
        byModule.set(path, child);
      }
      node = node.children.get(part);
    }
    return node;
  }

  for (const name of modules) ensure(name);
  for (const entry of entries) {
    const owner = ensure(entry.module);
    owner.declarations.push(entry);
    byName.set(entry.name, owner);
  }

  function summarize(node) {
    node.declarations.sort((a, b) => a.name.localeCompare(b.name));
    node.entries = [...node.declarations];
    node.counts = declarationCounts(node.declarations);
    node.visibleCounts = declarationCounts(node.declarations, { includeGenerated: true });
    for (const child of node.children.values()) {
      summarize(child);
      node.moduleCount += child.moduleCount;
      for (const key of Object.keys(node.counts)) {
        node.counts[key] += child.counts[key];
        node.visibleCounts[key] += child.visibleCounts[key];
      }
      for (const entry of child.entries) node.entries.push(entry);
    }
    node.declarationCount = node.counts.total;
  }
  summarize(root);

  const bundleCache = new Map();
  function bundles(parent) {
    if (bundleCache.has(parent)) return bundleCache.get(parent);
    const children = [...parent.children.values()];
    const order = new Map(children.map((child, i) => [child, i]));
    function branch(owner) {
      while (owner && owner !== parent && owner.parent !== parent) owner = owner.parent;
      return order.get(owner);
    }
    const counts = new Map();
    for (const child of children) {
      const source = order.get(child);
      for (const entry of child.entries) {
        for (const name of new Set(entry.dependencies ?? [])) {
          const target = branch(byName.get(name));
          if (target === undefined || target === source) continue;
          const a = Math.min(source, target);
          const b = Math.max(source, target);
          const key = a + ":" + b;
          if (!counts.has(key)) counts.set(key, { a: children[a], b: children[b], ab: 0, ba: 0 });
          const count = counts.get(key);
          if (source === a) count.ab += 1;
          else count.ba += 1;
        }
      }
    }
    const result = [...counts.values()].sort((a, b) => b.ab + b.ba - a.ab - a.ba);
    bundleCache.set(parent, result);
    return result;
  }

  return {
    root,
    find(name) {
      const path = modulePath(name).join(".");
      return path ? byModule.get(path) ?? null : root;
    },
    bundles,
  };
}
