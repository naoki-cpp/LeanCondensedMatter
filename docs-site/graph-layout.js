/**
 * Build a radial scene without reading the DOM or mutating the catalog.
 * Catalog entries provide dependencies and dependents as name arrays; root must exist.
 * Missing neighbors are ignored. Rejected neighbors prune traversal, while root is retained.
 * Levels are negative for dependencies and positive for consumers. Both traversals share
 * the node cap; dependencies are visited first and truncation is reported to the caller.
 */
export function buildGraphScene(byName, { root, direction = "both", depth: depthLimit = 2, accepts = () => true, maxNodes = 80 }) {
  const MIN_BRANCH_ARC = 52;
  const MIN_LEAF_ARC = 22;
  function addTraversal(levels, accessor, sign) {
    const visited = new Set([root]);
    const queue = [[root, 0]];
    let truncated = false;

    while (queue.length > 0) {
      const [name, depth] = queue.shift();
      if (depth >= depthLimit) continue;
      const entry = byName.get(name);
      if (!entry) continue;

      const neighbors = accessor(entry)
        .filter((neighbor) => byName.has(neighbor))
        .filter((neighbor) => neighbor === root || accepts(neighbor))
        .sort((a, b) => a.localeCompare(b));

      for (const neighbor of neighbors) {
        if (visited.has(neighbor)) continue;
        if (!levels.has(neighbor) && levels.size >= maxNodes) {
          truncated = true;
          continue;
        }
        visited.add(neighbor);
        const nextDepth = depth + 1;
        const nextLevel = sign * nextDepth;
        const previous = levels.get(neighbor);
        if (previous === undefined || Math.abs(nextLevel) < Math.abs(previous)) {
          levels.set(neighbor, nextLevel);
        }
        queue.push([neighbor, nextDepth]);
      }
    }
    return truncated;
  }

  function collectNeighborhood() {
    const levels = new Map([[root, 0]]);
    let truncated = false;
    if (direction === "dependencies" || direction === "both") {
      truncated = addTraversal(levels, (entry) => entry.dependencies, -1) || truncated;
    }
    if (direction === "consumers" || direction === "both") {
      truncated = addTraversal(levels, (entry) => entry.dependents, 1) || truncated;
    }
    return { levels, truncated };
  }

  function chooseTreeParents(levels) {
    const parents = new Map();
    const ordered = [...levels.entries()]
      .filter(([name]) => name !== root)
      .sort(([, a], [, b]) => Math.abs(a) - Math.abs(b));

    for (const [name, level] of ordered) {
      const parentLevel = level < 0 ? level + 1 : level - 1;
      const entry = byName.get(name);
      const candidates = [...levels.entries()]
        .filter(([, candidateLevel]) => candidateLevel === parentLevel)
        .map(([candidate]) => candidate)
        .filter((candidate) => {
          const candidateEntry = byName.get(candidate);
          return level < 0
            ? candidateEntry?.dependencies.includes(name)
            : entry?.dependencies.includes(candidate);
        })
        .sort((a, b) => a.localeCompare(b));
      if (candidates.length > 0) parents.set(name, candidates[0]);
    }
    return parents;
  }

  function treeChildren(levels, parents) {
    const children = new Map();
    for (const [name] of levels) {
      if (name === root) continue;
      const parent = parents.get(name);
      if (!parent) continue;
      if (!children.has(parent)) children.set(parent, []);
      children.get(parent).push(name);
    }
    for (const names of children.values()) names.sort((a, b) => a.localeCompare(b));
    return children;
  }

  function sideChildren(name, children, levels, sign) {
    return (children.get(name) ?? []).filter((child) => Math.sign(levels.get(child)) === sign);
  }

  function subtreeWeight(name, children, levels, sign, memo) {
    const key = `${sign}:${name}`;
    if (memo.has(key)) return memo.get(key);
    const descendants = sideChildren(name, children, levels, sign);
    const weight = descendants.length === 0
      ? 1
      : descendants.reduce((sum, child) => sum + subtreeWeight(child, children, levels, sign, memo), 0);
    memo.set(key, weight);
    return weight;
  }

  function sideDepth(levels, sign) {
    return Math.max(
      1,
      ...[...levels.values()]
        .filter((level) => Math.sign(level) === sign)
        .map((level) => Math.abs(level)),
    );
  }

  function densityRadiusStep(roots, children, levels, sign, angularSpan, memo) {
    if (roots.length === 0) return 0;
    const leafCount = roots.reduce(
      (sum, root) => sum + subtreeWeight(root, children, levels, sign, memo),
      0,
    );
    const depth = sideDepth(levels, sign);
    const firstRingRadius = (roots.length * MIN_BRANCH_ARC) / angularSpan;
    const outerRingRadius = (leafCount * MIN_LEAF_ARC) / angularSpan;
    return Math.max(firstRingRadius, outerRingRadius / depth);
  }

  function polarPoint(cx, cy, radius, angle) {
    return { x: cx + Math.cos(angle) * radius, y: cy + Math.sin(angle) * radius };
  }

  function radialLayout(levels) {
    const parents = chooseTreeParents(levels);
    const children = treeChildren(levels, parents);
    const maxDepth = Math.max(1, ...[...levels.values()].map((level) => Math.abs(level)));
    const baseRadiusStep = maxDepth <= 2 ? 180 : maxDepth === 3 ? 155 : 140;
    const branchFor = new Map([[root, "root"]]);
    
    const weightMemo = new Map();

    const dependencyRoots = sideChildren(root, children, levels, -1);
    const consumerRoots = sideChildren(root, children, levels, 1);

    const angularSpan = direction === "both" ? Math.PI - 0.16 : 2 * Math.PI - 0.16;
    const densityStep = Math.max(
      densityRadiusStep(dependencyRoots, children, levels, -1, angularSpan, weightMemo),
      densityRadiusStep(consumerRoots, children, levels, 1, angularSpan, weightMemo),
    );
    const radiusStep = Math.max(baseRadiusStep, densityStep);
    const outerRadius = maxDepth * radiusStep;
    const margin = 190;
    const width = Math.max(900, outerRadius * 2 + margin * 2);
    const height = Math.max(700, outerRadius * 2 + margin * 2);
    const cx = width / 2;
    const cy = height / 2;
    const positions = new Map([[root, { x: cx, y: cy, angle: 0, radius: 0, level: 0 }]]);

    function placeBranch(name, startAngle, endAngle, sign, branch) {
      const level = levels.get(name);
      const angle = (startAngle + endAngle) / 2;
      const radius = Math.abs(level) * radiusStep;
      const point = polarPoint(cx, cy, radius, angle);
      positions.set(name, { ...point, angle, radius, level });
      branchFor.set(name, branch);

      const descendants = sideChildren(name, children, levels, sign);
      if (descendants.length === 0) return;
      const total = descendants.reduce(
        (sum, child) => sum + subtreeWeight(child, children, levels, sign, weightMemo),
        0,
      );
      let cursor = startAngle;
      for (const child of descendants) {
        const fraction = subtreeWeight(child, children, levels, sign, weightMemo) / total;
        const span = (endAngle - startAngle) * fraction;
        const pad = Math.min(0.035, Math.max(0, span * 0.06));
        placeBranch(child, cursor + pad, cursor + span - pad, sign, branch);
        cursor += span;
      }
    }

    function placeSide(roots, sign, startAngle, endAngle) {
      if (roots.length === 0) return;
      const total = roots.reduce(
        (sum, child) => sum + subtreeWeight(child, children, levels, sign, weightMemo),
        0,
      );
      let cursor = startAngle;
      for (const root of roots) {
        const fraction = subtreeWeight(root, children, levels, sign, weightMemo) / total;
        const span = (endAngle - startAngle) * fraction;
        const pad = Math.min(0.045, Math.max(0, span * 0.045));
        placeBranch(root, cursor + pad, cursor + span - pad, sign, root);
        cursor += span;
      }
    }

    if (direction === "both") {
      placeSide(consumerRoots, 1, -Math.PI / 2 + 0.08, Math.PI / 2 - 0.08);
      placeSide(dependencyRoots, -1, Math.PI / 2 + 0.08, 3 * Math.PI / 2 - 0.08);
    } else if (direction === "dependencies") {
      placeSide(dependencyRoots, -1, -Math.PI + 0.08, Math.PI - 0.08);
    } else {
      placeSide(consumerRoots, 1, -Math.PI + 0.08, Math.PI - 0.08);
    }

    return { positions, parents, children, branchFor, width, height, cx, cy, radiusStep };
  }


  const { levels, truncated } = collectNeighborhood();
  return { ...radialLayout(levels), levels, truncated };
}
