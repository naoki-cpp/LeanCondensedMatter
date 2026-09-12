const RADIAL_NODE_ARC_SPACING = 38;
const RADIAL_DENSE_FIRST_RING = 14;
const RADIAL_DENSE_HIT_RADIUS = 8;

let radialDensity = {
  dense: false,
  showFirstRingLabels: true,
};

const baseSvg = svg;
svg = function densityAwareSvg(tag, attributes = {}) {
  if (tag !== "circle" || !radialDensity.dense || attributes.fill !== "transparent") {
    return baseSvg(tag, attributes);
  }
  return baseSvg(tag, { ...attributes, r: Math.min(Number(attributes.r) || RADIAL_DENSE_HIT_RADIUS, RADIAL_DENSE_HIT_RADIUS) });
};

function densityAwareRadiusStep(levels, maxDepth) {
  const baseStep = maxDepth <= 2 ? 180 : maxDepth === 3 ? 155 : 140;
  const angleSpan = state.direction === "both" ? Math.PI - 0.16 : 2 * Math.PI - 0.16;
  const activeSigns = state.direction === "both"
    ? [-1, 1]
    : state.direction === "dependencies" ? [-1] : [1];
  let radiusStep = baseStep;

  for (const sign of activeSigns) {
    for (let depth = 1; depth <= maxDepth; depth += 1) {
      const count = [...levels.values()].filter(
        (level) => Math.sign(level) === sign && Math.abs(level) === depth,
      ).length;
      if (count === 0) continue;
      const required = count * RADIAL_NODE_ARC_SPACING / (angleSpan * depth);
      radiusStep = Math.max(radiusStep, required);
    }
  }

  return Math.ceil(radiusStep);
}

radialLayout = function radialLayoutWithDensity(levels) {
  const parents = chooseTreeParents(levels);
  const children = treeChildren(levels, parents);
  const maxDepth = Math.max(1, ...[...levels.values()].map((level) => Math.abs(level)));
  const radiusStep = densityAwareRadiusStep(levels, maxDepth);
  const outerRadius = maxDepth * radiusStep;
  const margin = 180;
  const width = Math.max(900, outerRadius * 2 + margin * 2);
  const height = Math.max(700, outerRadius * 2 + margin * 2);
  const cx = width / 2;
  const cy = height / 2;
  const positions = new Map([[state.root, { x: cx, y: cy, angle: 0, radius: 0, level: 0 }]]);
  const branchFor = new Map([[state.root, "root"]]);
  const branchColor = new Map([["root", "#71e7dc"]]);
  const weightMemo = new Map();

  const dependencyRoots = sideChildren(state.root, children, levels, -1);
  const consumerRoots = sideChildren(state.root, children, levels, 1);
  const allRoots = [...dependencyRoots, ...consumerRoots];
  allRoots.forEach((name, index) => branchColor.set(name, BRANCH_COLORS[index % BRANCH_COLORS.length]));

  const largestFirstRing = Math.max(dependencyRoots.length, consumerRoots.length);
  radialDensity = {
    dense: largestFirstRing > RADIAL_DENSE_FIRST_RING || levels.size > 48,
    showFirstRingLabels: largestFirstRing <= RADIAL_DENSE_FIRST_RING,
  };
  ui.graph.classList.toggle("graph-dense", radialDensity.dense);

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

  if (state.direction === "both") {
    placeSide(consumerRoots, 1, -Math.PI / 2 + 0.08, Math.PI / 2 - 0.08);
    placeSide(dependencyRoots, -1, Math.PI / 2 + 0.08, 3 * Math.PI / 2 - 0.08);
  } else if (state.direction === "dependencies") {
    placeSide(dependencyRoots, -1, -Math.PI + 0.08, Math.PI - 0.08);
  } else {
    placeSide(consumerRoots, 1, -Math.PI + 0.08, Math.PI - 0.08);
  }

  return { positions, parents, branchFor, branchColor, width, height, cx, cy, radiusStep };
};

appendNodeLabel = function appendRadialNodeLabel(nodes, name, position, color, root, selected, showLeafLabel) {
  const depth = Math.abs(position.level);
  if (!root && !selected && depth === 1 && !radialDensity.showFirstRingLabels) return;
  if (!root && !selected && depth !== 1 && !showLeafLabel) return;

  const nodeGroup = nodes.lastElementChild?.classList?.contains("node") ? nodes.lastElementChild : null;
  const branch = nodeGroup?.getAttribute("data-branch") ?? "root";
  const baseOpacity = nodeGroup?.getAttribute("data-base-opacity") ?? "1";
  const offset = root ? 28 : depth === 1 ? 25 : 17;
  const labelPoint = root
    ? { x: position.x, y: position.y + offset }
    : polarPoint(position.x, position.y, offset, position.angle);
  const cosine = Math.cos(position.angle);
  const anchor = root || Math.abs(cosine) < 0.2 ? "middle" : cosine > 0 ? "start" : "end";
  const text = svg("text", {
    x: labelPoint.x,
    y: labelPoint.y,
    "text-anchor": anchor,
    "dominant-baseline": "middle",
    fill: root ? "#f5f7ff" : color,
    "font-size": root ? 12.5 : depth === 1 ? 11.5 : 9,
    "font-weight": root || depth === 1 ? 750 : 600,
    "paint-order": "stroke",
    stroke: "#080c18",
    "stroke-width": root ? 4 : 3,
    "stroke-linejoin": "round",
    "pointer-events": "none",
    "data-branch": branch,
    "data-base-opacity": baseOpacity,
  });
  text.style.opacity = baseOpacity;
  text.textContent = displayName(name);
  nodes.append(text);
};

ui.graph.addEventListener("focusin", (event) => {
  const node = event.target.closest?.(".node");
  if (!node) return;
  const branch = node.getAttribute("data-branch");
  setBranchFocus(branch === "root" ? null : branch);
});

ui.graph.addEventListener("focusout", (event) => {
  const nextNode = event.relatedTarget?.closest?.(".node");
  if (nextNode) return;
  setBranchFocus(null);
});

if (state.root) renderGraph();
