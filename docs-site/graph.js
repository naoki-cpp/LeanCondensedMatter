const SVG_NS = "http://www.w3.org/2000/svg";
const MAX_NODES = 80;
const SEARCH_LIMIT = 10;
const CATALOG_URL = "https://raw.githubusercontent.com/naoki-cpp/LeanCondensedMatter/graph-data/theorems.json";
const BRANCH_COLORS = [
  "#ff5f6d", "#ff9f43", "#2ed573", "#3b82f6", "#8b5cf6", "#ec4899",
  "#06b6d4", "#84cc16", "#f97316", "#a855f7", "#14b8a6", "#eab308",
];
const MIN_BRANCH_ARC = 52;
const MIN_LEAF_ARC = 22;

const state = {
  catalog: [],
  byName: new Map(),
  root: null,
  selected: null,
  direction: "both",
  depth: 2,
  module: "*",
  highlights: new Set(),
  searchResults: [],
  searchIndex: -1,
  graphBounds: null,
  viewBox: null,
  drag: null,
};

const ui = {
  overviewLink: document.querySelector("#overview-link"),
  searchForm: document.querySelector("#search-form"),
  search: document.querySelector("#theorem-search"),
  searchResults: document.querySelector("#search-results"),
  direction: document.querySelector("#direction"),
  depth: document.querySelector("#depth"),
  module: document.querySelector("#module-filter"),
  graph: document.querySelector("#graph"),
  viewport: document.querySelector("#graph-viewport"),
  overview: document.querySelector("#overview"),
  graphStatus: document.querySelector("#graph-status"),
  detail: document.querySelector("#detail"),
  zoomOut: document.querySelector("#zoom-out"),
  zoomIn: document.querySelector("#zoom-in"),
  fitView: document.querySelector("#fit-view"),
  highlightInputs: [...document.querySelectorAll("[data-highlight]")],
};

function svg(tag, attributes = {}) {
  const node = document.createElementNS(SVG_NS, tag);
  for (const [key, value] of Object.entries(attributes)) node.setAttribute(key, String(value));
  return node;
}

function element(tag, className = "", text = "") {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text) node.textContent = text;
  return node;
}

function normalizeEntry(entry) {
  return {
    ...entry,
    dependencies: Array.isArray(entry.dependencies) ? entry.dependencies : [],
    dependents: Array.isArray(entry.dependents) ? entry.dependents : [],
    compiledConsumers: Array.isArray(entry.compiledConsumers) ? entry.compiledConsumers : [],
    sourceUrl: typeof entry.sourceUrl === "string" ? entry.sourceUrl : null,
    sourceFile: typeof entry.sourceFile === "string" ? entry.sourceFile : null,
    sourceLine: Number.isInteger(entry.sourceLine) ? entry.sourceLine : null,
  };
}

function shortModule(moduleName) {
  const prefix = "LeanCondensedMatter.";
  return moduleName.startsWith(prefix) ? moduleName.slice(prefix.length) : moduleName;
}

function domainName(moduleName) {
  return shortModule(moduleName).split(".")[0] || shortModule(moduleName);
}

function declarationBaseName(name) {
  return name.split(".").at(-1) ?? name;
}

function displayName(name) {
  const parts = name.split(".");
  if (!state.root) return parts.length <= 3 ? name : `…${parts.slice(-3).join(".")}`;
  const rootParts = state.root.split(".");
  let common = 0;
  while (common < parts.length && common < rootParts.length && parts[common] === rootParts[common]) common += 1;
  const contextual = parts.slice(common).join(".");
  if (contextual && contextual.length <= 34) return contextual;
  const base = declarationBaseName(name);
  return base.length <= 34 ? base : `${base.slice(0, 31)}…`;
}

function moduleAllowed(name) {
  if (state.module === "*") return true;
  return state.byName.get(name)?.module === state.module;
}

function addTraversal(levels, accessor, sign) {
  const visited = new Set([state.root]);
  const queue = [[state.root, 0]];
  let truncated = false;

  while (queue.length > 0) {
    const [name, depth] = queue.shift();
    if (depth >= state.depth) continue;
    const entry = state.byName.get(name);
    if (!entry) continue;

    const neighbors = accessor(entry)
      .filter((neighbor) => state.byName.has(neighbor))
      .filter((neighbor) => neighbor === state.root || moduleAllowed(neighbor))
      .sort((a, b) => a.localeCompare(b));

    for (const neighbor of neighbors) {
      if (visited.has(neighbor)) continue;
      if (!levels.has(neighbor) && levels.size >= MAX_NODES) {
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
  const levels = new Map([[state.root, 0]]);
  let truncated = false;
  if (state.direction === "dependencies" || state.direction === "both") {
    truncated = addTraversal(levels, (entry) => entry.dependencies, -1) || truncated;
  }
  if (state.direction === "consumers" || state.direction === "both") {
    truncated = addTraversal(levels, (entry) => entry.dependents, 1) || truncated;
  }
  return { levels, truncated };
}

function highlightMatches(entry) {
  if (state.highlights.size === 0) return null;
  return (
    (state.highlights.has("terminal") && entry.terminal) ||
    (state.highlights.has("zero") && entry.compiledConsumerCount === 0) ||
    (state.highlights.has("single") && entry.singleCompiledConsumer) ||
    (state.highlights.has("wrapper") && entry.directWrapperOf !== null)
  );
}

function chooseTreeParents(levels) {
  const parents = new Map();
  const ordered = [...levels.entries()]
    .filter(([name]) => name !== state.root)
    .sort(([, a], [, b]) => Math.abs(a) - Math.abs(b));

  for (const [name, level] of ordered) {
    const parentLevel = level < 0 ? level + 1 : level - 1;
    const entry = state.byName.get(name);
    const candidates = [...levels.entries()]
      .filter(([, candidateLevel]) => candidateLevel === parentLevel)
      .map(([candidate]) => candidate)
      .filter((candidate) => {
        const candidateEntry = state.byName.get(candidate);
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
    if (name === state.root) continue;
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
  const branchFor = new Map([[state.root, "root"]]);
  const branchColor = new Map([["root", "#71e7dc"]]);
  const weightMemo = new Map();

  const dependencyRoots = sideChildren(state.root, children, levels, -1);
  const consumerRoots = sideChildren(state.root, children, levels, 1);
  const allRoots = [...dependencyRoots, ...consumerRoots];
  allRoots.forEach((name, index) => branchColor.set(name, BRANCH_COLORS[index % BRANCH_COLORS.length]));

  const angularSpan = state.direction === "both" ? Math.PI - 0.16 : 2 * Math.PI - 0.16;
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
  const positions = new Map([[state.root, { x: cx, y: cy, angle: 0, radius: 0, level: 0 }]]);

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

  return { positions, parents, children, branchFor, branchColor, width, height, cx, cy, radiusStep };
}

function isTreeEdge(source, target, levels, parents) {
  const sourceLevel = levels.get(source);
  const targetLevel = levels.get(target);
  if (targetLevel < 0) return parents.get(target) === source;
  if (sourceLevel > 0) return parents.get(source) === target;
  return false;
}

function edgeBranch(source, target, levels, branchFor) {
  const targetLevel = levels.get(target);
  return targetLevel < 0 ? branchFor.get(target) : branchFor.get(source);
}

function curvedEdgePath(source, target, cx, cy) {
  const middleRadius = (source.radius + target.radius) / 2;
  const c1 = polarPoint(cx, cy, middleRadius, source.angle);
  const c2 = polarPoint(cx, cy, middleRadius, target.angle);
  return `M ${source.x} ${source.y} C ${c1.x} ${c1.y}, ${c2.x} ${c2.y}, ${target.x} ${target.y}`;
}

function setBranchFocus(branch) {
  for (const item of ui.graph.querySelectorAll("[data-branch]")) {
    const ownBranch = item.getAttribute("data-branch");
    const baseOpacity = Number(item.getAttribute("data-base-opacity") ?? "1");
    item.style.opacity = !branch || ownBranch === branch || ownBranch === "root"
      ? String(baseOpacity)
      : "0.1";
  }
}

function setGraphViewBox(viewBox) {
  state.viewBox = viewBox;
  ui.graph.setAttribute("viewBox", `${viewBox.x} ${viewBox.y} ${viewBox.width} ${viewBox.height}`);
}

function fitGraph() {
  if (!state.graphBounds) return;
  setGraphViewBox({ ...state.graphBounds });
}

function zoomGraph(factor, clientX = null, clientY = null) {
  if (!state.viewBox || !state.graphBounds) return;
  const rect = ui.viewport.getBoundingClientRect();
  const px = clientX === null ? 0.5 : Math.min(1, Math.max(0, (clientX - rect.left) / rect.width));
  const py = clientY === null ? 0.5 : Math.min(1, Math.max(0, (clientY - rect.top) / rect.height));
  const anchorX = state.viewBox.x + state.viewBox.width * px;
  const anchorY = state.viewBox.y + state.viewBox.height * py;
  const minWidth = Math.min(220, state.graphBounds.width);
  const maxWidth = state.graphBounds.width * 3;
  const width = Math.min(maxWidth, Math.max(minWidth, state.viewBox.width * factor));
  const aspect = state.viewBox.height / state.viewBox.width;
  const height = width * aspect;
  setGraphViewBox({
    x: anchorX - width * px,
    y: anchorY - height * py,
    width,
    height,
  });
}

function appendNodeLabel(nodes, name, position, color, branch, root, selected, showLeafLabel, baseOpacity) {
  const depth = Math.abs(position.level);
  if (!root && !selected && depth !== 1 && !showLeafLabel) return;
  const offset = root ? 28 : depth === 1 ? 25 : 17;
  const labelPoint = root
    ? { x: position.x, y: position.y + offset }
    : polarPoint(position.x, position.y, offset, position.angle);
  const cosine = Math.cos(position.angle);
  const anchor = root || Math.abs(cosine) < 0.2 ? "middle" : cosine > 0 ? "start" : "end";
  const text = svg("text", {
    class: "node-label",
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
  text.style.opacity = String(baseOpacity);
  text.textContent = displayName(name);
  nodes.append(text);
}

function renderGraph({ preserveView = false } = {}) {
  if (!state.root || !state.byName.has(state.root)) return;
  ui.overview.hidden = true;
  ui.viewport.hidden = false;
  setGraphActionsEnabled(true);

  const previousView = preserveView ? state.viewBox : null;
  const { levels, truncated } = collectNeighborhood();
  const { positions, parents, children, branchFor, branchColor, width, height, cx, cy } = radialLayout(levels);
  ui.graph.replaceChildren();
  state.graphBounds = { x: 0, y: 0, width, height };

  const guides = svg("g", { "aria-hidden": "true" });
  const maxDepth = Math.max(1, ...[...levels.values()].map((level) => Math.abs(level)));
  for (let depth = 1; depth <= maxDepth; depth += 1) {
    const sample = [...positions.values()].find((position) => Math.abs(position.level) === depth);
    if (!sample) continue;
    guides.append(svg("circle", {
      cx, cy, r: sample.radius,
      fill: "none",
      stroke: "rgba(169,190,255,0.08)",
      "stroke-width": 1,
      "stroke-dasharray": "2 8",
    }));
  }
  ui.graph.append(guides);

  const edges = svg("g", { class: "edges" });
  let edgeCount = 0;
  for (const sourceName of levels.keys()) {
    const source = state.byName.get(sourceName);
    const sourcePosition = positions.get(sourceName);
    if (!sourcePosition) continue;
    for (const dependencyName of source.dependencies) {
      if (!levels.has(dependencyName)) continue;
      const targetPosition = positions.get(dependencyName);
      if (!targetPosition) continue;
      const treeEdge = isTreeEdge(sourceName, dependencyName, levels, parents);
      const isWrapper = source.directWrapperOf === dependencyName;
      const branch = edgeBranch(sourceName, dependencyName, levels, branchFor) ?? "cross";
      const color = treeEdge ? branchColor.get(branch) ?? "#91a9ff" : "#94a3b8";
      const opacity = treeEdge ? 0.72 : 0.18;
      const path = svg("path", {
        d: curvedEdgePath(sourcePosition, targetPosition, cx, cy),
        fill: "none",
        stroke: color,
        "stroke-width": isWrapper ? 2.4 : treeEdge ? 1.45 : 1,
        "stroke-opacity": opacity,
        "stroke-dasharray": isWrapper ? "7 5" : treeEdge ? "none" : "4 7",
        "stroke-linecap": "round",
        "data-branch": treeEdge ? branch : "cross",
        "data-base-opacity": 1,
      });
      const title = svg("title");
      title.textContent = isWrapper
        ? `${sourceName} directly wraps ${dependencyName}`
        : `${sourceName} depends on ${dependencyName}`;
      path.append(title);
      edges.append(path);
      edgeCount += 1;
    }
  }
  ui.graph.append(edges);

  const nodes = svg("g", { class: "nodes" });
  const showLeafLabels = levels.size <= 32;
  for (const [name, position] of positions) {
    const entry = state.byName.get(name);
    if (!entry) continue;
    const isRoot = name === state.root;
    const isSelected = name === state.selected;
    const depth = Math.abs(position.level);
    const sign = Math.sign(position.level);
    const branch = branchFor.get(name) ?? "root";
    const color = branchColor.get(branch) ?? "#91a9ff";
    const highlight = highlightMatches(entry);
    const baseOpacity = highlight === false ? 0.25 : 1;
    const isLeaf = depth > 1 && sideChildren(name, children, levels, sign).length === 0;
    const radius = isRoot ? 12 : depth === 1 ? 6.5 : isSelected ? 6 : 4.2;

    const group = svg("g", {
      class: `node${isRoot ? " node-root" : ""}${isSelected ? " node-selected" : ""}`,
      transform: `translate(${position.x}, ${position.y})`,
      tabindex: 0,
      role: "button",
      "aria-label": name,
      "data-branch": branch,
      "data-base-opacity": baseOpacity,
    });
    group.style.opacity = String(baseOpacity);

    const hit = svg("circle", { class: "node-hit", r: Math.max(13, radius + 7), fill: "transparent" });
    const dot = svg("circle", {
      class: "node-dot",
      r: radius,
      fill: isRoot ? "#71e7dc" : color,
      stroke: isSelected ? "#ffffff" : isRoot ? "#d9fffb" : "rgba(255,255,255,0.72)",
      "stroke-width": isSelected || isRoot ? 2.4 : 1,
    });
    group.append(hit, dot);

    const title = svg("title");
    title.textContent = `${name}\n${entry.module}`;
    group.append(title);

    const select = () => {
      state.selected = name;
      renderDetails(name);
      renderGraph({ preserveView: true });
    };
    const emphasize = () => {
      dot.setAttribute("r", String(radius + 2));
      setBranchFocus(isRoot ? null : branch);
    };
    const relax = () => {
      dot.setAttribute("r", String(radius));
      setBranchFocus(null);
    };

    group.addEventListener("click", select);
    group.addEventListener("dblclick", () => focusRoot(name));
    group.addEventListener("keydown", (event) => {
      if (event.key === "Enter" || event.key === " ") {
        event.preventDefault();
        select();
      }
    });
    group.addEventListener("pointerenter", emphasize);
    group.addEventListener("pointerleave", () => {
      if (document.activeElement !== group) relax();
    });
    group.addEventListener("focus", emphasize);
    group.addEventListener("blur", relax);
    nodes.append(group);
    appendNodeLabel(
      nodes,
      name,
      position,
      color,
      branch,
      isRoot,
      isSelected,
      showLeafLabels && isLeaf,
      baseOpacity,
    );
  }
  ui.graph.append(nodes);

  if (previousView) setGraphViewBox(previousView);
  else fitGraph();
  ui.graphStatus.textContent = `${levels.size} nodes · ${edgeCount} edges · radial tree${truncated ? ` · capped at ${MAX_NODES} nodes` : ""}`;
}

function badge(text, kind = "") {
  const span = document.createElement("span");
  span.className = `badge ${kind}`.trim();
  span.textContent = text;
  return span;
}

function relationSection(title, names) {
  const section = document.createElement("section");
  section.className = "relation-section";
  section.append(element("h3", "", `${title} (${names.length})`));
  if (names.length === 0) {
    section.append(element("p", "muted", "None"));
    return section;
  }
  const list = element("div", "relation-list");
  for (const name of names.slice(0, 40)) {
    const button = element("button", "", name);
    button.type = "button";
    if (state.byName.has(name)) button.addEventListener("click", () => focusRoot(name));
    else {
      button.disabled = true;
      button.title = "This consumer is not a theorem node in the current catalog";
    }
    list.append(button);
  }
  if (names.length > 40) list.append(element("p", "muted", `+ ${names.length - 40} more`));
  section.append(list);
  return section;
}

function sourceHref(entry) {
  if (entry.sourceUrl) return entry.sourceUrl;
  if (!entry.sourceFile) return null;
  const path = entry.sourceFile.split("/").map(encodeURIComponent).join("/");
  const line = entry.sourceLine ? `#L${entry.sourceLine}` : "";
  return `https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/${path}${line}`;
}

function renderDetails(name) {
  const entry = state.byName.get(name);
  ui.detail.replaceChildren();
  if (!entry) return;
  ui.detail.append(element("p", "detail-eyebrow", shortModule(entry.module)));
  ui.detail.append(element("h2", "", entry.name));

  const badges = element("div", "badges");
  if (entry.terminal) badges.append(badge("terminal", "terminal"));
  if (entry.compiledConsumerCount === 0) badges.append(badge("zero consumer", "zero"));
  if (entry.singleCompiledConsumer) badges.append(badge("single consumer", "single"));
  if (entry.directWrapperOf !== null) badges.append(badge("direct wrapper", "wrapper"));
  if (entry.retainedMention) badges.append(badge("retained"));
  if (entry.completedMention) badges.append(badge("completed"));
  ui.detail.append(badges);

  const actions = element("div", "detail-actions");
  if (name !== state.root) {
    const focus = element("button", "focus-button", "Focus graph here");
    focus.type = "button";
    focus.addEventListener("click", () => focusRoot(name));
    actions.append(focus);
  }
  const href = sourceHref(entry);
  if (href) {
    const source = element("a", "source-link", "View source");
    source.href = href;
    source.target = "_blank";
    source.rel = "noreferrer";
    actions.append(source);
  }
  if (actions.childElementCount > 0) ui.detail.append(actions);

  ui.detail.append(element("h3", "", "Statement"));
  const statement = document.createElement("pre");
  statement.textContent = entry.statement;
  ui.detail.append(statement);

  if (entry.docString) {
    ui.detail.append(element("h3", "", "Documentation"));
    ui.detail.append(element("p", "docstring", entry.docString));
  }
  if (entry.directWrapperOf !== null) {
    const wrapper = element("p", "wrapper-target");
    wrapper.append("Direct wrapper of ");
    wrapper.append(element("code", "", entry.directWrapperOf));
    ui.detail.append(wrapper);
  }
  ui.detail.append(relationSection("Dependencies", entry.dependencies));
  ui.detail.append(relationSection("Theorem dependents", entry.dependents));
  ui.detail.append(relationSection("Compiled consumers", entry.compiledConsumers));
}

function setGraphActionsEnabled(enabled) {
  ui.zoomOut.disabled = !enabled;
  ui.zoomIn.disabled = !enabled;
  ui.fitView.disabled = !enabled;
}

function writeLocation(push) {
  const url = new URL(window.location.href);
  if (state.direction === "both") url.searchParams.delete("direction");
  else url.searchParams.set("direction", state.direction);
  if (state.depth === 2) url.searchParams.delete("depth");
  else url.searchParams.set("depth", String(state.depth));
  if (state.module === "*") url.searchParams.delete("module");
  else url.searchParams.set("module", state.module);
  url.hash = state.root ?? "";
  const next = `${url.pathname}${url.search}${url.hash}`;
  if (push) history.pushState(null, "", next);
  else history.replaceState(null, "", next);
}

function focusRoot(name, { historyEntry = true } = {}) {
  if (!state.byName.has(name)) return;
  state.root = name;
  state.selected = name;
  ui.search.value = name;
  hideSearchResults();
  renderDetails(name);
  renderGraph();
  if (historyEntry) writeLocation(true);
}

function overviewHeader(title, description) {
  const header = element("div", "overview-header");
  header.append(element("h2", "", title));
  header.append(element("p", "", description));
  return header;
}

function summaryChip(text) {
  return element("span", "summary-chip", text);
}

function renderDomainOverview() {
  ui.overview.replaceChildren();
  ui.overview.append(overviewHeader(
    "Explore LeanCondensedMatter",
    "Browse a project area, choose a module, or search directly for a declaration. The graph opens as a radial dependency tree after you choose a declaration.",
  ));
  const modules = new Set(state.catalog.map((entry) => entry.module));
  const summary = element("div", "overview-summary");
  summary.append(summaryChip(`${state.catalog.length} theorems`));
  summary.append(summaryChip(`${modules.size} modules`));
  summary.append(summaryChip(`${state.catalog.filter((entry) => entry.terminal).length} terminal`));
  summary.append(summaryChip(`${state.catalog.filter((entry) => entry.directWrapperOf !== null).length} wrappers`));
  ui.overview.append(summary);

  const groups = new Map();
  for (const entry of state.catalog) {
    const domain = domainName(entry.module);
    if (!groups.has(domain)) groups.set(domain, []);
    groups.get(domain).push(entry);
  }
  const section = element("section", "overview-section");
  section.append(element("h3", "", "Project areas"));
  const grid = element("div", "domain-grid");
  for (const [domain, entries] of [...groups.entries()].sort(([a], [b]) => a.localeCompare(b))) {
    const moduleCount = new Set(entries.map((entry) => entry.module)).size;
    const button = element("button", "domain-card");
    button.type = "button";
    button.append(element("strong", "", domain));
    button.append(element("small", "", `${entries.length} theorems · ${moduleCount} modules`));
    button.addEventListener("click", () => renderDomain(domain));
    grid.append(button);
  }
  section.append(grid);
  ui.overview.append(section);
}

function renderDomain(domain) {
  const entries = state.catalog.filter((entry) => domainName(entry.module) === domain);
  const modules = new Map();
  for (const entry of entries) {
    if (!modules.has(entry.module)) modules.set(entry.module, []);
    modules.get(entry.module).push(entry);
  }
  ui.overview.replaceChildren();
  ui.overview.append(overviewHeader(domain, `${entries.length} theorems across ${modules.size} modules.`));
  const section = element("section", "overview-section");
  const head = element("div", "overview-section-head");
  head.append(element("h3", "", "Modules"));
  const back = element("button", "overview-back", "All areas");
  back.type = "button";
  back.addEventListener("click", renderDomainOverview);
  head.append(back);
  section.append(head);
  const grid = element("div", "module-grid");
  for (const [moduleName, moduleEntries] of [...modules.entries()].sort(([a], [b]) => a.localeCompare(b))) {
    const button = element("button", "module-card");
    button.type = "button";
    button.append(element("strong", "", shortModule(moduleName)));
    button.append(element("small", "", `${moduleEntries.length} theorems`));
    button.addEventListener("click", () => renderModule(moduleName));
    grid.append(button);
  }
  section.append(grid);
  ui.overview.append(section);
}

function renderModule(moduleName) {
  const entries = state.catalog
    .filter((entry) => entry.module === moduleName)
    .sort((a, b) => a.name.localeCompare(b.name));
  ui.overview.replaceChildren();
  ui.overview.append(overviewHeader(shortModule(moduleName), `${entries.length} theorems in this module.`));
  const section = element("section", "overview-section");
  const head = element("div", "overview-section-head");
  head.append(element("h3", "", "Declarations"));
  const back = element("button", "overview-back", domainName(moduleName));
  back.type = "button";
  back.addEventListener("click", () => renderDomain(domainName(moduleName)));
  head.append(back);
  section.append(head);
  const list = element("div", "declaration-list");
  for (const entry of entries) {
    const button = element("button", "declaration-card");
    button.type = "button";
    button.append(element("strong", "", declarationBaseName(entry.name)));
    const context = entry.docString?.trim() || entry.statement;
    button.append(element("small", "", context.slice(0, 150)));
    button.addEventListener("click", () => focusRoot(entry.name));
    list.append(button);
  }
  section.append(list);
  ui.overview.append(section);
}

function showOverview({ historyEntry = true, resetModule = true } = {}) {
  state.root = null;
  state.selected = null;
  state.viewBox = null;
  state.graphBounds = null;
  if (resetModule) {
    state.module = "*";
    ui.module.value = "*";
  }
  ui.search.value = "";
  hideSearchResults();
  ui.viewport.hidden = true;
  ui.overview.hidden = false;
  setGraphActionsEnabled(false);
  const moduleCount = new Set(state.catalog.map((entry) => entry.module)).size;
  ui.graphStatus.textContent = `${state.catalog.length} theorems · ${moduleCount} modules`;
  ui.detail.replaceChildren(element("p", "muted", "Choose a declaration from the overview or search to inspect its statement and relationships."));
  if (!resetModule && state.module !== "*" && state.catalog.some((entry) => entry.module === state.module)) renderModule(state.module);
  else renderDomainOverview();
  if (historyEntry) writeLocation(true);
}

function populateControls() {
  const modules = [...new Set(state.catalog.map((entry) => entry.module))].sort((a, b) => a.localeCompare(b));
  for (const moduleName of modules) {
    const option = document.createElement("option");
    option.value = moduleName;
    option.textContent = shortModule(moduleName);
    ui.module.append(option);
  }
}

function searchScore(entry, query) {
  const needle = query.trim().toLowerCase();
  if (!needle) return null;
  const name = entry.name.toLowerCase();
  const base = declarationBaseName(entry.name).toLowerCase();
  const moduleName = entry.module.toLowerCase();
  const docs = (entry.docString ?? "").toLowerCase();
  const tokens = needle.split(/\s+/).filter(Boolean);
  const haystack = `${name} ${moduleName} ${docs}`;
  if (!tokens.every((token) => haystack.includes(token))) return null;
  if (name === needle) return 0;
  if (base === needle) return 1;
  if (name.startsWith(needle)) return 2;
  if (base.startsWith(needle)) return 3;
  const nameIndex = name.indexOf(needle);
  if (nameIndex >= 0) return 10 + nameIndex / 1000;
  if (moduleName.includes(needle)) return 20;
  if (docs.includes(needle)) return 30;
  return 40;
}

function findSearchResults(query) {
  const ranked = [];
  for (const entry of state.catalog) {
    const score = searchScore(entry, query);
    if (score !== null) ranked.push({ entry, score });
  }
  ranked.sort((a, b) => a.score - b.score || a.entry.name.localeCompare(b.entry.name));
  return ranked.slice(0, SEARCH_LIMIT).map(({ entry }) => entry);
}

function updateSearchActive() {
  [...ui.searchResults.querySelectorAll(".search-result")].forEach((button, index) => {
    const active = index === state.searchIndex;
    button.classList.toggle("active", active);
    button.setAttribute("aria-selected", String(active));
  });
}

function renderSearchResults() {
  const query = ui.search.value.trim();
  state.searchResults = findSearchResults(query);
  state.searchIndex = state.searchResults.length > 0 ? 0 : -1;
  ui.searchResults.replaceChildren();
  if (!query || state.searchResults.length === 0) {
    hideSearchResults();
    return;
  }
  state.searchResults.forEach((entry, index) => {
    const button = element("button", "search-result");
    button.type = "button";
    button.setAttribute("role", "option");
    button.append(element("strong", "", entry.name));
    const context = entry.docString?.trim() || shortModule(entry.module);
    button.append(element("small", "", `${shortModule(entry.module)}${context && context !== shortModule(entry.module) ? ` · ${context}` : ""}`));
    button.addEventListener("click", () => focusRoot(entry.name));
    button.addEventListener("mousemove", () => {
      state.searchIndex = index;
      updateSearchActive();
    });
    ui.searchResults.append(button);
  });
  ui.searchResults.hidden = false;
  ui.search.setAttribute("aria-expanded", "true");
  updateSearchActive();
}

function hideSearchResults() {
  ui.searchResults.hidden = true;
  ui.search.setAttribute("aria-expanded", "false");
  state.searchResults = [];
  state.searchIndex = -1;
}

function openActiveSearchResult() {
  const entry = state.searchResults[state.searchIndex] ?? state.searchResults[0];
  if (entry) focusRoot(entry.name);
}

function restoreLocation() {
  const params = new URLSearchParams(location.search);
  const direction = params.get("direction");
  state.direction = ["both", "dependencies", "consumers"].includes(direction) ? direction : "both";
  const depth = Number(params.get("depth"));
  state.depth = [1, 2, 3, 4].includes(depth) ? depth : 2;
  const requestedModule = params.get("module");
  state.module = requestedModule && state.catalog.some((entry) => entry.module === requestedModule) ? requestedModule : "*";
  ui.direction.value = state.direction;
  ui.depth.value = String(state.depth);
  ui.module.value = state.module;

  let requested = "";
  try { requested = decodeURIComponent(location.hash.slice(1)); }
  catch { requested = location.hash.slice(1); }
  if (requested && state.byName.has(requested)) focusRoot(requested, { historyEntry: false });
  else showOverview({ historyEntry: false, resetModule: false });
}

function bindGraphNavigation() {
  ui.zoomIn.addEventListener("click", () => zoomGraph(0.8));
  ui.zoomOut.addEventListener("click", () => zoomGraph(1.25));
  ui.fitView.addEventListener("click", fitGraph);
  ui.viewport.addEventListener("wheel", (event) => {
    if (!state.root) return;
    event.preventDefault();
    zoomGraph(event.deltaY < 0 ? 0.88 : 1.14, event.clientX, event.clientY);
  }, { passive: false });

  ui.viewport.addEventListener("pointerdown", (event) => {
    if (!state.viewBox || event.target.closest?.(".node")) return;
    ui.viewport.setPointerCapture(event.pointerId);
    state.drag = { pointerId: event.pointerId, x: event.clientX, y: event.clientY, viewBox: { ...state.viewBox } };
    ui.viewport.classList.add("dragging");
  });
  ui.viewport.addEventListener("pointermove", (event) => {
    if (!state.drag || event.pointerId !== state.drag.pointerId) return;
    const rect = ui.viewport.getBoundingClientRect();
    const dx = (event.clientX - state.drag.x) * state.drag.viewBox.width / Math.max(1, rect.width);
    const dy = (event.clientY - state.drag.y) * state.drag.viewBox.height / Math.max(1, rect.height);
    setGraphViewBox({ ...state.drag.viewBox, x: state.drag.viewBox.x - dx, y: state.drag.viewBox.y - dy });
  });
  const endDrag = (event) => {
    if (!state.drag || event.pointerId !== state.drag.pointerId) return;
    state.drag = null;
    ui.viewport.classList.remove("dragging");
  };
  ui.viewport.addEventListener("pointerup", endDrag);
  ui.viewport.addEventListener("pointercancel", endDrag);
}

function bindEvents() {
  ui.overviewLink.addEventListener("click", () => showOverview());
  ui.search.addEventListener("input", renderSearchResults);
  ui.search.addEventListener("focus", () => { if (ui.search.value.trim()) renderSearchResults(); });
  ui.search.addEventListener("keydown", (event) => {
    if (ui.searchResults.hidden) return;
    if (event.key === "ArrowDown") {
      event.preventDefault();
      state.searchIndex = Math.min(state.searchResults.length - 1, state.searchIndex + 1);
      updateSearchActive();
    } else if (event.key === "ArrowUp") {
      event.preventDefault();
      state.searchIndex = Math.max(0, state.searchIndex - 1);
      updateSearchActive();
    } else if (event.key === "Enter") {
      event.preventDefault();
      openActiveSearchResult();
    } else if (event.key === "Escape") hideSearchResults();
  });
  ui.searchForm.addEventListener("submit", (event) => {
    event.preventDefault();
    if (state.searchResults.length === 0) renderSearchResults();
    openActiveSearchResult();
  });
  document.addEventListener("pointerdown", (event) => {
    if (!ui.searchForm.contains(event.target)) hideSearchResults();
  });

  ui.direction.addEventListener("change", () => {
    state.direction = ui.direction.value;
    if (state.root) renderGraph();
    writeLocation(false);
  });
  ui.depth.addEventListener("change", () => {
    state.depth = Number(ui.depth.value);
    if (state.root) renderGraph();
    writeLocation(false);
  });
  ui.module.addEventListener("change", () => {
    state.module = ui.module.value;
    if (state.root) renderGraph();
    else if (state.module === "*") renderDomainOverview();
    else renderModule(state.module);
    writeLocation(false);
  });
  for (const input of ui.highlightInputs) {
    input.addEventListener("change", () => {
      if (input.checked) state.highlights.add(input.dataset.highlight);
      else state.highlights.delete(input.dataset.highlight);
      if (state.root) renderGraph({ preserveView: true });
    });
  }
  window.addEventListener("popstate", restoreLocation);
  bindGraphNavigation();
}

async function main() {
  const response = await fetch(CATALOG_URL, { cache: "no-store" });
  if (!response.ok) throw new Error(`failed to load theorem catalog: ${response.status}`);
  state.catalog = (await response.json()).map(normalizeEntry).sort((a, b) => a.name.localeCompare(b.name));
  state.byName = new Map(state.catalog.map((entry) => [entry.name, entry]));
  if (state.catalog.length === 0) throw new Error("theorem catalog is empty");
  populateControls();
  bindEvents();
  restoreLocation();
}

main().catch((error) => {
  console.error(error);
  ui.graphStatus.textContent = "Failed to load declaration graph.";
  const message = element("p", "error-message", error instanceof Error ? error.message : String(error));
  ui.detail.replaceChildren(message);
});
