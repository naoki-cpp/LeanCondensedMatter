import { createModuleOverview } from "./module-overview.js";
import { declarationAllowed } from "./declaration-model.js";
import { buildModuleGraphCatalog } from "./module-import-map.js";
import {
  BRANCH_COLORS,
  ROOT_NODE_COLOR,
  ROOT_NODE_STROKE,
  graphNodeLabelAttributes,
  graphNodeRadius,
} from "./graph-style.js";

const SVG_NS = "http://www.w3.org/2000/svg";
const MAX_NODES = 80;
const SEARCH_LIMIT = 10;
const CATALOG_URL = "https://raw.githubusercontent.com/naoki-cpp/LeanCondensedMatter/graph-data/declarations.json";
const MODULES_URL = "https://raw.githubusercontent.com/naoki-cpp/LeanCondensedMatter/graph-data/module-imports.json";
const MIN_BRANCH_ARC = 52;
const MIN_LEAF_ARC = 22;

const state = {
  catalog: [],
  byName: new Map(),
  theoremCatalog: [],
  theoremByName: new Map(),
  moduleCatalog: [],
  moduleByName: new Map(),
  graphKind: "theorems",
  root: null,
  selected: null,
  browse: null,
  returnBrowse: null,
  page: "overview",
  direction: "both",
  depth: 2,
  module: "*",
  highlights: new Set(),
  kind: "*",
  generated: false,
  searchResults: [],
  searchIndex: -1,
  graphBounds: null,
  viewBox: null,
  drag: null,
};

const ui = {
  overviewLink: document.querySelector("#overview-link"),
  moduleImportsLink: document.querySelector("#module-imports-link"),
  searchForm: document.querySelector("#search-form"),
  searchLabel: document.querySelector("#search-form > label"),
  search: document.querySelector("#theorem-search"),
  searchResults: document.querySelector("#search-results"),
  direction: document.querySelector("#direction"),
  depth: document.querySelector("#depth"),
  module: document.querySelector("#module-filter"),
  moduleFilterLabel: document.querySelector("#module-filter").closest("label"),
  wrapperHighlightLabel: document.querySelector('[data-highlight="wrapper"]').closest("label"),
  graphLegend: document.querySelector(".legend"),
  graph: document.querySelector("#graph"),
  viewport: document.querySelector("#graph-viewport"),
  overview: document.querySelector("#overview"),
  graphToolbar: document.querySelector(".graph-toolbar"),
  graphStatus: document.querySelector("#graph-status"),
  detail: document.querySelector("#detail"),
  highlightInputs: [...document.querySelectorAll("[data-highlight]")],
};

let moduleOverview = null;

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
    directWrapperOf: entry.directWrapperOf ?? null,
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
  if (state.graphKind !== "modules" &&
      !declarationAllowed(state.byName.get(name), state.kind, state.generated)) return false;
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
  const highlights = state.graphKind === "modules"
    ? new Set([...state.highlights].filter((name) => name !== "wrapper"))
    : state.highlights;
  if (highlights.size === 0) return null;
  return (
    (highlights.has("terminal") && entry.terminal) ||
    (highlights.has("zero") && entry.compiledConsumerCount === 0) ||
    (highlights.has("single") && entry.singleCompiledConsumer) ||
    (highlights.has("wrapper") && entry.directWrapperOf != null)
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
  const branchColor = new Map([["root", ROOT_NODE_COLOR]]);
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
    ...graphNodeLabelAttributes({ depth, root, color }),
    "data-branch": branch,
    "data-base-opacity": baseOpacity,
  });
  text.style.opacity = String(baseOpacity);
  text.textContent = displayName(name);
  nodes.append(text);
}

function setModuleFilterEnabled(enabled) {
  ui.module.disabled = !enabled;
  ui.module.title = enabled
    ? "Filter the current dependency graph by exact module."
    : "Browse modules through the module hierarchy.";
}

function setGraphModeChrome() {
  const modules = state.graphKind === "modules";
  ui.overviewLink.textContent = "Declarations";
  document.getElementById("kind-filter").closest("label").hidden = modules;
  document.getElementById("generated-filter").closest("label").hidden = modules;
  ui.searchLabel.textContent = modules ? "Module" : "Declaration";
  ui.search.placeholder = modules ? "Module name" : "Name, module, or documentation";
  ui.moduleFilterLabel.hidden = modules;
  ui.wrapperHighlightLabel.hidden = modules;
  ui.graph.setAttribute("aria-label", modules
    ? "Interactive Lean module import graph"
    : "Interactive declaration dependency graph");
  const [terminal, zero, single] = ui.highlightInputs;
  terminal.nextSibling.nodeValue = modules ? " no project imports" : " terminal";
  zero.nextSibling.nodeValue = modules ? " no importers" : " zero consumer";
  single.nextSibling.nodeValue = modules ? " one importer" : " single consumer";
  ui.graphLegend.querySelector(".legend-node").parentElement.lastChild.nodeValue = modules ? " module" : " theorem";
  const edgeLegend = ui.graphLegend.querySelector(".legend-dependency");
  edgeLegend.childNodes[1].nodeValue = modules ? " import" : " dependency";
  ui.graphLegend.querySelector(".legend-edge.wrapper").parentElement.hidden = modules;
}

function renderGraph({ preserveView = false } = {}) {
  if (!state.root || !state.byName.has(state.root)) return;
  ui.overview.hidden = true;
  ui.viewport.hidden = false;
  ui.graphToolbar.hidden = false;
  setModuleFilterEnabled(state.graphKind === "theorems");

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
      const typeReference = source.typeDependencies?.includes(dependencyName);
      const valueReference = source.valueDependencies?.includes(dependencyName);
      const branch = edgeBranch(sourceName, dependencyName, levels, branchFor) ?? "cross";
      const color = treeEdge ? branchColor.get(branch) ?? "#91a9ff" : "#94a3b8";
      const opacity = treeEdge ? 0.72 : 0.18;
      const path = svg("path", {
        d: curvedEdgePath(sourcePosition, targetPosition, cx, cy),
        fill: "none",
        stroke: color,
        "stroke-width": isWrapper ? 2.4 : treeEdge ? 1.45 : 1,
        "stroke-opacity": opacity,
        "stroke-dasharray": isWrapper ? "7 5" : typeReference && !valueReference ? "2 5" : treeEdge ? "none" : "4 7",
        "stroke-linecap": "round",
        "data-branch": treeEdge ? branch : "cross",
        "data-base-opacity": 1,
      });
      const title = svg("title");
      title.textContent = isWrapper
        ? `${sourceName} directly wraps ${dependencyName}`
        : state.graphKind === "modules"
          ? `${sourceName} imports ${dependencyName}`
          : `${sourceName} depends on ${dependencyName} (${[typeReference && "type", valueReference && "body / proof"].filter(Boolean).join(" + ")})`;
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
    const radius = graphNodeRadius({ depth, root: isRoot, selected: isSelected });

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
    const definition = ["def", "abbrev", "opaque"].includes(entry.kind);
    const dot = svg("circle", {
      class: "node-dot",
      r: radius,
      stroke: isSelected ? "#ffffff" : isRoot ? ROOT_NODE_STROKE : "rgba(255,255,255,0.72)",
      "stroke-width": isSelected || isRoot ? 2.4 : 1,
      "stroke-dasharray": entry.generated ? "2 2" : "none",
      "data-kind": entry.kind ?? "module",
      fill: definition ? "#49bda5" : entry.kind === "axiom" ? "#f2b35d"
        : ["inductive", "constructor", "recursor", "quotient"].includes(entry.kind) ? "#b58ae8"
        : isRoot ? ROOT_NODE_COLOR : color,
    });
    group.append(hit, dot);

    const title = svg("title");
    title.textContent = `${name}\n${entry.kind ?? "module"}\n${entry.module}`;
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
  const graphCounts = state.graphKind === "modules"
    ? `${levels.size} modules · ${edgeCount} imports`
    : `${levels.size} nodes · ${edgeCount} edges`;
  ui.graphStatus.textContent = `${graphCounts}${truncated ? ` · capped at ${MAX_NODES} nodes` : ""}`;
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
      button.title = "This consumer is not available in the declaration catalog";
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

function renderModuleDetails(entry) {
  ui.detail.replaceChildren();
  ui.detail.append(element("p", "detail-eyebrow", "Lean module"));
  ui.detail.append(element("h2", "", entry.name));
  ui.detail.append(element("p", "docstring", entry.docString));

  const summary = element("div", "overview-summary");
  summary.append(summaryChip(entry.dependencies.length + " project imports"));
  summary.append(summaryChip(entry.dependents.length + " importers"));
  summary.append(summaryChip(entry.externalImportCount + " external imports"));
  ui.detail.append(summary);

  const actions = element("div", "detail-actions");
  if (entry.name !== state.root) {
    const focus = element("button", "focus-button", "Focus graph here");
    focus.type = "button";
    focus.addEventListener("click", () => focusRoot(entry.name));
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
  ui.detail.append(relationSection("Imports", entry.dependencies));
  ui.detail.append(relationSection("Imported by", entry.dependents));
}

function renderDetails(name) {
  const entry = state.byName.get(name);
  ui.detail.replaceChildren();
  if (!entry) return;
  if (state.graphKind === "modules") {
    renderModuleDetails(entry);
    return;
  }
  ui.detail.append(element("p", "detail-eyebrow", shortModule(entry.module)));
  ui.detail.append(element("h2", "", entry.name));

  const badges = element("div", "badges");
  badges.append(badge(entry.kind));
  if (entry.generated) badges.append(badge("generated"));
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
  ui.detail.append(relationSection("Type dependencies", entry.typeDependencies ?? []));
  ui.detail.append(relationSection("Body / proof dependencies", entry.valueDependencies ?? []));
  ui.detail.append(relationSection("Declaration consumers", entry.dependents));
  ui.detail.append(relationSection("Compiled consumers", entry.compiledConsumers));
}

function writeLocation(push) {
  const url = new URL(window.location.href);
  if (state.page === "imports") {
    url.searchParams.delete("depth");
    url.searchParams.delete("module");
    url.searchParams.delete("browse");
    url.searchParams.set("view", "imports");
    url.searchParams.set("import-module", state.root);
    if (state.direction === "both") url.searchParams.delete("direction");
    else url.searchParams.set("direction", state.direction);
    if (state.depth === 1) url.searchParams.delete("import-depth");
    else url.searchParams.set("import-depth", String(state.depth));
    url.hash = "";
  } else {
    url.searchParams.delete("view");
    url.searchParams.delete("import-module");
    url.searchParams.delete("import-depth");
    if (state.direction === "both") url.searchParams.delete("direction");
    else url.searchParams.set("direction", state.direction);
    if (state.depth === 2) url.searchParams.delete("depth");
    else url.searchParams.set("depth", String(state.depth));
    if (state.module === "*") url.searchParams.delete("module");
    else url.searchParams.set("module", state.module);
    if (!state.root && state.browse && state.browse !== "LeanCondensedMatter") url.searchParams.set("browse", state.browse);
    else url.searchParams.delete("browse");
    url.hash = state.root ?? "";
  }
  const next = `${url.pathname}${url.search}${url.hash}`;
  if (push) history.pushState(null, "", next);
  else history.replaceState(null, "", next);
}

function focusRoot(name, { historyEntry = true } = {}) {
  if (!state.byName.has(name)) return;
  if (state.graphKind === "theorems") {
    if (state.page === "overview") state.returnBrowse = state.browse;
    moduleOverview?.cancel();
    state.page = "theorem";
  } else {
    state.page = "imports";
  }
  state.root = name;
  state.selected = name;
  state.browse = null;
  ui.search.value = name;
  hideSearchResults();
  setGraphModeChrome();
  ui.viewport.hidden = false;
  ui.overview.hidden = true;
  setModuleFilterEnabled(state.graphKind === "theorems");
  renderDetails(name);
  renderGraph();
  if (historyEntry) writeLocation(true);
}

function summaryChip(text) {
  return element("span", "summary-chip", text);
}

function renderOverviewContent() {
  const requestedBrowse = state.browse ?? "LeanCondensedMatter";
  state.browse = requestedBrowse;
  moduleOverview?.render(requestedBrowse).then((rendered) => {
    if (!rendered && state.browse === requestedBrowse) {
      if (requestedBrowse !== "LeanCondensedMatter" && moduleOverview?.hasModule("LeanCondensedMatter")) {
        state.browse = "LeanCondensedMatter";
        writeLocation(false);
        renderOverviewContent();
        return;
      }
      ui.overview.replaceChildren(element("p", "error-message", "The project module hierarchy is unavailable."));
    }
  }).catch((error) => {
    if (state.browse !== requestedBrowse) return;
    console.error(error);
    ui.overview.replaceChildren(element("p", "error-message", error instanceof Error ? error.message : String(error)));
  });
}

function showOverview({ historyEntry = true, browse = null } = {}) {
  moduleOverview?.cancel();
  state.graphKind = "theorems";
  state.catalog = state.theoremCatalog;
  state.byName = state.theoremByName;
  state.page = "overview";
  state.root = null;
  state.selected = null;
  state.returnBrowse = null;
  state.viewBox = null;
  state.graphBounds = null;
  state.module = "*";
  ui.module.value = "*";
  ui.direction.value = state.direction;
  ui.depth.value = String(state.depth);
  const requestedBrowse = browse ?? "LeanCondensedMatter";
  state.browse = moduleOverview?.hasModule(requestedBrowse) && requestedBrowse !== "LeanCondensedMatter"
    ? shortModule(requestedBrowse)
    : "LeanCondensedMatter";
  ui.search.value = "";
  hideSearchResults();
  ui.viewport.hidden = true;
  ui.overview.hidden = false;
  ui.graphToolbar.hidden = true;
  setModuleFilterEnabled(false);
  setGraphModeChrome();
  ui.graphStatus.textContent = "";
  ui.detail.replaceChildren();
  renderOverviewContent();
  if (historyEntry) writeLocation(true);
}

function showModuleImports({ historyEntry = true, moduleName = null, depth = state.depth } = {}) {
  if (state.moduleCatalog.length === 0) return;
  moduleOverview?.cancel();
  const selectedModule = moduleName && state.moduleByName.has(moduleName)
    ? moduleName
    : state.moduleByName.has("LeanCondensedMatter") ? "LeanCondensedMatter" : state.moduleCatalog[0].name;
  state.graphKind = "modules";
  state.catalog = state.moduleCatalog;
  state.byName = state.moduleByName;
  state.page = "imports";
  state.depth = [1, 2, 3, 4].includes(Number(depth)) ? Number(depth) : 1;
  state.root = selectedModule;
  state.selected = selectedModule;
  state.browse = null;
  state.module = "*";
  state.viewBox = null;
  state.graphBounds = null;
  ui.module.value = "*";
  ui.direction.value = state.direction;
  ui.depth.value = String(state.depth);
  ui.search.value = "";
  hideSearchResults();
  setGraphModeChrome();
  ui.viewport.hidden = false;
  ui.overview.hidden = true;
  setModuleFilterEnabled(false);
  renderDetails(selectedModule);
  renderGraph();
  if (historyEntry) writeLocation(true);
}

function populateControls() {
  const modules = [...new Set(state.theoremCatalog.map((entry) => entry.module))].sort((a, b) => a.localeCompare(b));
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
    if (state.graphKind !== "modules" &&
        !declarationAllowed(entry, state.kind, state.generated)) continue;
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
  if (params.get("view") === "imports" && state.moduleCatalog.length > 0) {
    state.direction = ["both", "dependencies", "consumers"].includes(params.get("direction"))
      ? params.get("direction")
      : "both";
    const importDepth = Number(params.get("import-depth") ?? params.get("depth"));
    showModuleImports({
      historyEntry: false,
      moduleName: params.get("import-module"),
      depth: [1, 2, 3, 4].includes(importDepth) ? importDepth : 1,
    });
    if (!state.moduleByName.has(params.get("import-module"))) writeLocation(false);
    return;
  }

  state.graphKind = "theorems";
  state.catalog = state.theoremCatalog;
  state.byName = state.theoremByName;
  const direction = params.get("direction");
  state.direction = ["both", "dependencies", "consumers"].includes(direction) ? direction : "both";
  const depth = Number(params.get("depth"));
  state.depth = [1, 2, 3, 4].includes(depth) ? depth : 2;
  const requestedModule = params.get("module");
  const graphModule = requestedModule && state.catalog.some((entry) => entry.module === requestedModule)
    ? requestedModule
    : "*";
  state.module = graphModule;
  ui.direction.value = state.direction;
  ui.depth.value = String(state.depth);
  ui.module.value = state.module;

  let requested = "";
  try { requested = decodeURIComponent(location.hash.slice(1)); }
  catch { requested = location.hash.slice(1); }
  if (requested && state.byName.has(requested)) {
    focusRoot(requested, { historyEntry: false });
    return;
  }

  const requestedBrowse = params.get("browse");
  const browse = requestedBrowse && moduleOverview?.hasModule(requestedBrowse)
    ? shortModule(requestedBrowse)
    : graphModule !== "*" && moduleOverview?.hasModule(graphModule)
      ? shortModule(graphModule)
      : "LeanCondensedMatter";
  const legacyModuleRoute = !requestedBrowse && graphModule !== "*";
  showOverview({ historyEntry: false, browse });
  if (legacyModuleRoute || (requestedBrowse && !moduleOverview?.hasModule(requestedBrowse))) writeLocation(false);
}

function bindGraphNavigation() {
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
  for (const id of ["kind-filter", "generated-filter"]) {
    document.getElementById(id).addEventListener("change", () => {
      state.kind = document.getElementById("kind-filter").value;
      state.generated = document.getElementById("generated-filter").checked;
      if (state.page === "overview") showOverview({ browse: state.browse });
      else if (state.root) renderGraph();
      renderSearchResults();
    });
  }
  ui.overviewLink.addEventListener("click", () => {
    if (state.page === "theorem") showOverview({ browse: state.returnBrowse });
    else showOverview();
  });
  ui.moduleImportsLink.addEventListener("click", () => showModuleImports());
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
    if (!state.root) return;
    state.module = ui.module.value;
    renderGraph();
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
  if (!response.ok) throw new Error(`failed to load declaration catalog: ${response.status}`);
  state.theoremCatalog = (await response.json()).map(normalizeEntry).sort((a, b) => a.name.localeCompare(b.name));
  state.theoremByName = new Map(state.theoremCatalog.map((entry) => [entry.name, entry]));
  state.catalog = state.theoremCatalog;
  state.byName = state.theoremByName;
  if (state.theoremCatalog.length === 0) throw new Error("declaration catalog is empty");
  try {
    const modulesResponse = await fetch(MODULES_URL, { cache: "no-store" });
    if (!modulesResponse.ok) throw new Error("failed to load module imports: " + modulesResponse.status);
    const moduleData = await modulesResponse.json();
    state.moduleCatalog = buildModuleGraphCatalog(moduleData.modules).catalog;
    state.moduleByName = new Map(state.moduleCatalog.map((entry) => [entry.name, entry]));
  } catch (error) {
    console.error(error);
    ui.moduleImportsLink.disabled = true;
    ui.moduleImportsLink.title = "Module import data is unavailable.";
  }
  moduleOverview = createModuleOverview({
    catalog: state.theoremCatalog,
    allowed: (entry) => declarationAllowed(entry, state.kind, state.generated),
    modules: ["LeanCondensedMatter", ...state.moduleCatalog.map((entry) => entry.name)],
    overview: ui.overview,
    onBrowse: (moduleName) => showOverview({ browse: moduleName }),
    onOpenDeclaration: (name) => focusRoot(name),
  });
  populateControls();
  bindEvents();
  restoreLocation();
}

main().catch((error) => {
  console.error(error);
  ui.graphToolbar.hidden = false;
  ui.graphStatus.textContent = "Failed to load declaration graph.";
  const message = element("p", "error-message", error instanceof Error ? error.message : String(error));
  ui.detail.replaceChildren(message);
});
