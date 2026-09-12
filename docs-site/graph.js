const SVG_NS = "http://www.w3.org/2000/svg";
const MAX_NODES = 80;
const SEARCH_LIMIT = 10;
const CATALOG_URL = "https://raw.githubusercontent.com/naoki-cpp/LeanCondensedMatter/graph-data/theorems.json";

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
  const element = document.createElementNS(SVG_NS, tag);
  for (const [key, value] of Object.entries(attributes)) {
    element.setAttribute(key, String(value));
  }
  return element;
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
  while (common < parts.length && common < rootParts.length && parts[common] === rootParts[common]) {
    common += 1;
  }
  const contextual = parts.slice(common).join(".");
  if (contextual && contextual.length <= 34) return contextual;
  return parts.length <= 3 ? name : `…${parts.slice(-3).join(".")}`;
}

function moduleAllowed(name) {
  if (state.module === "*") return true;
  const entry = state.byName.get(name);
  return entry?.module === state.module;
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
  const matches =
    (state.highlights.has("terminal") && entry.terminal) ||
    (state.highlights.has("zero") && entry.compiledConsumerCount === 0) ||
    (state.highlights.has("single") && entry.singleCompiledConsumer) ||
    (state.highlights.has("wrapper") && entry.directWrapperOf !== null);
  return matches;
}

function layout(levels) {
  const grouped = new Map();
  for (const [name, level] of levels) {
    if (!grouped.has(level)) grouped.set(level, []);
    grouped.get(level).push(name);
  }
  for (const names of grouped.values()) names.sort((a, b) => a.localeCompare(b));

  const levelNumbers = [...grouped.keys()].sort((a, b) => a - b);
  const maxLayer = Math.max(...[...grouped.values()].map((names) => names.length), 1);
  const width = Math.max(900, levelNumbers.length * 260 + 180);
  const height = Math.max(620, maxLayer * 88 + 160);
  const xMargin = 135;
  const yMargin = 80;
  const xSpan = Math.max(1, width - 2 * xMargin);
  const positions = new Map();

  levelNumbers.forEach((level, levelIndex) => {
    const names = grouped.get(level);
    const x = levelNumbers.length === 1
      ? width / 2
      : xMargin + (xSpan * levelIndex) / (levelNumbers.length - 1);
    const usableHeight = height - 2 * yMargin;
    names.forEach((name, index) => {
      const y = names.length === 1
        ? height / 2
        : yMargin + (usableHeight * index) / (names.length - 1);
      positions.set(name, { x, y, level });
    });
  });

  return { positions, width, height };
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

function renderGraph({ preserveView = false } = {}) {
  if (!state.root || !state.byName.has(state.root)) return;

  ui.overview.hidden = true;
  ui.viewport.hidden = false;
  setGraphActionsEnabled(true);

  const previousView = preserveView ? state.viewBox : null;
  const { levels, truncated } = collectNeighborhood();
  const { positions, width, height } = layout(levels);
  ui.graph.replaceChildren();
  state.graphBounds = { x: 0, y: 0, width, height };

  const defs = svg("defs");
  const marker = svg("marker", {
    id: "arrow",
    viewBox: "0 0 10 10",
    refX: 8,
    refY: 5,
    markerWidth: 7,
    markerHeight: 7,
    orient: "auto-start-reverse",
  });
  marker.append(svg("path", { d: "M 0 0 L 10 5 L 0 10 z", class: "arrow-head" }));
  defs.append(marker);
  ui.graph.append(defs);

  const edges = svg("g", { class: "edges" });
  let edgeCount = 0;
  for (const sourceName of levels.keys()) {
    const source = state.byName.get(sourceName);
    const sourcePosition = positions.get(sourceName);
    for (const dependencyName of source.dependencies) {
      if (!levels.has(dependencyName)) continue;
      const targetPosition = positions.get(dependencyName);
      const isWrapper = source.directWrapperOf === dependencyName;
      const line = svg("line", {
        x1: sourcePosition.x,
        y1: sourcePosition.y,
        x2: targetPosition.x,
        y2: targetPosition.y,
        class: isWrapper ? "edge edge-wrapper" : "edge",
        "marker-end": "url(#arrow)",
      });
      const title = svg("title");
      title.textContent = isWrapper
        ? `${sourceName} directly wraps ${dependencyName}`
        : `${sourceName} depends on ${dependencyName}`;
      line.append(title);
      edges.append(line);
      edgeCount += 1;
    }
  }
  ui.graph.append(edges);

  const nodes = svg("g", { class: "nodes" });
  for (const [name, position] of positions) {
    const entry = state.byName.get(name);
    const highlight = highlightMatches(entry);
    const classes = ["node"];
    if (name === state.root) classes.push("node-root");
    if (name === state.selected) classes.push("node-selected");
    if (entry.directWrapperOf !== null) classes.push("node-wrapper");
    if (highlight === true) classes.push("node-highlight");
    if (highlight === false) classes.push("node-dim");

    const group = svg("g", {
      class: classes.join(" "),
      transform: `translate(${position.x}, ${position.y})`,
      tabindex: 0,
      role: "button",
      "aria-label": name,
    });
    group.append(svg("rect", { x: -105, y: -28, width: 210, height: 56, rx: 12 }));

    const label = svg("text", { x: 0, y: -2, "text-anchor": "middle" });
    label.textContent = displayName(name);
    group.append(label);

    const meta = svg("text", {
      x: 0,
      y: 16,
      "text-anchor": "middle",
      class: "node-meta",
    });
    const tags = [];
    if (entry.terminal) tags.push("terminal");
    if (entry.singleCompiledConsumer) tags.push("single consumer");
    if (entry.directWrapperOf !== null) tags.push("wrapper");
    meta.textContent = tags.length > 0 ? tags.join(" · ") : `${entry.dependencies.length} deps`;
    group.append(meta);

    const title = svg("title");
    title.textContent = `${name}\n${entry.module}`;
    group.append(title);

    const select = () => {
      state.selected = name;
      renderDetails(name);
      renderGraph({ preserveView: true });
    };
    group.addEventListener("click", select);
    group.addEventListener("dblclick", () => focusRoot(name));
    group.addEventListener("keydown", (event) => {
      if (event.key === "Enter" || event.key === " ") {
        event.preventDefault();
        select();
      }
    });
    nodes.append(group);
  }
  ui.graph.append(nodes);

  if (previousView) setGraphViewBox(previousView);
  else fitGraph();

  ui.graphStatus.textContent = `${levels.size} nodes · ${edgeCount} edges${truncated ? ` · capped at ${MAX_NODES} nodes` : ""}`;
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
  const heading = document.createElement("h3");
  heading.textContent = `${title} (${names.length})`;
  section.append(heading);

  if (names.length === 0) {
    const empty = document.createElement("p");
    empty.className = "muted";
    empty.textContent = "None";
    section.append(empty);
    return section;
  }

  const list = document.createElement("div");
  list.className = "relation-list";
  for (const name of names.slice(0, 40)) {
    const button = document.createElement("button");
    button.type = "button";
    button.textContent = name;
    if (state.byName.has(name)) {
      button.addEventListener("click", () => focusRoot(name));
    } else {
      button.disabled = true;
      button.title = "This consumer is not a theorem node in the current catalog";
    }
    list.append(button);
  }
  if (names.length > 40) {
    const more = document.createElement("p");
    more.className = "muted";
    more.textContent = `+ ${names.length - 40} more`;
    list.append(more);
  }
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

  const eyebrow = document.createElement("p");
  eyebrow.className = "detail-eyebrow";
  eyebrow.textContent = shortModule(entry.module);
  ui.detail.append(eyebrow);

  const heading = document.createElement("h2");
  heading.textContent = entry.name;
  ui.detail.append(heading);

  const badges = document.createElement("div");
  badges.className = "badges";
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

  const statementHeading = document.createElement("h3");
  statementHeading.textContent = "Statement";
  ui.detail.append(statementHeading);
  const statement = document.createElement("pre");
  statement.textContent = entry.statement;
  ui.detail.append(statement);

  if (entry.docString) {
    const docsHeading = document.createElement("h3");
    docsHeading.textContent = "Documentation";
    ui.detail.append(docsHeading);
    const docs = document.createElement("p");
    docs.className = "docstring";
    docs.textContent = entry.docString;
    ui.detail.append(docs);
  }

  if (entry.directWrapperOf !== null) {
    const wrapper = document.createElement("p");
    wrapper.className = "wrapper-target";
    wrapper.append("Direct wrapper of ");
    const code = document.createElement("code");
    code.textContent = entry.directWrapperOf;
    wrapper.append(code);
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
    "Browse a project area, choose a module, or search directly for a declaration. The dependency graph opens only after you choose a declaration."
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
  if (!resetModule && state.module !== "*" && state.catalog.some((entry) => entry.module === state.module)) {
    renderModule(state.module);
  } else {
    renderDomainOverview();
  }
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
  state.module = requestedModule && state.catalog.some((entry) => entry.module === requestedModule)
    ? requestedModule
    : "*";

  ui.direction.value = state.direction;
  ui.depth.value = String(state.depth);
  ui.module.value = state.module;

  let requested = "";
  try {
    requested = decodeURIComponent(location.hash.slice(1));
  } catch {
    requested = location.hash.slice(1);
  }
  if (requested && state.byName.has(requested)) {
    focusRoot(requested, { historyEntry: false });
  } else {
    showOverview({ historyEntry: false, resetModule: false });
  }
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
    state.drag = {
      pointerId: event.pointerId,
      x: event.clientX,
      y: event.clientY,
      viewBox: { ...state.viewBox },
    };
    ui.viewport.classList.add("dragging");
  });

  ui.viewport.addEventListener("pointermove", (event) => {
    if (!state.drag || event.pointerId !== state.drag.pointerId) return;
    const rect = ui.viewport.getBoundingClientRect();
    const dx = (event.clientX - state.drag.x) * state.drag.viewBox.width / Math.max(1, rect.width);
    const dy = (event.clientY - state.drag.y) * state.drag.viewBox.height / Math.max(1, rect.height);
    setGraphViewBox({
      ...state.drag.viewBox,
      x: state.drag.viewBox.x - dx,
      y: state.drag.viewBox.y - dy,
    });
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
  ui.search.addEventListener("focus", () => {
    if (ui.search.value.trim()) renderSearchResults();
  });
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
    } else if (event.key === "Escape") {
      hideSearchResults();
    }
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
  const message = document.createElement("p");
  message.className = "error-message";
  message.textContent = error instanceof Error ? error.message : String(error);
  ui.detail.replaceChildren(message);
});