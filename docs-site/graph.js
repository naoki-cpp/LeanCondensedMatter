const SVG_NS = "http://www.w3.org/2000/svg";
const MAX_NODES = 80;

const state = {
  catalog: [],
  byName: new Map(),
  root: null,
  selected: null,
  direction: "both",
  depth: 2,
  module: "*",
  highlights: new Set(),
};

const ui = {
  searchForm: document.querySelector("#search-form"),
  search: document.querySelector("#theorem-search"),
  suggestions: document.querySelector("#theorem-suggestions"),
  direction: document.querySelector("#direction"),
  depth: document.querySelector("#depth"),
  module: document.querySelector("#module-filter"),
  graph: document.querySelector("#graph"),
  graphStatus: document.querySelector("#graph-status"),
  detail: document.querySelector("#detail"),
  highlightInputs: [...document.querySelectorAll("[data-highlight]")],
};

function svg(tag, attributes = {}) {
  const element = document.createElementNS(SVG_NS, tag);
  for (const [key, value] of Object.entries(attributes)) {
    element.setAttribute(key, String(value));
  }
  return element;
}

function normalizeEntry(entry) {
  return {
    ...entry,
    dependencies: Array.isArray(entry.dependencies) ? entry.dependencies : [],
    dependents: Array.isArray(entry.dependents) ? entry.dependents : [],
    compiledConsumers: Array.isArray(entry.compiledConsumers) ? entry.compiledConsumers : [],
  };
}

function displayName(name) {
  const parts = name.split(".");
  if (parts.length <= 3) return name;
  return `…${parts.slice(-3).join(".")}`;
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
  const width = Math.max(980, levelNumbers.length * 260 + 180);
  const height = Math.max(660, maxLayer * 88 + 180);
  const xMargin = 135;
  const yMargin = 90;
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

function renderGraph() {
  if (!state.root || !state.byName.has(state.root)) return;

  const { levels, truncated } = collectNeighborhood();
  const { positions, width, height } = layout(levels);
  ui.graph.replaceChildren();
  ui.graph.setAttribute("viewBox", `0 0 ${width} ${height}`);

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
      renderGraph();
    };
    group.addEventListener("click", select);
    group.addEventListener("keydown", (event) => {
      if (event.key === "Enter" || event.key === " ") {
        event.preventDefault();
        select();
      }
    });
    nodes.append(group);
  }
  ui.graph.append(nodes);

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

function renderDetails(name) {
  const entry = state.byName.get(name);
  ui.detail.replaceChildren();
  if (!entry) return;

  const eyebrow = document.createElement("p");
  eyebrow.className = "detail-eyebrow";
  eyebrow.textContent = entry.module;
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

  if (name !== state.root) {
    const focus = document.createElement("button");
    focus.type = "button";
    focus.className = "focus-button";
    focus.textContent = "Focus graph here";
    focus.addEventListener("click", () => focusRoot(name));
    ui.detail.append(focus);
  }

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

function focusRoot(name) {
  if (!state.byName.has(name)) return;
  state.root = name;
  state.selected = name;
  ui.search.value = name;
  history.replaceState(null, "", `#${encodeURIComponent(name)}`);
  renderDetails(name);
  renderGraph();
}

function populateControls() {
  for (const entry of state.catalog) {
    const option = document.createElement("option");
    option.value = entry.name;
    ui.suggestions.append(option);
  }

  const modules = [...new Set(state.catalog.map((entry) => entry.module))].sort((a, b) => a.localeCompare(b));
  for (const moduleName of modules) {
    const option = document.createElement("option");
    option.value = moduleName;
    option.textContent = moduleName;
    ui.module.append(option);
  }
}

function findSearchMatch(query) {
  const needle = query.trim().toLowerCase();
  if (!needle) return null;
  const exact = state.catalog.find((entry) => entry.name.toLowerCase() === needle);
  if (exact) return exact.name;
  return state.catalog.find((entry) => entry.name.toLowerCase().includes(needle))?.name ?? null;
}

function bindEvents() {
  ui.searchForm.addEventListener("submit", (event) => {
    event.preventDefault();
    const match = findSearchMatch(ui.search.value);
    if (match) focusRoot(match);
  });

  ui.direction.addEventListener("change", () => {
    state.direction = ui.direction.value;
    renderGraph();
  });
  ui.depth.addEventListener("change", () => {
    state.depth = Number(ui.depth.value);
    renderGraph();
  });
  ui.module.addEventListener("change", () => {
    state.module = ui.module.value;
    renderGraph();
  });
  for (const input of ui.highlightInputs) {
    input.addEventListener("change", () => {
      if (input.checked) state.highlights.add(input.dataset.highlight);
      else state.highlights.delete(input.dataset.highlight);
      renderGraph();
    });
  }
}

async function main() {
  const response = await fetch("./data/theorems.json");
  if (!response.ok) throw new Error(`failed to load theorem catalog: ${response.status}`);
  state.catalog = (await response.json()).map(normalizeEntry).sort((a, b) => a.name.localeCompare(b.name));
  state.byName = new Map(state.catalog.map((entry) => [entry.name, entry]));

  if (state.catalog.length === 0) throw new Error("theorem catalog is empty");

  populateControls();
  bindEvents();

  const requested = decodeURIComponent(location.hash.slice(1));
  const initial = state.byName.has(requested)
    ? requested
    : [...state.catalog].sort((a, b) => {
        const aScore = a.dependencies.length + a.dependents.length;
        const bScore = b.dependencies.length + b.dependents.length;
        return bScore - aScore || a.name.localeCompare(b.name);
      })[0].name;
  focusRoot(initial);
}

main().catch((error) => {
  console.error(error);
  ui.graphStatus.textContent = "Failed to load declaration graph.";
  const message = document.createElement("p");
  message.className = "error-message";
  message.textContent = error instanceof Error ? error.message : String(error);
  ui.detail.replaceChildren(message);
});
