const SVG_NS = "http://www.w3.org/2000/svg";
const PROJECT_PREFIX = "LeanCondensedMatter.";
const VISIBLE_NEIGHBORS = 40;
const CANVAS_WIDTH = 1120;
const NODE_WIDTH = 290;
const NODE_HEIGHT = 40;

function element(tag, className = "", text = "") {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text) node.textContent = text;
  return node;
}

function svg(tag, attributes = {}) {
  const node = document.createElementNS(SVG_NS, tag);
  for (const [key, value] of Object.entries(attributes)) node.setAttribute(key, String(value));
  return node;
}

function shortModule(name) {
  return name.startsWith(PROJECT_PREFIX) ? name.slice(PROJECT_PREFIX.length) : name;
}

function displayModule(name) {
  const short = shortModule(name);
  return short.length > 39 ? "..." + short.slice(-36) : short;
}

function sourceUrl(module) {
  const path = module.sourceFile.split("/").map(encodeURIComponent).join("/");
  return "https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/" + path;
}

export function createModuleImportExplorer({ overview, modules, onSelect }) {
  const byName = new Map(modules.map((module) => [module.name, module]));
  const names = [...byName.keys()].sort((a, b) => a.localeCompare(b));
  if (names.length === 0) throw new Error("module import data is empty");
  const importers = new Map(names.map((name) => [name, []]));
  const internalImports = new Map();
  const moduleOptions = element("datalist");
  moduleOptions.id = "module-import-options";
  for (const name of names) {
    const option = element("option");
    option.value = name;
    moduleOptions.append(option);
  }
  let importCount = 0;

  for (const module of modules) {
    const imports = module.imports.filter((name) => byName.has(name)).sort((a, b) => a.localeCompare(b));
    internalImports.set(module.name, imports);
    importCount += imports.length;
    for (const imported of imports) importers.get(imported).push(module.name);
  }
  for (const values of importers.values()) values.sort((a, b) => a.localeCompare(b));

  function makeSearchForm(selectedName) {
    const form = element("form", "module-import-search");
    const label = element("label", "", "Module");
    const input = element("input");
    const listId = moduleOptions.id;
    input.type = "search";
    input.setAttribute("list", listId);
    input.setAttribute("aria-label", "Find a Lean module");
    input.placeholder = "Search module name";
    input.value = selectedName;
    input.id = listId + "-input";
    label.htmlFor = input.id;
    const button = element("button", "", "Show imports");
    button.type = "submit";
    const message = element("p", "module-import-note");
    message.hidden = true;
    form.addEventListener("submit", (event) => {
      event.preventDefault();
      const value = input.value.trim();
      const matches = byName.has(value) ? [value] : names.filter((name) => shortModule(name) === value);
      if (matches.length === 1) onSelect(matches[0]);
      else {
        message.hidden = false;
        message.textContent = matches.length > 1
          ? "That short name matches multiple modules. Choose the full module name from suggestions."
          : "Choose a module from the suggestions.";
      }
    });
    form.append(label, input, moduleOptions, button);
    overview.append(form, message);
  }

  function addEdge(group, startX, startY, endX, endY) {
    const bend = Math.max(34, Math.abs(endX - startX) * 0.4);
    const direction = endX < startX ? -1 : 1;
    const path = svg("path", {
      class: "import-edge",
      d: "M " + startX + " " + startY
        + " C " + (startX + direction * bend) + " " + startY
        + ", " + (endX - direction * bend) + " " + endY
        + ", " + endX + " " + endY,
    });
    group.append(path);
  }

  function addNode(group, name, x, y, { root = false, relation = "" } = {}) {
    const node = svg("g", { class: "import-node" + (root ? " root" : " neighbor") });
    const rect = svg("rect", {
      x,
      y: y - NODE_HEIGHT / 2,
      width: NODE_WIDTH,
      height: NODE_HEIGHT,
      rx: 9,
    });
    const text = svg("text", { x: x + NODE_WIDTH / 2, y: y + 4 });
    text.textContent = displayModule(name);
    const title = svg("title");
    title.textContent = name + (relation ? " - " + relation : "");
    node.append(rect, text, title);
    if (!root) {
      node.setAttribute("tabindex", "0");
      node.setAttribute("role", "button");
      node.setAttribute("aria-label", "Show imports for " + name);
      const activate = () => onSelect(name);
      node.addEventListener("click", activate);
      node.addEventListener("keydown", (event) => {
        if (event.key === "Enter" || event.key === " ") {
          event.preventDefault();
          activate();
        }
      });
    }
    group.append(node);
  }

  function render(moduleName) {
    const module = byName.get(moduleName);
    if (!module) return false;
    overview.replaceChildren();
    const header = element("div", "overview-header module-overview-header");
    header.append(element("p", "module-overview-eyebrow", "Direct import relationships"));
    header.append(element("h2", "", "Module imports"));
    header.append(element(
      "p",
      "",
      "This view shows direct imports between LeanCondensedMatter modules; external dependencies are counted separately. Select a neighboring module to continue browsing.",
    ));
    const summary = element("div", "overview-summary");
    summary.append(element("span", "summary-chip", names.length + " source modules"));
    summary.append(element("span", "summary-chip", importCount + " internal imports"));
    header.append(summary);
    overview.append(header);
    makeSearchForm(moduleName);

    const dependencies = internalImports.get(moduleName);
    const dependents = importers.get(moduleName) ?? [];
    const selectedHeader = element("section", "overview-section");
    selectedHeader.append(element("h3", "", module.name));
    const source = element("a", "module-import-source", "Open Lean source on GitHub");
    source.href = sourceUrl(module);
    source.target = "_blank";
    source.rel = "noreferrer";
    selectedHeader.append(source);
    const counts = element("div", "overview-summary");
    counts.append(element("span", "summary-chip", dependencies.length + " direct imports"));
    counts.append(element("span", "summary-chip", dependents.length + " importers"));
    counts.append(element("span", "summary-chip", module.externalImportCount + " external imports"));
    selectedHeader.append(counts);
    overview.append(selectedHeader);

    const visibleDependencies = dependencies.slice(0, VISIBLE_NEIGHBORS);
    const visibleDependents = dependents.slice(0, VISIBLE_NEIGHBORS);
    const rows = Math.max(visibleDependencies.length, visibleDependents.length);
    const height = Math.max(300, (rows + 1) * 54);
    const centerY = height / 2;
    const diagramScroll = element("div", "module-import-diagram-scroll");
    const diagram = svg("svg", {
      class: "module-import-diagram",
      viewBox: "0 0 " + CANVAS_WIDTH + " " + height,
      width: CANVAS_WIDTH,
      height,
      role: "group",
      "aria-label": "Direct module imports and importers for " + module.name,
    });
    const defs = svg("defs");
    const marker = svg("marker", {
      id: "module-import-arrow",
      viewBox: "0 0 8 8",
      refX: 7,
      refY: 4,
      markerWidth: 7,
      markerHeight: 7,
      orient: "auto",
    });
    marker.append(svg("path", { d: "M 0 0 L 8 4 L 0 8 Z", fill: "#71e7dc" }));
    defs.append(marker);
    diagram.append(defs);

    const headings = svg("g", { "aria-hidden": "true" });
    const importsHeading = svg("text", { class: "column-heading", x: 180, y: 24 });
    importsHeading.textContent = "Imports";
    const importersHeading = svg("text", { class: "column-heading", x: 945, y: 24 });
    importersHeading.textContent = "Imported by";
    headings.append(importsHeading, importersHeading);
    diagram.append(headings);

    const edges = svg("g", { "aria-hidden": "true" });
    visibleDependencies.forEach((name, index) => {
      const y = ((index + 1) * height) / (visibleDependencies.length + 1);
      addEdge(edges, 415, centerY, 326, y);
    });
    visibleDependents.forEach((name, index) => {
      const y = ((index + 1) * height) / (visibleDependents.length + 1);
      addEdge(edges, 800, y, 706, centerY);
    });
    diagram.append(edges);

    const nodes = svg("g");
    visibleDependencies.forEach((name, index) => {
      const y = ((index + 1) * height) / (visibleDependencies.length + 1);
      addNode(nodes, name, 35, y, { relation: "imported by " + module.name });
    });
    addNode(nodes, module.name, 415, centerY, { root: true });
    visibleDependents.forEach((name, index) => {
      const y = ((index + 1) * height) / (visibleDependents.length + 1);
      addNode(nodes, name, 800, y, { relation: "imports " + module.name });
    });
    diagram.append(nodes);
    diagramScroll.append(diagram);
    overview.append(diagramScroll);

    const note = element("p", "module-import-note");
    note.textContent = "Arrows point from the importing module to the module it imports. External dependencies are counted above but not drawn.";
    if (dependencies.length > VISIBLE_NEIGHBORS || dependents.length > VISIBLE_NEIGHBORS) {
      note.textContent += " Showing " + visibleDependencies.length + " of " + dependencies.length
        + " imports and " + visibleDependents.length + " of " + dependents.length
        + " importers. Search for a module to recenter the view.";
    }
    overview.append(note);
    return true;
  }

  return {
    defaultModule: byName.has("LeanCondensedMatter") ? "LeanCondensedMatter" : names[0],
    hasModule(name) {
      return typeof name === "string" && byName.has(name);
    },
    render,
    summary: { moduleCount: names.length, importCount },
  };
}
