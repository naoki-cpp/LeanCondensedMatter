const CATALOG_URL = "https://raw.githubusercontent.com/naoki-cpp/LeanCondensedMatter/graph-data/theorems.json";
const SOURCE_ROOT_URL = "https://raw.githubusercontent.com/naoki-cpp/LeanCondensedMatter/main/LeanCondensedMatter";
const PROJECT_PREFIX = "LeanCondensedMatter.";

const overview = document.querySelector("#overview");
const overviewLink = document.querySelector("#overview-link");
const searchForm = document.querySelector("#search-form");
const searchInput = document.querySelector("#theorem-search");
const moduleFilter = document.querySelector("#module-filter");
const graphViewport = document.querySelector("#graph-viewport");

let catalogPromise = null;
let canonicalizingLegacyModule = false;
let hierarchyRenderVersion = 0;
const moduleDescriptionPromises = new Map();

function element(tag, className = "", text = "") {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text) node.textContent = text;
  return node;
}

function shortModule(moduleName) {
  return moduleName.startsWith(PROJECT_PREFIX) ? moduleName.slice(PROJECT_PREFIX.length) : moduleName;
}

function moduleParts(moduleName) {
  return shortModule(moduleName).split(".").filter(Boolean);
}

function moduleSourceUrl(moduleName) {
  return `${SOURCE_ROOT_URL}/${moduleParts(moduleName).join("/")}.lean`;
}

function extractModuleDescription(source) {
  const match = source.match(/\/-!\s*([\s\S]*?)\s*-\//);
  if (!match) return "";

  const paragraphs = match[1]
    .split(/\n\s*\n/)
    .map((block) => block.trim())
    .filter(Boolean);
  const description = paragraphs.find((block) => !block.startsWith("#"));
  if (!description) return "";

  return description
    .split("\n")
    .map((line) => line.trim())
    .filter(Boolean)
    .join(" ")
    .replace(/`([^`]+)`/g, "$1");
}

function loadModuleDescription(moduleName) {
  const canonicalName = shortModule(moduleName);
  if (!moduleDescriptionPromises.has(canonicalName)) {
    const descriptionPromise = fetch(moduleSourceUrl(canonicalName), { cache: "no-store" })
      .then((response) => (response.ok ? response.text() : ""))
      .then(extractModuleDescription)
      .catch(() => "");
    moduleDescriptionPromises.set(canonicalName, descriptionPromise);
  }
  return moduleDescriptionPromises.get(canonicalName);
}

function declarationBaseName(name) {
  return name.split(".").at(-1) ?? name;
}

async function loadCatalog() {
  if (!catalogPromise) {
    catalogPromise = fetch(CATALOG_URL, { cache: "no-store" }).then(async (response) => {
      if (!response.ok) throw new Error(`failed to load theorem catalog: ${response.status}`);
      return response.json();
    });
  }
  return catalogPromise;
}

function makeTree(domain, entries) {
  const root = {
    name: domain,
    fullName: domain,
    children: new Map(),
    declarations: [],
    declarationCount: 0,
    moduleCount: 1,
  };

  for (const entry of entries) {
    const parts = moduleParts(entry.module);
    if (parts[0] !== domain) continue;
    let node = root;
    for (const part of parts.slice(1)) {
      if (!node.children.has(part)) {
        node.children.set(part, {
          name: part,
          fullName: `${node.fullName}.${part}`,
          children: new Map(),
          declarations: [],
          declarationCount: 0,
          moduleCount: 1,
        });
      }
      node = node.children.get(part);
    }
    node.declarations.push(entry);
  }

  function summarize(node) {
    node.declarations.sort((a, b) => a.name.localeCompare(b.name));
    let declarations = node.declarations.length;
    let modules = 1;
    for (const child of node.children.values()) {
      summarize(child);
      declarations += child.declarationCount;
      modules += child.moduleCount;
    }
    node.declarationCount = declarations;
    node.moduleCount = modules;
  }

  summarize(root);
  return root;
}

function resolveNode(root, path) {
  let node = root;
  for (const segment of path) {
    node = node.children.get(segment);
    if (!node) return null;
  }
  return node;
}

function summaryChip(text) {
  return element("span", "summary-chip", text);
}

function renderBreadcrumb(domain, path) {
  const breadcrumb = element("nav", "module-breadcrumb");
  breadcrumb.setAttribute("aria-label", "Module hierarchy");

  const allAreas = element("button", "module-crumb", "All areas");
  allAreas.type = "button";
  allAreas.addEventListener("click", () => overviewLink?.click());
  breadcrumb.append(allAreas);

  const segments = [domain, ...path];
  segments.forEach((segment, index) => {
    breadcrumb.append(element("span", "module-crumb-separator", "/"));
    const crumb = element("button", "module-crumb", segment);
    crumb.type = "button";
    crumb.disabled = index === segments.length - 1;
    crumb.addEventListener("click", () => renderHierarchy(domain, path.slice(0, index)));
    breadcrumb.append(crumb);
  });
  return breadcrumb;
}

function openDeclaration(entry) {
  if (!searchForm || !searchInput) return;
  searchInput.value = entry.name;
  searchInput.dispatchEvent(new Event("input", { bubbles: true }));
  searchForm.dispatchEvent(new Event("submit", { bubbles: true, cancelable: true }));
}

function moduleCard(domain, path, child, description) {
  const button = element("button", "module-tree-card");
  button.type = "button";

  const heading = element("span", "module-tree-card-heading");
  heading.append(element("strong", "", child.name));
  if (child.children.size > 0) heading.append(element("span", "module-tree-chevron", "›"));
  button.append(heading);

  const details = [];
  details.push(`${child.declarationCount} declaration${child.declarationCount === 1 ? "" : "s"}`);
  if (child.moduleCount > 1) details.push(`${child.moduleCount} modules`);
  button.append(element("small", "", details.join(" · ")));
  if (description) button.append(element("span", "module-description module-card-description", description));

  button.addEventListener("click", () => renderHierarchy(domain, [...path, child.name]));
  return button;
}

function declarationCard(entry) {
  const button = element("button", "declaration-card module-declaration-card");
  button.type = "button";
  button.append(element("strong", "", declarationBaseName(entry.name)));
  const context = entry.docString?.trim() || entry.statement || entry.name;
  button.append(element("small", "", context.slice(0, 150)));
  button.addEventListener("click", () => openDeclaration(entry));
  return button;
}

async function renderHierarchy(domain, path = []) {
  const renderVersion = ++hierarchyRenderVersion;
  const catalog = await loadCatalog();
  const entries = catalog.filter((entry) => moduleParts(entry.module)[0] === domain);
  const tree = makeTree(domain, entries);
  const node = resolveNode(tree, path);
  if (!node || !overview || renderVersion !== hierarchyRenderVersion) return;

  const children = [...node.children.values()].sort(
    (a, b) => b.declarationCount - a.declarationCount || a.name.localeCompare(b.name),
  );
  const descriptions = await Promise.all([
    loadModuleDescription(node.fullName),
    ...children.map((child) => loadModuleDescription(child.fullName)),
  ]);
  if (renderVersion !== hierarchyRenderVersion) return;

  overview.replaceChildren();
  overview.append(renderBreadcrumb(domain, path));

  const header = element("div", "overview-header module-overview-header");
  header.append(element("p", "module-overview-eyebrow", "Module hierarchy"));
  header.append(element("h2", "", node.fullName));
  if (descriptions[0]) header.append(element("p", "module-description module-header-description", descriptions[0]));
  const summary = element("div", "overview-summary");
  summary.append(summaryChip(`${node.declarationCount} declarations`));
  summary.append(summaryChip(`${node.moduleCount} module${node.moduleCount === 1 ? "" : "s"}`));
  summary.append(summaryChip(`${node.children.size} direct submodule${node.children.size === 1 ? "" : "s"}`));
  header.append(summary);
  overview.append(header);

  if (children.length > 0) {
    const section = element("section", "overview-section");
    section.append(element("h3", "", "Direct submodules"));
    const grid = element("div", "module-tree-grid");
    children.forEach((child, index) => grid.append(moduleCard(domain, path, child, descriptions[index + 1])));
    section.append(grid);
    overview.append(section);
  }

  if (node.declarations.length > 0) {
    const section = element("section", "overview-section");
    const head = element("div", "overview-section-head");
    head.append(element("h3", "", "Declarations in this module"));
    head.append(element("span", "module-direct-count", String(node.declarations.length)));
    section.append(head);
    const list = element("div", "declaration-list");
    for (const entry of node.declarations) list.append(declarationCard(entry));
    section.append(list);
    overview.append(section);
  }
}

function syncModuleFilterAvailability() {
  if (!moduleFilter || !graphViewport) return;
  const graphActive = !graphViewport.hidden;
  moduleFilter.disabled = !graphActive;
  moduleFilter.title = graphActive
    ? "Filter the current dependency graph by exact module."
    : "Browse modules through the overview hierarchy.";
}

async function hydrateDomainDescriptions() {
  if (!overview || overview.hidden) return;
  const cards = [...overview.querySelectorAll(".domain-card")];
  await Promise.all(cards.map(async (card) => {
    if (card.dataset.moduleDescriptionHydrated) return;
    const domain = card.querySelector("strong")?.textContent?.trim();
    if (!domain) return;
    card.dataset.moduleDescriptionHydrated = "pending";
    const description = await loadModuleDescription(domain);
    if (description && card.isConnected && !card.querySelector(".domain-description")) {
      card.append(element("span", "module-description domain-description", description));
    }
    card.dataset.moduleDescriptionHydrated = "true";
  }));
}

async function canonicalizeLegacyModuleRoute() {
  if (canonicalizingLegacyModule || !overview || overview.hidden || !moduleFilter) return;
  if (moduleFilter.options.length <= 1) return;
  if (location.hash) return;
  const requestedModule = new URLSearchParams(location.search).get("module");
  if (!requestedModule) return;
  const parts = moduleParts(requestedModule);
  if (parts.length === 0) return;

  canonicalizingLegacyModule = true;
  try {
    moduleFilter.value = "*";
    moduleFilter.dispatchEvent(new Event("change", { bubbles: true }));
    await renderHierarchy(parts[0], parts.slice(1));
  } finally {
    canonicalizingLegacyModule = false;
  }
}

function syncOverviewNavigationMode() {
  syncModuleFilterAvailability();
  hydrateDomainDescriptions().catch((error) => console.error(error));
  canonicalizeLegacyModuleRoute().catch((error) => console.error(error));
}

const navigationObserver = new MutationObserver(syncOverviewNavigationMode);
if (overview) navigationObserver.observe(overview, { attributes: true, attributeFilter: ["hidden"], childList: true });
if (graphViewport) navigationObserver.observe(graphViewport, { attributes: true, attributeFilter: ["hidden"] });
if (moduleFilter) navigationObserver.observe(moduleFilter, { childList: true });
syncOverviewNavigationMode();

// The base explorer owns the project-area cards. Capture those clicks before its
// flat domain renderer and replace only the domain-detail view with hierarchy.
document.addEventListener("click", (event) => {
  const card = event.target.closest?.(".domain-card");
  if (!card || !overview?.contains(card)) return;
  const domain = card.querySelector("strong")?.textContent?.trim();
  if (!domain) return;
  event.preventDefault();
  event.stopImmediatePropagation();
  renderHierarchy(domain).catch((error) => {
    console.error(error);
    overview.replaceChildren(element("p", "error-message", error instanceof Error ? error.message : String(error)));
  });
}, true);
