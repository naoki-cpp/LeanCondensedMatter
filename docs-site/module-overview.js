const REPOSITORY_ROOT_URL = "https://raw.githubusercontent.com/naoki-cpp/LeanCondensedMatter/main";
const PROJECT_NAME = "LeanCondensedMatter";
const PROJECT_PREFIX = "LeanCondensedMatter.";
const SOURCE_ROOT_URL = `${REPOSITORY_ROOT_URL}/${PROJECT_NAME}`;

import { declarationAllowed, declarationCounts } from "./declaration-model.js";

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
  if (moduleName === PROJECT_NAME) return `${REPOSITORY_ROOT_URL}/${PROJECT_NAME}.lean`;
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

function declarationBaseName(name) {
  return name.split(".").at(-1) ?? name;
}

function makeNode(name, fullName) {
  return {
    name,
    fullName,
    children: new Map(),
    declarations: [],
    declarationCount: 0,
    moduleCount: 1,
  };
}

function relativeModuleParts(moduleName) {
  return moduleName === PROJECT_NAME ? [] : moduleParts(moduleName);
}

function makeTree(entries, modules) {
  const root = makeNode(PROJECT_NAME, PROJECT_NAME);

  function ensureModule(moduleName) {
    let node = root;
    for (const part of relativeModuleParts(moduleName)) {
      if (!node.children.has(part)) {
        node.children.set(part, makeNode(part, `${node.fullName}.${part}`));
      }
      node = node.children.get(part);
    }
    return node;
  }

  for (const moduleName of modules) ensureModule(moduleName);
  for (const entry of entries) {
    ensureModule(entry.module).declarations.push(entry);
  }

  function summarize(node) {
    node.declarations.sort((a, b) => a.name.localeCompare(b.name));
    const counts = declarationCounts(node.declarations);
    let modules = 1;
    for (const child of node.children.values()) {
      summarize(child);
      for (const key of Object.keys(counts)) counts[key] += child.counts[key];
      modules += child.moduleCount;
    }
    node.counts = counts;
    node.declarationCount = counts.total;
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

export function createModuleOverview({ catalog, modules = [], overview, onBrowse, onOpenDeclaration,
  allowed = (entry) => declarationAllowed(entry) }) {
  const moduleDescriptionPromises = new Map();
  let hierarchyRenderVersion = 0;

  const tree = makeTree(catalog, [PROJECT_NAME, ...modules]);

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

  function renderBreadcrumb(path) {
    const breadcrumb = element("nav", "module-breadcrumb");
    breadcrumb.setAttribute("aria-label", "Module hierarchy");

    const project = element("button", "module-crumb", PROJECT_NAME);
    project.type = "button";
    project.disabled = path.length === 0;
    project.addEventListener("click", () => onBrowse(PROJECT_NAME));
    breadcrumb.append(project);

    path.forEach((segment, index) => {
      breadcrumb.append(element("span", "module-crumb-separator", "/"));
      const crumb = element("button", "module-crumb", segment);
      crumb.type = "button";
      crumb.disabled = index === path.length - 1;
      const target = path.slice(0, index + 1).join(".");
      crumb.addEventListener("click", () => onBrowse(target));
      breadcrumb.append(crumb);
    });
    return breadcrumb;
  }

  function moduleCard(child) {
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

    button.addEventListener("click", () => onBrowse(child.fullName));
    return button;
  }

  function declarationCard(entry) {
    const button = element("button", "declaration-card module-declaration-card");
    button.type = "button";
    button.append(element("strong", "", declarationBaseName(entry.name)));
    button.append(element("span", "badge", entry.kind));
    if (entry.generated) button.append(element("span", "badge", "generated"));
    const context = entry.docString?.trim() || entry.statement || entry.name;
    button.append(element("small", "", context.slice(0, 150)));
    button.addEventListener("click", () => onOpenDeclaration(entry.name));
    return button;
  }

  async function render(moduleName) {
    const canonicalName = shortModule(moduleName);
    const parts = relativeModuleParts(canonicalName);
    const renderVersion = ++hierarchyRenderVersion;
    const node = resolveNode(tree, parts);
    if (!node) return false;
    // A superseded valid request is handled by the newer render, so it must not
    // trigger the owner's invalid-target fallback even when the browse value is unchanged.
    if (renderVersion !== hierarchyRenderVersion) return true;

    const children = [...node.children.values()].sort(
      (a, b) => b.declarationCount - a.declarationCount || a.name.localeCompare(b.name),
    );
    const description = await loadModuleDescription(node.fullName);
    if (renderVersion !== hierarchyRenderVersion) return true;

    overview.replaceChildren();
    overview.append(renderBreadcrumb(parts));

    const header = element("div", "overview-header module-overview-header");
    header.append(element("h2", "", node.fullName));
    if (description) header.append(element("p", "module-description module-header-description", description));
    const summary = element("div", "overview-summary");
    const counts = node.counts;
    summary.append(summaryChip(`Definitions ${counts.definitions}`));
    summary.append(summaryChip(`Theorems ${counts.theorems}`));
    summary.append(summaryChip(`Total ${counts.total}`));
    if (counts.generated) summary.append(summaryChip(`Generated ${counts.generated}`));
    summary.append(summaryChip(`${node.declarationCount} declarations`));
    summary.append(summaryChip(`${node.moduleCount} module${node.moduleCount === 1 ? "" : "s"}`));
    summary.append(summaryChip(`${node.children.size} direct submodule${node.children.size === 1 ? "" : "s"}`));
    header.append(summary);
    overview.append(header);

    if (children.length > 0) {
      const section = element("section", "overview-section");
      section.append(element("h3", "", "Direct submodules"));
      const grid = element("div", "module-tree-grid");
      children.forEach((child) => grid.append(moduleCard(child)));
      section.append(grid);
      overview.append(section);
    }

    if (node.declarations.length > 0) {
      const section = element("section", "overview-section");
      const head = element("div", "overview-section-head");
      head.append(element("h3", "", "Declarations in this module"));
      head.append(element("span", "module-direct-count", String(node.declarations.filter(allowed).length)));
      section.append(head);
      const list = element("div", "declaration-list");
      for (const entry of node.declarations.filter(allowed)) list.append(declarationCard(entry));
      section.append(list);
      overview.append(section);
    }
    return true;
  }

  return {
    cancel() {
      hierarchyRenderVersion += 1;
    },
    hasModule(moduleName) {
      const parts = relativeModuleParts(shortModule(moduleName));
      return resolveNode(tree, parts) !== null;
    },
    render,
  };
}
