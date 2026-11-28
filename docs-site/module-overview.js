const REPOSITORY_ROOT_URL = "https://raw.githubusercontent.com/naoki-cpp/LeanCondensedMatter/main";
const SOURCE_ROOT_URL = `${REPOSITORY_ROOT_URL}/${PROJECT_NAME}`;

import { buildDeclarationHierarchy, modulePath, PROJECT_NAME } from "./declaration-hierarchy.js";
import { declarationAllowed, declarationCounts } from "./declaration-model.js";
import { renderResearchMap } from "./research-map.js";

function element(tag, className = "", text = "") {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text) node.textContent = text;
  return node;
}

function moduleSourceUrl(moduleName) {
  if (moduleName === PROJECT_NAME) return `${REPOSITORY_ROOT_URL}/${PROJECT_NAME}.lean`;
  return `${SOURCE_ROOT_URL}/${modulePath(moduleName).join("/")}.lean`;
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

function summaryChip(text) {
  return element("span", "summary-chip", text);
}

export function createModuleOverview({ catalog, modules = [], onBrowse, onOpenDeclaration,
  allowed = (entry) => declarationAllowed(entry) }) {
  const moduleDescriptionPromises = new Map();

  const tree = buildDeclarationHierarchy(catalog, modules);

  function loadModuleDescription(moduleName) {
    const canonicalName = modulePath(moduleName).join(".") || PROJECT_NAME;
    if (!moduleDescriptionPromises.has(canonicalName)) {
      const descriptionPromise = fetch(moduleSourceUrl(canonicalName), { cache: "no-store" })
        .then((response) => (response.ok ? response.text() : ""))
        .then(extractModuleDescription)
        .catch(() => "");
      moduleDescriptionPromises.set(canonicalName, descriptionPromise);
    }
    return moduleDescriptionPromises.get(canonicalName);
  }

  function renderBreadcrumb(path, browse = onBrowse) {
    const breadcrumb = element("nav", "module-breadcrumb");
    breadcrumb.setAttribute("aria-label", "Module hierarchy");

    const project = element("button", "module-crumb", PROJECT_NAME);
    project.type = "button";
    project.disabled = path.length === 0;
    project.addEventListener("click", () => browse(PROJECT_NAME));
    breadcrumb.append(project);

    path.forEach((segment, index) => {
      breadcrumb.append(element("span", "module-crumb-separator", "/"));
      const crumb = element("button", "module-crumb", segment);
      crumb.type = "button";
      crumb.disabled = index === path.length - 1;
      const target = path.slice(0, index + 1).join(".");
      crumb.addEventListener("click", () => browse(target));
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

  async function prepare(moduleName, selectedName) {
    const parts = modulePath(moduleName);
    const node = tree.find(moduleName);
    if (!node) return null;

    const children = [...node.children.values()].sort(
      (a, b) => b.declarationCount - a.declarationCount || a.name.localeCompare(b.name),
    );
    const description = await loadModuleDescription(node.fullName);

    return () => buildContent(node, parts, children, description, selectedName);
  }

  function buildContent(node, parts, children, description, selectedName) {
    const content = [];
    const breadcrumb = element("div", "");
    breadcrumb.append(renderBreadcrumb(parts));

    const header = element("div", "overview-header module-overview-header");
    const isMap = children.length > 0 && parts.length === 0;
    if (!isMap) header.append(element("h2", "", node.name));
    const descriptionField = element("p", "module-description module-header-description", description);
    descriptionField.hidden = !description;
    header.append(descriptionField);
    const summary = element("div", "overview-summary");
    const visibleTree = isMap ? buildDeclarationHierarchy(catalog.filter(allowed)) : null;
    const mapRegions = children.map((child) => visibleTree?.find(child.fullName)).filter(Boolean);
    const mapEntries = mapRegions.flatMap((child) => child.entries);
    const mapCounts = declarationCounts(mapEntries, { includeGenerated: true });
    function showSummary(current, counts = current.counts) {
      const chips = [summaryChip(`Definitions ${counts.definitions}`),
        summaryChip(`Theorems ${counts.theorems}`), summaryChip(`Total ${counts.total}`)];
      if (counts.generated) chips.push(summaryChip(`Generated ${counts.generated}`));
      chips.push(summaryChip(`${current.moduleCount} module${current.moduleCount === 1 ? "" : "s"}`),
        summaryChip(`${current.children.size} direct submodule${current.children.size === 1 ? "" : "s"}`));
      summary.replaceChildren(...chips);
    }
    showSummary(node, isMap ? mapCounts : undefined);
    header.append(summary);
    if (isMap) {
      let descriptionRequest = 0;
      function updateMapHeader(moduleName, browseMap) {
        const request = ++descriptionRequest;
        const path = moduleName ? modulePath(moduleName) : [];
        const current = (moduleName && tree.find(moduleName)) || node;
        breadcrumb.replaceChildren(renderBreadcrumb(path, browseMap));
        showSummary(current, moduleName ? visibleTree.find(moduleName)?.visibleCounts : mapCounts);
        descriptionField.textContent = moduleName ? "" : description;
        descriptionField.hidden = !descriptionField.textContent;
        if (!moduleName) return;
        loadModuleDescription(moduleName).then((text) => {
          if (request !== descriptionRequest) return;
          descriptionField.textContent = text;
          descriptionField.hidden = !text;
        });
      }
      content.push(renderResearchMap(mapRegions, onOpenDeclaration, updateMapHeader, [breadcrumb, header], node.name, visibleTree, mapCounts, selectedName));
    } else {
      content.push(breadcrumb, header);
    }
    if (children.length > 0 && parts.length > 0) {
      const section = element("section", "overview-section");
      section.append(element("h3", "", "Direct submodules"));
      const grid = element("div", "module-tree-grid");
      children.forEach((child) => grid.append(moduleCard(child)));
      section.append(grid);
      content.push(section);
    }

    if (node.declarations.length > 0) {
      const direct = node.declarations.filter(allowed);
      const section = element("section", "overview-section");
      const head = element("div", "overview-section-head");
      head.append(element("h3", "", "Declarations in this module"));
      head.append(element("span", "module-direct-count", String(direct.length)));
      section.append(head);
      const list = element("div", "declaration-list");
      for (const entry of direct) list.append(declarationCard(entry));
      section.append(list);
      content.push(section);
    }
    return content;
  }

  return {
    hasModule(moduleName) {
      return tree.find(moduleName) !== null;
    },
    prepare,
  };
}
