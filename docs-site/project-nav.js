const projectRoot = "LeanCondensedMatter";

function topLevelModuleName(section) {
  const summary = section.querySelector(":scope > summary");
  if (!summary) return "";

  const leadingText = summary.firstChild?.textContent ?? summary.textContent;
  return leadingText.replace(/\s*\(\s*$/, "").trim();
}

function filterProjectNavigation() {
  const moduleList = document.querySelector(".module_list");
  if (!moduleList) return;

  for (const section of [...moduleList.children]) {
    const name = topLevelModuleName(section);
    const path = section.dataset.path ?? "";
    const isProject =
      name === projectRoot ||
      path.endsWith(`/${projectRoot}.html`) ||
      path.endsWith(`${projectRoot}.html`);

    if (!isProject) section.remove();
  }

  const projectSection = moduleList.querySelector(":scope > details");
  if (projectSection) projectSection.open = true;

  const heading = moduleList.previousElementSibling;
  if (heading?.tagName === "H3") heading.textContent = "Project modules";

  const note = document.createElement("p");
  note.textContent = "Dependency documentation remains available through declaration links and search.";
  note.style.margin = "0.45rem 0 0.85rem";
  note.style.fontSize = "0.78rem";
  note.style.lineHeight = "1.45";
  note.style.color = "var(--muted-text, gray)";
  moduleList.before(note);
}

if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", filterProjectNavigation, { once: true });
} else {
  filterProjectNavigation();
}
