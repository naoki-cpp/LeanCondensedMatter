import { renderLeanMath, renderLeanSourceFallback } from "./lean-math.js";
import { catalogData } from "./catalog-data.js";
import { renderStatement, renderStructuredDefinition } from "./statement-view.js";

const SOURCE_BASE_URL = "https://raw.githubusercontent.com/naoki-cpp/LeanCondensedMatter/main/";
const definitionSourceRequests = new Map();

function element(tag, className = "", text = "") {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text) node.textContent = text;
  return node;
}

function sourceHref(entry) {
  if (entry.sourceUrl) return entry.sourceUrl;
  if (!entry.sourceFile) return null;
  const path = entry.sourceFile.split("/").map(encodeURIComponent).join("/");
  const line = entry.sourceLine ? `#L${entry.sourceLine}` : "";
  return `https://github.com/naoki-cpp/LeanCondensedMatter/blob/main/${path}${line}`;
}

function loadDefinitionSource(sourceFile) {
  if (!definitionSourceRequests.has(sourceFile)) {
    const path = sourceFile.split("/").map(encodeURIComponent).join("/");
    const request = fetch(SOURCE_BASE_URL + path, { cache: "no-store" })
      .then((response) => {
        if (!response.ok) throw new Error("failed to load Lean source: " + response.status);
        return response.text();
      })
      .catch((error) => {
        definitionSourceRequests.delete(sourceFile);
        throw error;
      });
    definitionSourceRequests.set(sourceFile, request);
  }
  return definitionSourceRequests.get(sourceFile);
}

function findDefinitionAssignment(source) {
  let blockCommentDepth = 0;
  let inString = false;
  let escaped = false;
  let nesting = 0;
  for (let index = 0; index < source.length; index += 1) {
    const pair = source.slice(index, index + 2);
    const character = source[index];

    if (blockCommentDepth > 0) {
      if (pair === "/-") {
        blockCommentDepth += 1;
        index += 1;
      } else if (pair === "-/") {
        blockCommentDepth -= 1;
        index += 1;
      }
      continue;
    }
    if (inString) {
      if (escaped) escaped = false;
      else if (character === "\\") escaped = true;
      else if (character === '"') inString = false;
      continue;
    }
    if (pair === "--") {
      const lineEnd = source.indexOf("\n", index + 2);
      if (lineEnd < 0) return -1;
      index = lineEnd;
      continue;
    }
    if (pair === "/-") {
      blockCommentDepth = 1;
      index += 1;
      continue;
    }
    if (character === '"') {
      inString = true;
      continue;
    }
    if (character === "(" || character === "[" || character === "{") nesting += 1;
    else if (character === ")" || character === "]" || character === "}") nesting = Math.max(0, nesting - 1);
    else if (nesting === 0 && pair === ":=") return index + 2;
  }
  return -1;
}

function extractDefinitionBody(source) {
  const assignmentEnd = findDefinitionAssignment(source);
  if (assignmentEnd < 0) return null;
  if (/^\s*\|/mu.test(source.slice(0, assignmentEnd))) return null;
  const body = source.slice(assignmentEnd).trim();
  return body || null;
}

function declarationSourceRange(entry, source) {
  const firstLine = entry.declarationStartLine ?? entry.sourceLine;
  const lastLine = entry.sourceEndLine ?? firstLine;
  if (!Number.isInteger(firstLine) || firstLine < 1 || !Number.isInteger(lastLine) || lastLine < firstLine) return null;
  const lines = source.split(/\r?\n/u);
  return lines.slice(firstLine - 1, lastLine).join("\n");
}

function definitionBody(entry) {
  if (entry.kind !== "def" && entry.kind !== "abbrev") return;
  const firstSourceLine = entry.declarationStartLine ?? entry.sourceLine;
  const hasStructuredBody = typeof entry.structuredStatement?.definitionBody?.text === "string";
  const hasSourceRange = entry.sourceFile && Number.isInteger(firstSourceLine) && Number.isInteger(entry.sourceEndLine);
  if (!hasStructuredBody && !hasSourceRange) return;

  const disclosure = element("details", "definition-body");
  const summary = element("summary", "", "Definition body");
  const content = element("div", "definition-body-content");
  content.setAttribute("aria-live", "polite");
  disclosure.append(summary, content);
  disclosure.addEventListener("toggle", async () => {
    if (!disclosure.open || disclosure.dataset.state === "loading" || disclosure.dataset.state === "loaded") return;
    disclosure.dataset.state = "loading";
    content.textContent = "Loading definition body…";
    try {
      content.replaceChildren();
      if (renderStructuredDefinition(content, entry)) {
        disclosure.dataset.state = "loaded";
        return;
      }
      if (!hasSourceRange) throw new Error("definition source range is unavailable");
      content.textContent = "Loading definition body…";
      const source = await loadDefinitionSource(entry.sourceFile);
      const sourceRange = declarationSourceRange(entry, source);
      if (!sourceRange) throw new Error("definition source range is unavailable");
      const body = extractDefinitionBody(sourceRange);
      if (!content.isConnected) return;
      disclosure.dataset.state = "loaded";
      content.replaceChildren();
      if (body) renderLeanMath(content, body);
      else renderLeanSourceFallback(content, sourceRange, "This definition uses Lean syntax that cannot be isolated as a formula.");
    } catch (error) {
      if (!content.isConnected) return;
      disclosure.dataset.state = "";
      content.replaceChildren(element("p", "error-message", "Definition source could not be loaded."));
      console.error(error);
    }
  });
  return disclosure;
}

export function declarationSourceLink(entry) {
  const href = sourceHref(entry);
  if (!href) return null;
  const link = element("a", "source-link", "View source");
  link.href = href;
  link.target = "_blank";
  link.rel = "noreferrer";
  return link;
}

export function declarationStatement(entry) {
  function render(resolved) {
    const statement = element("div", "math-presentation");
    renderStatement(statement, resolved);
    const body = definitionBody(resolved);
    return body ? [statement, body] : [statement];
  }
  if (!catalogData.hasDeferredStatement(entry)) return render(entry);

  // Both maps use this isolated container. A late response can update only its
  // original selection, never the details of a subsequently selected declaration.
  const container = element("div", "declaration-statement");
  container.setAttribute("aria-busy", "true");
  container.append(element("p", "muted", "Loading structured statement…"));
  catalogData.statement(entry).then((structuredStatement) => {
    container.replaceChildren(...render({ ...entry, structuredStatement }));
  }).catch((error) => {
    console.error(error);
    container.replaceChildren(
      element("p", "math-fallback-note",
        "Structured statement unavailable. Showing the original statement; reload the page to refresh catalog data."),
      ...render(entry));
  }).finally(() => container.removeAttribute("aria-busy"));
  return [container];
}

export function declarationRelations(names, isAvailable) {
  const entries = [...new Set(names ?? [])].map((name) => ({ name, available: isAvailable(name) }));
  return { entries, availableCount: entries.filter((entry) => entry.available).length };
}
