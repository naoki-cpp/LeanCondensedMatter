import { PROJECT_NAME } from "./declaration-hierarchy.js";

export function readExplorerLocation(location, navigation, { hasImport, hasDeclaration, hasModule, hasGraphModule, hasImports }) {
  const params = new URLSearchParams(location.search);
  const direction = ["dependencies", "consumers"].includes(params.get("direction")) ? params.get("direction") : "both";
  const imports = params.get("view") === "imports" && hasImports;
  const depth = Number((imports ? params.get("import-depth") : null) ?? params.get("depth"));
  const settings = { direction, depth: [1, 2, 3, 4].includes(depth) ? depth : imports ? 1 : 2 };
  if (imports) {
    const root = params.get("import-module");
    return { ...settings, page: "imports", root, canonicalize: !hasImport(root) };
  }
  const requestedModule = params.get("module");
  const module = requestedModule && hasGraphModule(requestedModule) ? requestedModule : "*";
  let root = location.hash.slice(1);
  try { root = decodeURIComponent(root); }
  catch { /* Keep malformed hashes available for an exact lookup. */ }
  if (hasDeclaration(root)) {
    return { ...settings, page: "theorem", root, module,
      returnBrowse: navigation?.returnBrowse ?? null, returnMap: navigation?.returnMap ?? null };
  }
  const requestedBrowse = params.get("browse");
  const validBrowse = requestedBrowse && hasModule(requestedBrowse);
  return { ...settings, page: "overview",
    browse: validBrowse ? requestedBrowse : module !== "*" && hasModule(module) ? module : PROJECT_NAME,
    mapSelection: navigation?.mapSelection, canonicalize: Boolean(requestedBrowse ? !validBrowse : module !== "*") };
}

export function writeExplorerLocation(href, state, mapSelection = null) {
  const url = new URL(href);
  const imports = state.page === "imports";
  const values = {
    view: imports ? "imports" : null,
    "import-module": imports ? state.root : null,
    "import-depth": imports && state.depth !== 1 ? state.depth : null,
    depth: !imports && state.depth !== 2 ? state.depth : null,
    direction: state.direction === "both" ? null : state.direction,
    module: !imports && state.module !== "*" ? state.module : null,
    browse: !imports && !state.root && state.browse !== PROJECT_NAME ? state.browse : null,
  };
  for (const [key, value] of Object.entries(values)) {
    if (value == null) url.searchParams.delete(key);
    else if (url.searchParams.get(key) !== String(value)) url.searchParams.set(key, value);
  }
  url.hash = imports ? "" : state.root ?? "";
  const navigation = state.page === "theorem" && (state.returnMap || state.returnBrowse)
    ? { returnBrowse: state.returnBrowse, returnMap: state.returnMap }
    : state.page === "overview" && mapSelection ? { mapSelection } : null;
  return { path: url.pathname + url.search + url.hash, navigation };
}
