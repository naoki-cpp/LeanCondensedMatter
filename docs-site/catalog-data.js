const BASE_URL = "https://raw.githubusercontent.com/naoki-cpp/LeanCondensedMatter/graph-data/";

export function createCatalogData(fetchData = (...args) => fetch(...args), base = BASE_URL) {
  let modules = {};
  const requests = new Map();

  async function load() {
    const response = await fetchData(base + "declaration-index.json", { cache: "no-cache" });
    if (response.status === 404) {
      // During deployment the previous graph-data snapshot may still be published.
      const legacy = await fetchData(base + "declarations.json", { cache: "no-cache" });
      if (!legacy.ok) throw new Error("failed to load declaration catalog: " + legacy.status);
      modules = {};
      return legacy.json();
    }
    if (!response.ok) throw new Error("failed to load declaration index: " + response.status);
    const index = await response.json();
    if (index.version !== 1 || !Array.isArray(index.declarations) ||
        !index.modules || typeof index.modules !== "object" || Array.isArray(index.modules)) {
      throw new Error("unsupported declaration index");
    }
    modules = index.modules;
    return index.declarations;
  }

  function shardPath(entry) {
    return Object.hasOwn(modules, entry.module) ? modules[entry.module] : null;
  }

  function hasDeferredStatement(entry) {
    return !Object.hasOwn(entry, "structuredStatement") && Boolean(shardPath(entry));
  }

  async function statement(entry) {
    if (!hasDeferredStatement(entry)) return entry.structuredStatement ?? null;
    const path = shardPath(entry);
    if (!/^declaration-details\/[a-f0-9]{64}\.json$/u.test(path)) {
      throw new Error("invalid declaration detail path");
    }
    if (!requests.has(path)) {
      const request = fetchData(base + path, { cache: "force-cache" })
        .then((response) => {
          if (!response.ok) throw new Error("failed to load declaration details: " + response.status);
          return response.json();
        })
        .then((data) => {
          if (!data || typeof data !== "object" || Array.isArray(data)) {
            throw new Error("invalid declaration details");
          }
          return data;
        })
        .catch((error) => {
          requests.delete(path);
          throw error;
        });
      requests.set(path, request);
    }
    const rows = await requests.get(path);
    return Object.hasOwn(rows, entry.name) ? rows[entry.name] : null;
  }

  return { load, hasDeferredStatement, statement };
}

export const catalogData = createCatalogData();
