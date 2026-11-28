import { buildDeclarationHierarchy } from "./declaration-hierarchy.js";
import { declarationAllowed } from "./declaration-model.js";

export function createDeclarationVisibility(catalog, kind = "*", generated = false) {
  const entries = catalog.filter((entry) => declarationAllowed(entry, kind, generated));
  const byName = new Map(entries.map((entry) => [entry.name, entry]));
  let hierarchy;
  return {
    entries,
    allows(name, module = "*") {
      const entry = byName.get(name);
      return Boolean(entry && (module === "*" || entry.module === module));
    },
    mapHierarchy() {
      return hierarchy ??= buildDeclarationHierarchy(entries);
    },
  };
}
