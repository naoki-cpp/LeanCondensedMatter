export const DEFINITION_KINDS = new Set(["def", "abbrev", "opaque"]);

export function declarationAllowed(entry, kind = "*", generated = false) {
  if (!entry || (!generated && entry.generated)) return false;
  return kind === "*" || (kind === "definition"
    ? DEFINITION_KINDS.has(entry.kind) : entry.kind === kind);
}

export function declarationCounts(entries, { includeGenerated = false } = {}) {
  const generated = entries.filter((entry) => entry.generated).length;
  const source = includeGenerated ? entries : entries.filter((entry) => !entry.generated);
  return {
    definitions: source.filter((entry) => DEFINITION_KINDS.has(entry.kind)).length,
    theorems: source.filter((entry) => entry.kind === "theorem").length,
    total: source.length,
    generated,
  };
}
