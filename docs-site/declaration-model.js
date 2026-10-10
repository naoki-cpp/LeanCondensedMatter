export const DEFINITION_KINDS = new Set(["def", "abbrev", "opaque"]);

export function declarationAllowed(entry, kind = "*", generated = false) {
  if (!entry || (!generated && entry.generated)) return false;
  return kind === "*" || (kind === "definition"
    ? DEFINITION_KINDS.has(entry.kind) : entry.kind === kind);
}

export function declarationCounts(entries) {
  const source = entries.filter((entry) => !entry.generated);
  return {
    definitions: source.filter((entry) => DEFINITION_KINDS.has(entry.kind)).length,
    theorems: source.filter((entry) => entry.kind === "theorem").length,
    total: source.length,
    generated: entries.length - source.length,
  };
}
