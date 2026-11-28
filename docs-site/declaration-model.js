export const DEFINITION_KINDS = new Set(["def", "abbrev", "opaque"]);

export function declarationAllowed(entry, kind = "*", generated = false) {
  if (!entry || (!generated && entry.generated)) return false;
  return kind === "*" || (kind === "definition"
    ? DEFINITION_KINDS.has(entry.kind) : entry.kind === kind);
}

export function declarationCounts(entries, { includeGenerated = false } = {}) {
  const counts = { definitions: 0, theorems: 0, proved: 0, missingAxiomData: 0, total: 0, generated: 0 };
  for (const entry of entries) {
    if (entry.generated) {
      counts.generated += 1;
      if (!includeGenerated) continue;
    }
    counts.total += 1;
    if (DEFINITION_KINDS.has(entry.kind)) counts.definitions += 1;
    if (entry.kind === "theorem") {
      counts.theorems += 1;
      if (!Array.isArray(entry.axioms)) counts.missingAxiomData += 1;
      else if (!entry.axioms.includes("sorryAx")) counts.proved += 1;
    }
  }
  return counts;
}
