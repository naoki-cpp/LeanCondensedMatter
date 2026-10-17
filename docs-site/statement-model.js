import { leanPrettyToTex } from "./lean-math.js";

const SYMBOLS = new Map([["Real", "\\mathbb{R}"], ["Complex", "\\mathbb{C}"],
  ["Nat", "\\mathbb{N}"], ["Int", "\\mathbb{Z}"], ["Rat", "\\mathbb{Q}"]]);
const INFIX = new Map([["Eq", "="], ["Iff", "\\iff"], ["And", "\\land"],
  ["Or", "\\lor"], ["HAdd.hAdd", "+"], ["HSub.hSub", "-"],
  ["HMul.hMul", "\\cdot"], ["HDiv.hDiv", "/"], ["LE.le", "\\le"], ["LT.lt", "<"]]);
// A generic Coe instance with these types need not be the canonical inclusion.
const COERCIONS = new Set(["Complex.ofReal"]);

function identifier(name) {
  if (typeof name !== "string" || !name) return null;
  return leanPrettyToTex(name) ?? "\\mathrm{" + name.replace(/[\\{}#$%&_^~]/gu,
    (character) => ({ "\\": "\\backslash{}", "^": "\\textasciicircum{}", "~": "\\textasciitilde{}" }[character] ?? "\\" + character)) + "}";
}

function head(node) { return node?.kind === "app" ? node.fn?.name : node?.name; }
function argumentsOf(node) { return node?.kind === "app" && Array.isArray(node.args) ? node.args : []; }
function isVar(node, id) { return node?.kind === "var" && node.id === id; }

// Full identifiers remain available in the symbol key. Colliding short names stay qualified.
function constantLabels(presentation) {
  const names = new Set();
  const variables = new Set(presentation.binders.map((binder) => binder.name));
  function visit(node, depth = 0) {
    if (!node || typeof node !== "object" || depth > 32) return;
    if (node.kind === "const" && typeof node.name === "string") names.add(node.name);
    if (node.kind === "var") variables.add(node.name);
    visit(node.fn, depth + 1);
    for (const argument of argumentsOf(node)) visit(argument, depth + 1);
  }
  for (const binder of presentation.binders) visit(binder.type);
  visit(presentation.conclusion);
  for (const field of presentation.fields ?? []) visit(field.type);
  const counts = new Map();
  for (const name of names) {
    const short = name.split(".").at(-1);
    counts.set(short, (counts.get(short) ?? 0) + 1);
  }
  return new Map([...names].map((name) => [name,
    counts.get(name.split(".").at(-1)) === 1 && !variables.has(name.split(".").at(-1)) ? name.split(".").at(-1) : name]));
}

export function expressionToTex(node, labels = new Map(), depth = 0) {
  if (!node || depth > 32) return null;
  if (node.kind === "const") return SYMBOLS.get(node.name) ?? identifier(labels.get(node.name) ?? node.name);
  if (node.kind === "var") return identifier(node.name);
  if (node.kind === "sort") return node.isProp ? "\\mathrm{Prop}" : "\\mathrm{Type}";
  if (node.kind === "text") return leanPrettyToTex(node.text);
  if (node.kind !== "app" || !Array.isArray(node.args)) return null;
  const args = node.args.map((arg) => expressionToTex(arg, labels, depth + 1));
  if (args.some((arg) => arg === null)) return null;
  const name = head(node);
  if (INFIX.has(name) && args.length === 2) {
    return "\\left(" + args[0] + "\\right) " + INFIX.get(name) + " \\left(" + args[1] + "\\right)";
  }
  if (name === "Not" && args.length === 1) return "\\lnot\\left(" + args[0] + "\\right)";
  if (name === "HPow.hPow" && args.length === 2) return "\\left(" + args[0] + "\\right)^{" + args[1] + "}";
  if (COERCIONS.has(name) && args.length === 1 && node.argumentType === "Real" && node.resultType === "Complex") {
    return "\\iota_{\\mathbb{R}\\hookrightarrow\\mathbb{C}}\\left(" + args[0] + "\\right)";
  }
  const fn = expressionToTex(node.fn, labels, depth + 1);
  if (fn === null) return null;
  return args.length ? fn + "\\left(" + args.join(",\\,") + "\\right)" : fn;
}

export function buildStatementModel(presentation) {
  if (presentation?.version !== 1 || !Array.isArray(presentation.binders) || !presentation.conclusion ||
      presentation.binders.some((binder) => !binder || typeof binder.id !== "string" || !binder.type) ||
      (presentation.fields !== undefined && (!Array.isArray(presentation.fields) ||
        presentation.fields.some((field) => !field || typeof field.name !== "string" || !field.type)))) return null;
  const labels = constantLabels(presentation);
  const bindings = presentation.binders;
  const covered = new Set();
  const settings = [];
  for (const type of bindings.filter((binder) => binder.role === "type")) {
    const norm = bindings.find((binder) => binder.role === "instance" && head(binder.type) === "NormedAddCommGroup" &&
      argumentsOf(binder.type).length === 1 && isVar(argumentsOf(binder.type)[0], type.id));
    const inner = bindings.find((binder) => binder.role === "instance" && head(binder.type) === "InnerProductSpace" &&
      argumentsOf(binder.type).length === 2 && head(argumentsOf(binder.type)[0]) === "Complex" &&
      isVar(argumentsOf(binder.type)[1], type.id) && binder.instanceRoots?.includes(norm?.id));
    const complete = bindings.find((binder) => binder.role === "instance" && head(binder.type) === "CompleteSpace" &&
      argumentsOf(binder.type).length === 1 && isVar(argumentsOf(binder.type)[0], type.id) &&
      binder.instanceRoots?.includes(norm?.id));
    if (norm && inner && complete) {
      settings.push({ name: type.name, text: "complex Hilbert space", evidence: [norm, inner, complete] });
      for (const binder of [type, norm, inner, complete]) covered.add(binder.id);
    }
  }
  const row = (binder) => ({ ...binder, tex: expressionToTex(binder.type, labels) });
  return {
    settings,
    variables: bindings.filter((binder) => !covered.has(binder.id) && ["type", "variable"].includes(binder.role)).map(row),
    assumptions: bindings.filter((binder) => !covered.has(binder.id) && !["type", "variable"].includes(binder.role)).map(row),
    conclusion: { ...presentation.conclusion, tex: expressionToTex(presentation.conclusion, labels) },
    fields: (Array.isArray(presentation.fields) ? presentation.fields : []).map(row),
    symbols: [...labels].filter(([name]) => !SYMBOLS.has(name) && !INFIX.has(name)),
  };
}
