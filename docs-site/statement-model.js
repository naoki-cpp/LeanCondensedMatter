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
    visit(node.binder?.type, depth + 1);
    visit(node.body, depth + 1);
    for (const argument of argumentsOf(node)) visit(argument, depth + 1);
  }
  for (const binder of presentation.binders) visit(binder.type);
  visit(presentation.conclusion);
  visit(presentation.definitionBody);
  for (const field of presentation.fields ?? []) visit(field.type);
  const counts = new Map();
  for (const name of names) {
    const short = name.split(".").at(-1);
    counts.set(short, (counts.get(short) ?? 0) + 1);
  }
  return new Map([...names].map((name) => [name,
    counts.get(name.split(".").at(-1)) === 1 && !variables.has(name.split(".").at(-1)) ? name.split(".").at(-1) : name]));
}

// Render only known fully qualified constants with the expected explicit arity.
// The synthetic index is a display-only bound variable, distinct from Lean identifiers
// (which use \mathrm). Depth distinguishes nested summation indices.
function operatorNotation(node, args, depth) {
  if (node.fn?.kind !== "const") return null;
  const name = node.fn.name;
  const group = (value) => "\\left(" + value + "\\right)";
  if (args.length === 1) {
    const x = args[0];
    switch (name) {
      case "Neg.neg": return "-" + group(x);
      case "Inv.inv": return group(x) + "^{-1}";
      case "Norm.norm": return "\\left\\lVert " + x + "\\right\\rVert";
      case "Star.star": return group(x) + "^{\\star}";
      case "ContinuousLinearMap.adjoint":
      case "Matrix.conjTranspose": return group(x) + "^{\\dagger}";
      case "Matrix.trace": return "\\operatorname{Tr}" + group(x);
      case "NormedSpace.exp":
      case "Real.exp":
      case "Complex.exp": return "\\exp" + group(x);
      case "tsum": {
        const index = "\\mathsf{i}_{" + depth + "}";
        return "\\sum_{" + index + "}" + group(group(x) + group(index));
      }
      default: return null;
    }
  }
  if (args.length === 2) {
    const [x, y] = args;
    switch (name) {
      case "Inner.inner":
        return "\\left\\langle " + x + ", " + y + "\\right\\rangle" +
          (SYMBOLS.has(node.resultType) ? "_{" + SYMBOLS.get(node.resultType) + "}" : "");
      case "HSMul.hSMul":
      case "SMul.smul": return group(x) + "\\,\\bullet\\," + group(y);
      case "Function.comp": return group(x) + "\\circ " + group(y);
      case "Finset.sum":
      case "Finset.prod": {
        const index = "\\mathsf{i}_{" + depth + "}";
        const symbol = name === "Finset.sum" ? "\\sum" : "\\prod";
        return symbol + "_{" + index + "\\in " + x + "}" + group(group(y) + group(index));
      }
      default: return null;
    }
  }
  // Mathlib's explicit scalar inner-product notation may retain the scalar argument.
  if (name === "inner" && args.length === 3) {
    return "\\left\\langle " + args[1] + ", " + args[2] + "\\right\\rangle_{" + args[0] + "}";
  }
  return null;
}

// A lambda binder is identified by its elaborated free-variable ID, not its name.
// Synthetic names cannot capture Lean identifiers or enclosing synthetic binders.
function lambdaParts(node, labels, depth, bound, prefix = "v") {
  if (node?.kind !== "lambda" || typeof node.binder?.id !== "string" ||
      !node.binder.type || !node.body || bound.has(node.binder.id) || depth > 32) return null;
  const index = "\\mathsf{" + prefix + "}_{" + depth + "}";
  const type = expressionToTex(node.binder.type, labels, depth + 1, bound);
  const scoped = new Map(bound);
  scoped.set(node.binder.id, index);
  const body = expressionToTex(node.body, labels, depth + 1, scoped);
  return type === null || body === null ? null : { index, type, body };
}

function binderNotation(node, labels, depth, bound) {
  if (node.fn?.kind !== "const") return null;
  const name = node.fn.name;
  const finite = name === "Finset.sum" || name === "Finset.prod";
  if (!finite && name !== "tsum") return null;
  if (node.args.length !== (finite ? 2 : 1)) return null;
  const lambda = node.args[finite ? 1 : 0];
  const parts = lambdaParts(lambda, labels, depth, bound, "i");
  if (!parts) return null;
  const domain = finite ? expressionToTex(node.args[0], labels, depth + 1, bound) : parts.type;
  if (domain === null) return null;
  const op = name === "Finset.prod" ? "\\prod" : "\\sum";
  return op + "_{" + parts.index + "\\in " + domain +
    "}\\left(" + parts.body + "\\right)";
}

export function expressionToTex(node, labels = new Map(), depth = 0, bound = new Map()) {
  if (!node || depth > 32) return null;
  if (node.kind === "const") return SYMBOLS.get(node.name) ?? identifier(labels.get(node.name) ?? node.name);
  if (node.kind === "var") return bound.get(node.id) ?? identifier(node.name);
  if (node.kind === "sort") return node.isProp ? "\\mathrm{Prop}" : "\\mathrm{Type}";
  // A pretty-printed fallback may mention a binder whose name was replaced.
  // Under a renamed binder, do not silently display such text as a free variable.
  if (node.kind === "text") return bound.size && !/^\d+(?:\.\d+)?$/u.test(node.text)
    ? null : leanPrettyToTex(node.text);
  if (node.kind === "lambda") {
    const parts = lambdaParts(node, labels, depth, bound);
    return parts ? "\\lambda " + parts.index + "\\mathrel{:}" + parts.type + ".\\," + parts.body : null;
  }
  if (node.kind !== "app" || !Array.isArray(node.args)) return null;
  const binderTex = binderNotation(node, labels, depth, bound);
  if (binderTex !== null) return binderTex;
  const args = node.args.map((arg) => expressionToTex(arg, labels, depth + 1, bound));
  if (args.some((arg) => arg === null)) return null;
  const notation = operatorNotation(node, args, depth);
  if (notation !== null) return notation;
  const name = head(node);
  if (INFIX.has(name) && args.length === 2) {
    return "\\left(" + args[0] + "\\right) " + INFIX.get(name) + " \\left(" + args[1] + "\\right)";
  }
  if (name === "Not" && args.length === 1) return "\\lnot\\left(" + args[0] + "\\right)";
  if (name === "HPow.hPow" && args.length === 2) return "\\left(" + args[0] + "\\right)^{" + args[1] + "}";
  if (COERCIONS.has(name) && args.length === 1 && node.argumentType === "Real" && node.resultType === "Complex") {
    return "\\iota_{\\mathbb{R}\\hookrightarrow\\mathbb{C}}\\left(" + args[0] + "\\right)";
  }
  const fn = expressionToTex(node.fn, labels, depth + 1, bound);
  if (fn === null) return null;
  const appliedFn = node.fn.kind === "lambda" ? "\\left(" + fn + "\\right)" : fn;
  return args.length ? appliedFn + "\\left(" + args.join(",\\,") + "\\right)" : fn;
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
    definitionBody: typeof presentation.definitionBody?.text === "string"
      ? { text: presentation.definitionBody.text, tex: expressionToTex(presentation.definitionBody, labels) }
      : null,
    symbols: [...labels].filter(([name]) => !SYMBOLS.has(name) && !INFIX.has(name)),
  };
}
