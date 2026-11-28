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
function constantHead(node) {
  const fn = node?.kind === "app" ? node.fn : node;
  return fn?.kind === "const" ? fn.name : undefined;
}

// A semilinear self-map is not necessarily a complex-linear operator.
// Require the actual RingHom.id Complex and the same Hilbert-space variable.
function variableRoles(bindings, hilbertSpaces) {
  const roles = new Map();
  for (const binder of bindings) {
    if (binder.role !== "variable") continue;
    const name = constantHead(binder.type);
    const args = argumentsOf(binder.type);
    if (args.length === 0 && (name === "Real" || name === "Complex")) {
      roles.set(binder.id, { kind: "scalar", field: name });
    } else if (args.length === 1 && ["QuantumTheory.Observable", "QuantumTheory.DensityOperator", "QuantumTheory.StateVector"].includes(name)) {
      roles.set(binder.id, { kind: name === "QuantumTheory.StateVector" ? "ket" : "operator-wrapper",
        wrapper: name, space: args[0]?.kind === "var" ? args[0].id : undefined });
    } else if (binder.type.kind === "var" && hilbertSpaces.has(binder.type.id)) {
      roles.set(binder.id, { kind: "hilbert-vector", space: binder.type.id });
    } else if (["LinearMap", "ContinuousLinearMap"].includes(name) && args.length === 3 &&
        constantHead(args[0]) === "RingHom.id" && argumentsOf(args[0]).length === 1 &&
        constantHead(argumentsOf(args[0])[0]) === "Complex" &&
        args[1]?.kind === "var" && isVar(args[2], args[1].id) &&
        hilbertSpaces.has(args[1].id)) {
      roles.set(binder.id, { kind: "operator", space: args[1].id, map: name });
    }
  }
  return roles;
}

function roleOf(node, roles) { return node?.kind === "var" ? roles.get(node.id) : undefined; }

function styledVariable(node, roles) {
  const tex = identifier(node.name);
  if (tex === null) return null;
  const kind = roleOf(node, roles)?.kind;
  if (kind === "operator" || kind === "operator-wrapper") return "\\hat{" + tex + "}";
  if (kind === "ket" || kind === "hilbert-vector") return "\\left|" + tex + "\\right\\rangle";
  return tex;
}

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
function operatorNotation(node, args, depth, roles) {
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
    const left = roleOf(node.args[0], roles);
    const right = roleOf(node.args[1], roles);
    const sameOperators = left?.kind === "operator" && right?.kind === "operator" &&
      left.space === right.space && left.map === right.map;
    if (name === "HMul.hMul" && sameOperators && node.resultType === left.map) {
      return x + "\\," + y;
    }
    if ((name === "HSMul.hSMul" || name === "SMul.smul") && left?.kind === "scalar" &&
        left.field === "Complex" && right?.kind === "operator" && node.resultType === right.map) {
      return x + "\\," + y;
    }
    if (name === "QuantumTheory.expValue") {
      if (left?.wrapper === "QuantumTheory.Observable" && right?.kind === "ket" &&
          left.space !== undefined && left.space === right.space) {
        const psi = identifier(node.args[1].name);
        return "\\left\\langle " + psi + "\\middle|" + args[0] + "\\middle|" + psi + "\\right\\rangle";
      }
    }
    // Both operands must be known from the statement telescope. A wrapped
    // normalized state is not interchangeable with an unwrapped Hilbert vector.
    if (["DFunLike.coe", "FunLike.coe", "LinearMap.toFun", "ContinuousLinearMap.toFun"].includes(name) &&
        left?.kind === "operator" && right?.kind === "hilbert-vector" && left.space === right.space) {
      return x + "\\," + y;
    }
    if (name === "Inner.inner" && node.resultType === "Complex" &&
        left?.kind === "hilbert-vector" && right?.kind === "hilbert-vector" && left.space === right.space) {
      return "\\left\\langle " + identifier(node.args[0].name) + "\\middle|" +
        identifier(node.args[1].name) + "\\right\\rangle";
    }
    switch (name) {
      case "Bracket.bracket": return "\\left[" + x + ", " + y + "\\right]";
      case "Inner.inner":
        return "\\left\\langle " + x + ", " + y + "\\right\\rangle" +
          (SYMBOLS.has(node.resultType) ? "_{" + SYMBOLS.get(node.resultType) + "}" : "");
      case "HSMul.hSMul":
      case "SMul.smul": return group(x) + "\\,\\bullet\\," + group(y);
      case "Function.comp":
      case "LinearMap.comp":
      case "ContinuousLinearMap.comp": return group(x) + "\\circ " + group(y);
      case "Finset.sum":
      case "Finset.prod": {
        const index = "\\mathsf{i}_{" + depth + "}";
        const symbol = name === "Finset.sum" ? "\\sum" : "\\prod";
        return symbol + "_{" + index + "\\in " + x + "}" + group(group(y) + group(index));
      }
      default: return null;
    }
  }
  // The project uses one fixed-sign bracket for both CAR and CCR. Keep
  // the sign visible unless its identity can be established from the tree.
  if (name === "ScalarExchange.zetaCommutator" && args.length === 3) {
    const sign = node.args[0];
    // Do not guess a numeral from a bare OfNat.ofNat node: the old
    // presentation schema may have omitted its implicit Nat index.
    if (sign.kind === "text" && sign.text === "1") return "\\left[" + args[1] + ", " + args[2] + "\\right]";
    if (sign.kind === "text" && sign.text === "-1") return "\\left\\{" + args[1] + ", " + args[2] + "\\right\\}";
    return "\\left[" + args[1] + ", " + args[2] + "\\right]_{" + args[0] + "}";
  }
  if (name === "InnerProductSpace.rankOne" && args.length === 3 && constantHead(node.args[0]) === "Complex" &&
      roleOf(node.args[1], roles)?.kind === "hilbert-vector" &&
      roleOf(node.args[2], roles)?.kind === "hilbert-vector") {
    return args[1] + "\\left\\langle " + identifier(node.args[2].name) + "\\right|";
  }
  // Mathlib's explicit scalar inner-product notation may retain the scalar argument.
  if (name === "inner" && args.length === 3) {
    const left = roleOf(node.args[1], roles);
    const right = roleOf(node.args[2], roles);
    if (constantHead(node.args[0]) === "Complex" && left?.kind === "hilbert-vector" &&
        right?.kind === "hilbert-vector" && left.space === right.space) {
      return "\\left\\langle " + identifier(node.args[1].name) + "\\middle|" +
        identifier(node.args[2].name) + "\\right\\rangle";
    }
    return "\\left\\langle " + args[1] + ", " + args[2] + "\\right\\rangle_{" + args[0] + "}";
  }
  return null;
}

// A lambda binder is identified by its elaborated free-variable ID, not its name.
// Synthetic names cannot capture Lean identifiers or enclosing synthetic binders.
function lambdaParts(node, labels, depth, bound, roles, prefix = "v") {
  if (node?.kind !== "lambda" || typeof node.binder?.id !== "string" ||
      !node.binder.type || !node.body || bound.has(node.binder.id) || depth > 32) return null;
  const index = "\\mathsf{" + prefix + "}_{" + depth + "}";
  const type = expressionToTex(node.binder.type, labels, depth + 1, bound, roles);
  const scoped = new Map(bound);
  scoped.set(node.binder.id, index);
  const body = expressionToTex(node.body, labels, depth + 1, scoped, roles);
  return type === null || body === null ? null : { index, type, body };
}

function binderNotation(node, labels, depth, bound, roles) {
  if (node.fn?.kind !== "const") return null;
  const name = node.fn.name;
  const finite = name === "Finset.sum" || name === "Finset.prod";
  if (!finite && name !== "tsum") return null;
  if (node.args.length !== (finite ? 2 : 1)) return null;
  const lambda = node.args[finite ? 1 : 0];
  const parts = lambdaParts(lambda, labels, depth, bound, roles, "i");
  if (!parts) return null;
  const domain = finite ? expressionToTex(node.args[0], labels, depth + 1, bound, roles) : parts.type;
  if (domain === null) return null;
  const op = name === "Finset.prod" ? "\\prod" : "\\sum";
  return op + "_{" + parts.index + "\\in " + domain +
    "}\\left(" + parts.body + "\\right)";
}

export function expressionToTex(node, labels = new Map(), depth = 0, bound = new Map(), roles = new Map()) {
  if (!node || depth > 32) return null;
  if (node.kind === "const") return SYMBOLS.get(node.name) ?? identifier(labels.get(node.name) ?? node.name);
  if (node.kind === "var") return bound.get(node.id) ?? styledVariable(node, roles);
  if (node.kind === "sort") return node.isProp ? "\\mathrm{Prop}" : "\\mathrm{Type}";
  // A pretty-printed fallback may mention a binder whose name was replaced.
  // Under a renamed binder, do not silently display such text as a free variable.
  if (node.kind === "text") return bound.size && !/^\d+(?:\.\d+)?$/u.test(node.text)
    ? null : leanPrettyToTex(node.text);
  if (node.kind === "lambda") {
    const parts = lambdaParts(node, labels, depth, bound, roles);
    return parts ? "\\lambda " + parts.index + "\\mathrel{:}" + parts.type + ".\\," + parts.body : null;
  }
  if (node.kind !== "app" || !Array.isArray(node.args)) return null;
  const binderTex = binderNotation(node, labels, depth, bound, roles);
  if (binderTex !== null) return binderTex;
  const args = node.args.map((arg) => expressionToTex(arg, labels, depth + 1, bound, roles));
  if (args.some((arg) => arg === null)) return null;
  const notation = operatorNotation(node, args, depth, roles);
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
  const fn = expressionToTex(node.fn, labels, depth + 1, bound, roles);
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
  const hilbertSpaces = new Set();
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
      hilbertSpaces.add(type.id);
      for (const binder of [type, norm, inner, complete]) covered.add(binder.id);
    }
  }
  const roles = variableRoles(bindings, hilbertSpaces);
  const render = (node) => expressionToTex(node, labels, 0, new Map(), roles);
  const row = (binder) => ({ ...binder, tex: render(binder.type) });
  return {
    settings,
    variables: bindings.filter((binder) => !covered.has(binder.id) && ["type", "variable"].includes(binder.role)).map(row),
    assumptions: bindings.filter((binder) => !covered.has(binder.id) && !["type", "variable"].includes(binder.role)).map(row),
    conclusion: { ...presentation.conclusion, tex: render(presentation.conclusion) },
    fields: (Array.isArray(presentation.fields) ? presentation.fields : []).map(row),
    definitionBody: typeof presentation.definitionBody?.text === "string"
      ? { text: presentation.definitionBody.text, tex: render(presentation.definitionBody) }
      : null,
    symbols: [...labels].filter(([name]) => !SYMBOLS.has(name) && !INFIX.has(name)),
  };
}
