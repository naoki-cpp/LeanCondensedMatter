import { test } from "node:test";
import assert from "node:assert/strict";
import { buildStatementModel, expressionToTex } from "../statement-model.js";
import { renderStatement, renderStructuredDefinition } from "../statement-view.js";

const constant = (name) => ({ kind: "const", name });
const variable = (id, name = id) => ({ kind: "var", id, name });
const app = (name, ...args) => ({ kind: "app", fn: constant(name), args });
const binder = (id, role, type, instanceRoots = []) => ({ id, name: id, role, type, instanceRoots, typeText: id + "-type" });

// A schema fixture for coe_observableExpValue, rather than a regenerated Lean catalog.
function expectationStatement() {
  const H = variable("H");
  const real = app("QuantumTheory.observableExpValue", variable("A"), variable("psi", "ψ"));
  const inclusion = { ...app("Complex.ofReal", real), argumentType: "Real", resultType: "Complex" };
  return { version: 1, fields: [], binders: [
    binder("H", "type", { kind: "sort", isProp: false }),
    binder("norm", "instance", app("NormedAddCommGroup", H)),
    binder("inner", "instance", app("InnerProductSpace", constant("Complex"), H), ["norm"]),
    binder("complete", "instance", app("CompleteSpace", H), ["norm"]),
    binder("A", "variable", app("QuantumTheory.Observable", H)),
    { ...binder("psi", "variable", app("QuantumTheory.StateVector", H)), name: "ψ" },
  ], conclusion: { ...app("Eq", inclusion, app("QuantumTheory.expValue", variable("A"), variable("psi", "ψ"))),
    text: "↑(QuantumTheory.observableExpValue A ψ) = QuantumTheory.expValue A ψ" } };
}

test("typed expectation statement separates a compatible Hilbert setting and variables", () => {
  const model = buildStatementModel(expectationStatement());
  assert.deepEqual(model.settings.map((item) => [item.name, item.text]), [["H", "complex Hilbert space"]]);
  assert.deepEqual(model.variables.map((item) => item.name), ["A", "ψ"]);
  assert.equal(model.assumptions.length, 0);
  assert.equal(model.settings[0].evidence.length, 3);
  assert.match(model.conclusion.tex, /\\iota_\{\\mathbb\{R\}\\hookrightarrow\\mathbb\{C\}\}/);
  assert.match(model.conclusion.tex, /observableExpValue/);
  assert.doesNotMatch(model.conclusion.tex, /QuantumTheory/);
  assert.ok(model.symbols.some(([full]) => full === "QuantumTheory.observableExpValue"));
});

test("missing completeness, another scalar, or unrelated norms never produce a Hilbert summary", () => {
  for (const change of [
    (data) => { data.binders = data.binders.filter((item) => item.id !== "complete"); },
    (data) => { data.binders[2].type.args[0] = constant("Real"); },
    (data) => { data.binders[3].instanceRoots = ["anotherNorm"]; },
    (data) => { data.binders[3].instanceRoots = []; data.binders[3].dependencies = ["norm"]; },
  ]) {
    const data = expectationStatement();
    change(data);
    const model = buildStatementModel(data);
    assert.equal(model.settings.length, 0);
    assert.ok(model.variables.some((item) => item.id === "H"));
    assert.equal(model.assumptions.length, data.binders.filter((item) => item.role === "instance").length);
  }
});

test("unrecognized class and proposition assumptions remain visible", () => {
  const data = expectationStatement();
  data.binders.push(binder("extra", "instance", app("CustomPhysicalCondition", variable("H"))));
  data.binders.push(binder("h", "assumption", app("Eq", variable("A"), variable("B"))));
  assert.deepEqual(buildStatementModel(data).assumptions.map((item) => item.id), ["extra", "h"]);
});

test("coercion rendering requires both recognized identity and actual source/target types", () => {
  assert.match(expressionToTex({ ...app("Complex.ofReal", variable("x")), argumentType: "Real", resultType: "Complex" }), /\\iota/);
  for (const node of [app("Complex.ofReal", variable("x")),
    { ...app("Coe.coe", variable("x")), argumentType: "Real", resultType: "Complex" },
    { ...app("Custom.cast", variable("x")), argumentType: "Real", resultType: "Complex" },
    { ...app("Coe.coe", variable("x")), argumentType: "Nat", resultType: "Complex" }]) {
    assert.doesNotMatch(expressionToTex(node), /\\iota/);
  }
});

test("colliding constants and variable names remain distinguishable", () => {
  const data = expectationStatement();
  data.conclusion = app("Eq", app("First.A", constant("First.value")), app("Second.value", variable("A")));
  const model = buildStatementModel(data);
  assert.match(model.conclusion.tex, /First\.A/);
  assert.match(model.conclusion.tex, /First\.value/);
  assert.match(model.conclusion.tex, /Second\.value/);
});

test("unsupported and future data use fallback, and powers group their entire exponent", () => {
  assert.equal(buildStatementModel(undefined), null);
  assert.equal(buildStatementModel({ ...expectationStatement(), version: 2 }), null);
  assert.equal(buildStatementModel({ ...expectationStatement(), fields: [null] }), null);
  assert.equal(expressionToTex({ kind: "text", text: "match x with | _ => 1" }), null);
  assert.match(expressionToTex(app("HPow.hPow", variable("x"), { kind: "text", text: "10" })), /\^\{10\}/);
});

class Element {
  constructor(tag) { this.tag = tag; this.children = []; this.textContent = ""; this.isConnected = true; this.classList = { add() {} }; }
  append(...children) { this.children.push(...children); }
  replaceChildren(...children) { this.children = children; this.textContent = ""; }
  setAttribute() {}
  text() { return this.textContent + this.children.map((child) => child.text?.() ?? child).join(" "); }
}

test("detail rendering includes fields, unsupported field source, and the complete original statement", async () => {
  globalThis.document = { createElement: (tag) => new Element(tag) };
  const data = expectationStatement();
  data.fields = [{ name: "vertices", type: constant("Nat"), typeText: "Nat" },
    { name: "condition", type: { kind: "unknown" }, typeText: "unsupported field type" }];
  const container = new Element("div");
  renderStatement(container, { kind: "inductive", statement: "original universe and instance arguments", structuredStatement: data });
  await Promise.resolve();
  const text = container.text();
  for (const expected of ["Setting", "Variables", "Result type", "Structure fields", "vertices", "condition",
    "Nat", "unsupported field type", "Underlying typeclass assumptions", "original universe and instance arguments",
    data.conclusion.text]) {
    assert.ok(text.includes(expected), expected);
  }
});


test("recognized operator applications use mathematical notation without reordering arguments", () => {
  const x = variable("x");
  const y = variable("y");
  const G = variable("G");
  const tex = (name, ...args) => expressionToTex(app(name, ...args));
  assert.equal(tex("Matrix.trace", G), String.raw`\operatorname{Tr}\left(\mathrm{G}\right)`);
  assert.equal(tex("ContinuousLinearMap.adjoint", G), String.raw`\left(\mathrm{G}\right)^{\dagger}`);
  assert.equal(tex("Star.star", G), String.raw`\left(\mathrm{G}\right)^{\star}`);
  assert.equal(tex("Norm.norm", x), String.raw`\left\lVert \mathrm{x}\right\rVert`);
  assert.equal(tex("NormedSpace.exp", G), String.raw`\exp\left(\mathrm{G}\right)`);
  assert.equal(expressionToTex({ ...app("Inner.inner", x, y), resultType: "Complex" }),
    String.raw`\left\langle \mathrm{x}, \mathrm{y}\right\rangle_{\mathbb{C}}`);
  assert.equal(tex("Function.comp", x, y), String.raw`\left(\mathrm{x}\right)\circ \left(\mathrm{y}\right)`);
  assert.match(tex("HSMul.hSMul", x, G), /\\bullet/);
});

test("finite sums, products, and total infinite sums retain the function and domain", () => {
  const S = variable("S");
  const f = variable("f");
  const i = String.raw`\mathsf{i}_{0}`;
  const sum = expressionToTex(app("Finset.sum", S, f));
  assert.equal(sum, "\\sum_{" + i + "\\in \\mathrm{S}}\\left(\\left(\\mathrm{f}\\right)\\left(" + i + "\\right)\\right)");
  assert.equal(expressionToTex(app("Finset.prod", S, f)), sum.replace("\\sum", "\\prod"));
  assert.equal(expressionToTex(app("tsum", f)), sum.replace("\\in \\mathrm{S}", ""));
  const nested = expressionToTex(app("Finset.sum", S, app("Finset.prod", S, f)));
  assert.ok(nested.includes(String.raw`\mathsf{i}_{1}`));
});

test("unknown names, mismatched arities and unsupported operands do not receive special notation", () => {
  const x = variable("x");
  const y = variable("y");
  assert.doesNotMatch(expressionToTex(app("Custom.trace", x)), /\\operatorname\{Tr\}/);
  assert.doesNotMatch(expressionToTex(app("Matrix.trace", x, y)), /\\operatorname\{Tr\}/);
  assert.doesNotMatch(expressionToTex(app("Custom.sum", x, y)), /\\sum_/);
  assert.doesNotMatch(expressionToTex({ kind: "app", fn: variable("f", "Matrix.trace"), args: [x] }), /\\operatorname\{Tr\}/);
  assert.equal(expressionToTex(app("Finset.sum", x, { kind: "text", text: "match x with | _ => 1" })), null);
});

const lambda = (id, type, body) => ({ kind: "lambda", binder: { id, name: id, type }, body });

test("structured lambda and sum binders use variable identity rather than printed names", () => {
  const outer = variable("outer", "x");
  const inner = variable("inner", "x");
  const body = app("HAdd.hAdd", outer, inner);
  const sum = app("Finset.sum", variable("S"), lambda("inner", constant("Nat"), body));
  const tex = expressionToTex(sum);
  assert.match(tex, /\\sum_\{\\mathsf\{i\}_\{0\}\\in \\mathrm\{S\}\}/);
  assert.match(tex, /\\left\(\\mathrm\{x\}\\right\) \+ \\left\(\\mathsf\{i\}_\{0\}\\right\)/);
  const nested = app("tsum", lambda("outer", constant("Nat"), sum));
  const nestedTex = expressionToTex(nested);
  assert.match(nestedTex, /\\mathsf\{i\}_\{0\}\\in \\mathbb\{N\}/);
  assert.match(nestedTex, /\\mathsf\{i\}_\{1\}/);
  assert.match(nestedTex, /\\left\(\\mathsf\{i\}_\{0\}\\right\) \+ \\left\(\\mathsf\{i\}_\{1\}\\right\)/);
  assert.match(expressionToTex(lambda("inner", constant("Nat"), inner)), /\\lambda \\mathsf\{v\}_\{0\}/);
});

test("opaque text beneath renamed binders falls back rather than capturing variables", () => {
  assert.equal(expressionToTex(app("tsum", lambda("i", constant("Nat"), { kind: "text", text: "f i" }))), null);
  assert.equal(expressionToTex({ kind: "lambda", binder: { id: "i" }, body: variable("i") }), null);
  assert.match(expressionToTex(app("tsum", lambda("i", constant("Nat"), { kind: "text", text: "1" }))), /1/);
});

test("definition body shares the statement symbol labels and retains its exact Lean text", async () => {
  const data = expectationStatement();
  data.definitionBody = { ...app("Second.observableExpValue", variable("A")), text: "Second.observableExpValue A" };
  const model = buildStatementModel(data);
  assert.match(model.definitionBody.tex, /Second\.observableExpValue/);
  assert.match(model.conclusion.tex, /QuantumTheory\.observableExpValue/);
  assert.equal(model.definitionBody.text, "Second.observableExpValue A");
  globalThis.document = { createElement: (tag) => new Element(tag) };
  const container = new Element("div");
  assert.equal(renderStructuredDefinition(container, { kind: "def", structuredStatement: data }), true);
  await Promise.resolve();
  assert.ok(container.text().includes(data.definitionBody.text));
  for (const kind of ["opaque", "theorem", "axiom", "inductive"]) {
    assert.equal(renderStructuredDefinition(new Element("div"), { kind, structuredStatement: data }), false);
  }
  delete data.definitionBody;
  assert.equal(renderStructuredDefinition(new Element("div"), { kind: "def", structuredStatement: data }), false);
  assert.equal(renderStructuredDefinition(new Element("div"), { kind: "abbrev", structuredStatement: { ...data, version: 2 } }), false);
});


test("operator hats require a complex-linear endomorphism on the recognized Hilbert space", () => {
  const data = expectationStatement();
  const H = variable("H");
  const K = variable("K");
  const id = app("RingHom.id", constant("Complex"));
  const operator = app("ContinuousLinearMap", id, H, H);
  data.binders.push(
    binder("B", "variable", operator),
    binder("C", "variable", operator),
    binder("L", "variable", app("LinearMap", id, H, H)),
    binder("F", "variable", app("ContinuousLinearMap", id, H, K)),
    binder("T", "variable", app("ContinuousLinearMap", constant("Complex.conjAe"), H, H)),
    binder("R", "variable", app("ContinuousLinearMap", app("RingHom.id", constant("Real")), H, H)),
    binder("M", "variable", app("Matrix", H, H, constant("Complex"))),
    binder("G", "variable", H),
  );
  const render = (node) => buildStatementModel({ ...data, conclusion: node }).conclusion.tex;
  for (const name of ["B", "C", "L", "A"]) assert.match(render(variable(name)), /\\hat\{/);
  for (const name of ["F", "T", "R", "M", "G"]) assert.doesNotMatch(render(variable(name)), /\\hat\{/);
  assert.match(render(variable("psi", "ψ")), /\\left\|\\psi\\right\\rangle/);
  const product = { ...app("HMul.hMul", variable("B"), variable("C")), resultType: "ContinuousLinearMap" };
  assert.equal(render(product), "\\hat{\\mathrm{B}}\\,\\hat{\\mathrm{C}}");
  assert.match(render({ ...product, resultType: "Complex" }), /\\cdot/);
  assert.match(render(app("HMul.hMul", variable("F"), variable("C"))), /\\cdot/);
  data.binders = data.binders.filter((item) => item.id !== "complete");
  assert.doesNotMatch(render(variable("B")), /\\hat\{/);
});

test("typed scalar action and quantum wrappers preserve conservative notation", () => {
  const data = expectationStatement();
  const H = variable("H");
  data.binders.push(
    binder("B", "variable", app("LinearMap", app("RingHom.id", constant("Complex")), H, H)),
    binder("z", "variable", constant("Complex")),
    binder("r", "variable", constant("Real")),
    binder("rho", "variable", app("QuantumTheory.DensityOperator", H)),
    binder("fake", "variable", { kind: "app", fn: variable("custom", "QuantumTheory.Observable"), args: [H] }),
  );
  const render = (node) => buildStatementModel({ ...data, conclusion: node }).conclusion.tex;
  const scale = (id) => ({ ...app("HSMul.hSMul", variable(id), variable("B")), resultType: "LinearMap" });
  assert.equal(render(scale("z")), "\\mathrm{z}\\,\\hat{\\mathrm{B}}");
  assert.match(render(scale("r")), /\\bullet/);
  assert.match(render({ ...scale("z"), resultType: "Real" }), /\\bullet/);
  assert.match(render(variable("rho")), /\\hat\{/);
  assert.doesNotMatch(render(variable("fake")), /\\hat\{/);
  assert.match(render(app("Star.star", variable("B"))), /\^\{\\star\}/);
  assert.match(render(app("ContinuousLinearMap.adjoint", variable("B"))), /\^\{\\dagger\}/);
  assert.doesNotMatch(expressionToTex(variable("B")), /\\hat\{/);
});


test("operator application and Dirac notation require matching typed operands", () => {
  const data = expectationStatement();
  const H = variable("H");
  data.binders.push(
    binder("B", "variable", app("ContinuousLinearMap", app("RingHom.id", constant("Complex")), H, H)),
    binder("u", "variable", H),
    binder("v", "variable", H),
    binder("f", "variable", { kind: "text", text: "H → H" }),
  );
  const render = (node) => buildStatementModel({ ...data, conclusion: node }).conclusion.tex;
  const B = variable("B");
  const u = variable("u");
  const v = variable("v");
  assert.equal(render(app("DFunLike.coe", B, v)), "\\hat{\\mathrm{B}}\\,\\left|\\mathrm{v}\\right\\rangle");
  assert.match(render(app("DFunLike.coe", B, variable("psi", "ψ"))), /coe/);
  assert.match(render(app("DFunLike.coe", variable("f"), v)), /coe/);
  assert.match(render(app("Custom.coe", B, v)), /coe/);
  assert.equal(render({ ...app("Inner.inner", u, v), resultType: "Complex" }),
    "\\left\\langle \\mathrm{u}\\middle|\\mathrm{v}\\right\\rangle");
  assert.equal(render(app("InnerProductSpace.rankOne", constant("Complex"), u, v)),
    "\\left|\\mathrm{u}\\right\\rangle\\left\\langle \\mathrm{v}\\right|");
  assert.match(render(app("InnerProductSpace.rankOne", constant("Real"), u, v)), /rankOne/);
  assert.equal(render(app("QuantumTheory.expValue", variable("A"), variable("psi", "ψ"))),
    "\\left\\langle \\psi\\middle|\\hat{\\mathrm{A}}\\middle|\\psi\\right\\rangle");
  assert.match(render(app("QuantumTheory.observableExpValue", variable("A"), variable("psi", "ψ"))), /observableExpValue/);
});

test("exchange brackets preserve sign, order and distinction from general brackets", () => {
  const a = variable("A");
  const b = variable("B");
  const text = (text) => ({ kind: "text", text });
  const render = (sign) => expressionToTex(app("ScalarExchange.zetaCommutator", sign, a, b));
  assert.equal(render(text("1")), "\\left[\\mathrm{A}, \\mathrm{B}\\right]");
  assert.equal(render(text("-1")), "\\left\\{\\mathrm{A}, \\mathrm{B}\\right\\}");
  assert.equal(render(variable("ζ")), "\\left[\\mathrm{A}, \\mathrm{B}\\right]_{\\zeta}");
  assert.match(render(app("OfNat.ofNat")), /ofNat/);
  assert.equal(expressionToTex(app("Bracket.bracket", a, b)), "\\left[\\mathrm{A}, \\mathrm{B}\\right]");
  assert.match(expressionToTex(app("Custom.zetaCommutator", text("-1"), a, b)), /zetaCommutator/);
});


test("compound endomorphisms preserve grouping, order and the common Hilbert space", () => {
  const data = expectationStatement();
  const H = variable("H");
  const K = variable("K");
  const type = (space, map = "ContinuousLinearMap") => app(map, app("RingHom.id", constant("Complex")), space, space);
  data.binders.push(...["B", "C", "D"].map((id) => binder(id, "variable", type(H))),
    binder("L", "variable", type(H, "LinearMap")),
    binder("F", "variable", type(K)), binder("u", "variable", H), binder("v", "variable", H),
    binder("z", "variable", constant("Complex")));
  const [B, C, D, L, F, u, v, z] = ["B", "C", "D", "L", "F", "u", "v", "z"].map((id) => variable(id));
  const op = (name, ...args) => ({ ...app(name, ...args), resultType: "ContinuousLinearMap" });
  const mul = (a, b) => op("HMul.hMul", a, b);
  const add = (a, b) => op("HAdd.hAdd", a, b);
  const apply = (a, b) => app("DFunLike.coe", a, b);
  const render = (node) => buildStatementModel({ ...data, conclusion: node }).conclusion.tex;
  const hat = (s) => "\\hat{\\mathrm{" + s + "}}";
  assert.equal(render(mul(mul(B, C), D)), [B, C, D].map((x) => hat(x.name)).join("\\,"));
  assert.equal(render(mul(B, mul(D, C))), [B, D, C].map((x) => hat(x.name)).join("\\,"));
  assert.match(render(mul(add(B, C), D)), /\\right\)\\,\\hat\{\\mathrm\{D\}\}/);
  assert.match(render(apply(add(B, C), v)), /\\right\)\\,\\left\|\\mathrm\{v\}/);
  assert.match(render(apply(op("ContinuousLinearMap.adjoint", B), v)), /\^\{\\dagger\}/);
  assert.match(render(apply(op("HSMul.hSMul", z, B), v)), /\\mathrm\{z\}/);
  assert.match(render(mul(mul(B, L), C)), /\\cdot/);
  assert.match(render(mul(mul(B, F), C)), /\\cdot/);
  assert.match(render(mul({ ...mul(B, C), resultType: "Complex" }, D)), /\\cdot/);
  assert.match(render(apply(app("Custom.operator", B), v)), /coe/);
  assert.match(render(app("LinearMap.toFun", B, v)), /toFun/);
  const element = "\\left\\langle \\mathrm{u}\\middle|" + hat("B") + "\\," + hat("C") + "\\middle|\\mathrm{v}\\right\\rangle";
  assert.equal(render({ ...app("Inner.inner", u, apply(mul(B, C), v)), resultType: "Complex" }), element);
  assert.equal(render(app("inner", constant("Complex"), u, apply(mul(B, C), v))), element);
  assert.match(render({ ...app("Inner.inner", apply(B, u), apply(C, v)), resultType: "Complex" }), /\\right\\rangle/);
  assert.doesNotMatch(render({ ...app("Inner.inner", u, apply(F, v)), resultType: "Complex" }), /\\middle\|/);
});
