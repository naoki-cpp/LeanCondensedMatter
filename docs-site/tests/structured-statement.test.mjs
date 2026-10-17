import { test } from "node:test";
import assert from "node:assert/strict";
import { buildStatementModel, expressionToTex } from "../statement-model.js";
import { renderStatement } from "../statement-view.js";

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
