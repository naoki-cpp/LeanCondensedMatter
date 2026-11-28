import { test } from "node:test";
import assert from "node:assert/strict";
import { declarationAllowed, declarationCounts } from "../declaration-model.js";
import { createModuleOverview } from "../module-overview.js";
import { declarationRelations, declarationStatement } from "../declaration-details.js";
import { createDeclarationVisibility } from "../declaration-visibility.js";

test("definition filter and generated declarations", () => {
  for (const kind of ["def", "abbrev", "opaque"]) {
    assert.equal(declarationAllowed({ kind }, "definition"), true);
  }
  assert.equal(declarationAllowed({ kind: "theorem" }, "definition"), false);
  assert.equal(declarationAllowed({ kind: "def", generated: true }), false);
  assert.equal(declarationAllowed({ kind: "def", generated: true }, "*", true), true);
  assert.deepEqual(declarationCounts([
    { kind: "def" }, { kind: "def" }, { kind: "theorem", generated: true },
  ]), { definitions: 2, theorems: 0, proved: 0, missingAxiomData: 0, total: 2, generated: 1 });
  assert.deepEqual(declarationCounts([
    { kind: "theorem" }, { kind: "theorem", axioms: [] }, { kind: "theorem", axioms: ["sorryAx"] },
  ]), { definitions: 0, theorems: 3, proved: 1, missingAxiomData: 1, total: 3, generated: 0 });
});

class Element {
  constructor(tag) {
    this.tag = tag;
    this.children = [];
    this.textContent = "";
    this.style = {};
    this.dataset = {};
    this.classList = { add() {} };
  }
  getContext() { return null; }
  append(...children) { this.children.push(...children); }
  prepend(...children) { this.children.unshift(...children); }
  replaceChildren(...children) { this.children = children; }
  setAttribute() {}
  addEventListener(event, callback) { this[event] = callback; }
  text() { return this.textContent + this.children.map((child) => child.text?.() ?? child).join(" "); }
  find(tag) { return this.children.flatMap((child) => typeof child === "object"
    ? [...(child.tag === tag ? [child] : []), ...child.find(tag)] : []); }
}

test("shared declaration detail counts distinct relations and keeps opaque bodies hidden", () => {
  globalThis.document = { createElement: (tag) => new Element(tag), createTextNode: (text) => text };
  const entry = { name: "example", sourceFile: "Example.lean", sourceLine: 1, sourceEndLine: 2, statement: "Nat" };
  assert.deepEqual(declarationRelations(["a", "b", "a"], (name) => name === "a"), {
    entries: [{ name: "a", available: true }, { name: "b", available: false }], availableCount: 1,
  });
  assert.equal(declarationStatement({ ...entry, kind: "opaque" }).length, 1);
  assert.equal(declarationStatement({ ...entry, kind: "def" }).at(-1).tag, "details");
  const structuredOnly = { kind: "def", statement: "Nat", structuredStatement: { definitionBody: { text: "1" } } };
  assert.equal(declarationStatement(structuredOnly).at(-1).tag, "details");
  assert.equal(declarationStatement({ ...structuredOnly, kind: "opaque" }).length, 1);
});

test("MixedOrderData overview counts and opens both definitions", async () => {
  globalThis.document = { createElement: (tag) => new Element(tag), createTextNode: (text) => text };
  globalThis.window = { devicePixelRatio: 1 };
  globalThis.fetch = async () => ({ ok: true, text: async () => "/-! # Mixed order data -/" });
  const overview = new Element("div");
  const names = ["componentMixedPosition", "componentMixedPositionEquiv"];
  let opened;
  const explorer = createModuleOverview({
    catalog: names.map((name) => ({ name, module: "LeanCondensedMatter.MixedOrderData",
      kind: "def", generated: false, statement: "Nat", dependencies: [],
      dependents: name === names[1] ? [names[0]] : [] })),
    onOpenDeclaration(name) { opened = name; },
  });
  overview.replaceChildren(...(await explorer.prepare("MixedOrderData"))().nodes);
  assert.match(overview.text(), /Definitions 2/);
  assert.match(overview.text(), /Theorems 0/);
  assert.match(overview.text(), /Total 2/);
  assert.equal(overview.find("h2").find((heading) => heading.id === "research-map-title")?.text(), "Mixed Order Data");
  assert.equal(overview.find("canvas").length, 1);
  assert.doesNotMatch(overview.text(), /Direct submodules|Module details/);
  overview.replaceChildren(...(await explorer.prepare("LeanCondensedMatter"))().nodes);
  const mapTitle = overview.find("h2").find((heading) => heading.id === "research-map-title");
  assert.equal(mapTitle?.text(), "LeanCondensedMatter");
  const region = overview.find("button").find((button) => button.className === "research-map-region");
  assert.equal(region.text(), "Mixed Order Data");
  assert.equal(overview.find("p").find((item) => item.className === "research-map-declaration-count")?.text(), "2 definitions · 0 proved theorems");
  region.click();
  assert.equal(mapTitle?.text(), "Mixed Order Data");
  assert.equal(overview.find("canvas").length, 1);
  const canvas = overview.find("canvas")[0];
  const hover = overview.find("div").find((item) => item.className === "research-map-hover");
  canvas.getBoundingClientRect = () => ({ left: 0, top: 0, width: 960, height: 670 });
  canvas.pointermove({ clientX: 480, clientY: 335, pointerType: "mouse", pointerId: 1 });
  assert.equal(hover.hidden, false);
  assert.equal(hover.text(), names[0]);
  canvas.pointerleave();
  assert.equal(hover.hidden, true);
  const picker = overview.find("select")[0];
  picker.value = names[0];
  picker.change();
  assert.match(overview.text(), /Depends on \(0\)/);
  overview.find("button").find((item) => item.text() === "View dependency graph").click();
  assert.equal(opened, names[0]);
  picker.value = names[1];
  picker.change();
  assert.match(overview.text(), /Used by \(1\)/);
  overview.find("button").find((item) => item.text() === names[0]).click();
  assert.equal(overview.find("h3").find((item) => item.className === "research-map-detail-title").text(), names[0]);
  assert.match(overview.text(), /Definitions 2/);
  assert.match(overview.text(), /Theorems 0/);
  assert.match(overview.text(), /Total 2/);
  overview.replaceChildren(...(await explorer.prepare("LeanCondensedMatter", names[1]))().nodes);
  assert.equal(overview.find("select")[0].value, names[1]);
  assert.equal(overview.find("h3").find((item) => item.className === "research-map-detail-title").text(), names[1]);
});

test("map filters points and picker while preserving the total dependency count", async () => {
  globalThis.document = { createElement: (tag) => new Element(tag), createTextNode: (text) => text };
  globalThis.window = { devicePixelRatio: 1 };
  globalThis.fetch = async () => ({ ok: false });
  const overview = new Element("div");
  const module = "LeanCondensedMatter.Example";
  const catalog = [
    { name: "result", kind: "theorem", dependencies: ["definition", "generated"] },
    { name: "definition", kind: "def", dependencies: [] },
    { name: "generated", kind: "theorem", generated: true, axioms: ["sorryAx"], dependencies: [] },
  ].map((entry) => ({ module, statement: "Nat", dependents: [], ...entry }));
  let generated = false;
  const explorer = createModuleOverview({ catalog,
    visibleDeclarations: () => createDeclarationVisibility(catalog, "theorem", generated) });
  overview.replaceChildren(...(await explorer.prepare("LeanCondensedMatter"))().nodes);
  let picker = overview.find("select")[0];
  assert.deepEqual(picker.find("option").map(({ value }) => value), ["", "result"]);
  assert.match(overview.text(), /Definitions 0.*Theorems 1.*Total 1/);
  picker.value = "result";
  picker.change();
  assert.match(overview.text(), /Depends on \(2 total, 0 on map\)/);
  generated = true;
  overview.replaceChildren(...(await explorer.prepare("LeanCondensedMatter"))().nodes);
  picker = overview.find("select")[0];
  assert.deepEqual(picker.find("option").map(({ value }) => value), ["", "generated", "result"]);
  assert.match(overview.text(), /Theorems 2.*Total 2.*Generated 1/);
  assert.match(overview.text(), /0 definitions · 0 proved theorems · 1 theorem without axiom data/);
});
