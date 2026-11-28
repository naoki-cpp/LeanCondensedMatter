import { test } from "node:test";
import assert from "node:assert/strict";
import { declarationAllowed, declarationCounts } from "../declaration-model.js";
import { createModuleOverview } from "../module-overview.js";

test("definition filter and generated declarations", () => {
  for (const kind of ["def", "abbrev", "opaque"]) {
    assert.equal(declarationAllowed({ kind }, "definition"), true);
  }
  assert.equal(declarationAllowed({ kind: "theorem" }, "definition"), false);
  assert.equal(declarationAllowed({ kind: "def", generated: true }), false);
  assert.equal(declarationAllowed({ kind: "def", generated: true }, "*", true), true);
  assert.deepEqual(declarationCounts([
    { kind: "def" }, { kind: "def" }, { kind: "theorem", generated: true },
  ]), { definitions: 2, theorems: 0, proved: 0, total: 2, generated: 1 });
});

class Element {
  constructor(tag) {
    this.tag = tag;
    this.children = [];
    this.textContent = "";
    this.style = {};
    this.classList = { add() {} };
  }
  getContext() { return null; }
  append(...children) { this.children.push(...children); }
  replaceChildren(...children) { this.children = children; }
  setAttribute() {}
  addEventListener(event, callback) { this[event] = callback; }
  text() { return this.textContent + this.children.map((child) => child.text?.() ?? child).join(" "); }
  find(tag) { return this.children.flatMap((child) => typeof child === "object"
    ? [...(child.tag === tag ? [child] : []), ...child.find(tag)] : []); }
}

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
    onBrowse() { assert.fail("The map should open a declaration directly"); },
    onOpenDeclaration(name) { opened = name; },
  });
  overview.replaceChildren(...(await explorer.prepare("MixedOrderData"))());
  assert.match(overview.text(), /Definitions 2/);
  assert.match(overview.text(), /Theorems 0/);
  assert.match(overview.text(), /Total 2/);
  for (const name of names) {
    const card = overview.find("button").find((button) => button.text().includes(name));
    assert.match(card.text(), /def/);
    card.click();
    assert.equal(opened, name);
  }
  overview.replaceChildren(...(await explorer.prepare("LeanCondensedMatter"))());
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
  overview.find("button").find((item) => item.text() === "Open full dependency graph").click();
  assert.equal(opened, names[0]);
  picker.value = names[1];
  picker.change();
  assert.match(overview.text(), /Used by \(1\)/);
  overview.find("button").find((item) => item.text() === names[0]).click();
  assert.equal(overview.find("h4").at(-1).text(), names[0]);
  assert.match(overview.text(), /Definitions 2/);
  assert.match(overview.text(), /Theorems 0/);
  assert.match(overview.text(), /Total 2/);
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
    allowed: (entry) => declarationAllowed(entry, "theorem", generated) });
  overview.replaceChildren(...(await explorer.prepare("LeanCondensedMatter"))());
  let picker = overview.find("select")[0];
  assert.deepEqual(picker.find("option").map(({ value }) => value), ["", "result"]);
  assert.match(overview.text(), /Definitions 0.*Theorems 1.*Total 1/);
  picker.value = "result";
  picker.change();
  assert.match(overview.text(), /Depends on \(2 total, 0 on map\)/);
  generated = true;
  overview.replaceChildren(...(await explorer.prepare("LeanCondensedMatter"))());
  picker = overview.find("select")[0];
  assert.deepEqual(picker.find("option").map(({ value }) => value), ["", "generated", "result"]);
  assert.match(overview.text(), /Theorems 2.*Total 2.*Generated 1/);
  assert.match(overview.text(), /0 definitions · 1 proved theorem/);
});
