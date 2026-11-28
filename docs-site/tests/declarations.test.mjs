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
  ]), { definitions: 2, theorems: 0, total: 2, generated: 1 });
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
      dependents: name === names[1] ? [names[0]] : [] })), overview,
    onBrowse() { assert.fail("The map should open a declaration directly"); },
    onOpenDeclaration(name) { opened = name; },
  });
  await explorer.render("MixedOrderData");
  assert.match(overview.text(), /Definitions 2/);
  assert.match(overview.text(), /Theorems 0/);
  assert.match(overview.text(), /Total 2/);
  for (const name of names) {
    const card = overview.find("button").find((button) => button.text().includes(name));
    assert.match(card.text(), /def/);
    card.click();
    assert.equal(opened, name);
  }
  await explorer.render("LeanCondensedMatter");
  assert.equal(overview.find("h3").find((heading) => heading.id === "research-map-title")?.text(), "Map");
  const region = overview.find("button").find((button) => button.className === "research-map-region");
  assert.match(region.text(), /2 declarations/);
  region.click();
  assert.equal(overview.find("canvas").length, 1);
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
