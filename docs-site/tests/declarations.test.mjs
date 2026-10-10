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
  constructor(tag) { this.tag = tag; this.children = []; this.textContent = ""; }
  append(...children) { this.children.push(...children); }
  replaceChildren(...children) { this.children = children; }
  setAttribute() {}
  addEventListener(event, callback) { this[event] = callback; }
  text() { return this.textContent + this.children.map((child) => child.text?.() ?? child).join(" "); }
  find(tag) { return this.children.flatMap((child) => typeof child === "object"
    ? [...(child.tag === tag ? [child] : []), ...child.find(tag)] : []); }
}

test("MixedComponentCrossing overview counts and opens both definitions", async () => {
  globalThis.document = { createElement: (tag) => new Element(tag) };
  globalThis.fetch = async () => ({ ok: true, text: async () => "/-! # Mixed crossings -/" });
  const overview = new Element("div");
  const names = ["mixedComponentCrossingCount", "mixedComponentWeight"];
  let opened;
  const explorer = createModuleOverview({
    catalog: names.map((name) => ({ name, module: "LeanCondensedMatter.MixedComponentCrossing",
      kind: "def", generated: false, statement: "Nat" })), overview,
    onBrowse() {}, onOpenDeclaration(name) { opened = name; },
  });
  await explorer.render("MixedComponentCrossing");
  assert.match(overview.text(), /Definitions 2/);
  assert.match(overview.text(), /Theorems 0/);
  assert.match(overview.text(), /Total 2/);
  for (const name of names) {
    const card = overview.find("button").find((button) => button.text().includes(name));
    assert.match(card.text(), /def/);
    card.click();
    assert.equal(opened, name);
  }
});
