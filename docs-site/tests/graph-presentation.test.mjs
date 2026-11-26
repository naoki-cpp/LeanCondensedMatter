import { test } from "node:test";
import assert from "node:assert/strict";
import { createGraphPresentation } from "../graph-presentation.js";

test("import legend and drawing share styles without declaration-only meanings", () => {
  const p = createGraphPresentation("modules");
  const legend = p.legend();
  assert.deepEqual(legend.map((item) => item.label), ["module", "import", "cross-link"]);
  assert.deepEqual(legend[0].attributes, p.node({ kind: "module" }));
  assert.deepEqual(legend[1].attributes, p.edge());
  assert.deepEqual(legend[2].attributes, p.edge({ tree: false }));
  assert.deepEqual(p.edge({ wrapper: true, typeOnly: true }), p.edge());
});

test("declaration legend uses the exact node and edge rules used by drawing", () => {
  const p = createGraphPresentation("theorems");
  const legend = new Map(p.legend().map((item) => [item.label, item.attributes]));
  for (const [kind, label] of [["theorem", "theorem"], ["def", "definition"], ["axiom", "axiom"], ["constructor", "type / constructor / recursor"]]) {
    assert.deepEqual(p.node({ kind }), legend.get(label));
  }
  assert.deepEqual(p.edge({ wrapper: true }), legend.get("direct wrapper"));
  assert.deepEqual(p.edge({ typeOnly: true }), legend.get("type reference"));
  assert.notEqual(p.node({ kind: "theorem" }, { root: true }).fill, legend.get("theorem").fill);
  assert.ok(p.edge({ tree: false, focused: true })["stroke-opacity"] > p.edge({ tree: false })["stroke-opacity"]);
});
