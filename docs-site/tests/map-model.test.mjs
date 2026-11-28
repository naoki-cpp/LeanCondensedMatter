import { test } from "node:test";
import assert from "node:assert/strict";
import { buildDeclarationHierarchy } from "../declaration-hierarchy.js";
import { declarationAllowed } from "../declaration-model.js";
import { createMapNavigation } from "../map-navigation.js";

test("module paths, subtree counts, and directional sibling dependencies share one hierarchy", () => {
  const entries = [
    { name: "outer", module: "LeanCondensedMatter.A", kind: "def", dependencies: ["left", "neighbor"] },
    { name: "left", module: "A.Left.Deep", kind: "theorem", dependencies: ["right", "right", "neighbor", "missing"] },
    { name: "right", module: "A.Right", kind: "theorem", axioms: ["sorryAx"], dependencies: ["left"] },
    { name: "neighbor", module: "AB", kind: "opaque" },
    { name: "generated", module: "A.Right", kind: "def", generated: true },
  ];
  const hierarchy = buildDeclarationHierarchy(entries, ["A.Empty"]);
  const a = hierarchy.find("LeanCondensedMatter.A");
  assert.equal(a, hierarchy.find("A"));
  assert.equal(hierarchy.find("LeanCondensedMatter"), hierarchy.root);
  assert.equal(hierarchy.find("A.Missing"), null);
  assert.equal(hierarchy.find("A.Empty").entries.length, 0);
  assert.deepEqual(a.declarations.map(({ name }) => name), ["outer"]);
  assert.deepEqual(a.entries.map(({ name }) => name), ["outer", "left", "generated", "right"]);
  assert.deepEqual(a.counts, { definitions: 1, theorems: 2, proved: 1, total: 3, generated: 1 });
  assert.equal(a.visibleCounts.definitions, 2);
  const directions = (parent) => hierarchy.bundles(parent).map(({ a, b, ab, ba }) => [a.path, b.path, ab, ba]);
  assert.deepEqual(directions(a), [["A.Left", "A.Right", 1, 1]]);
  assert.deepEqual(directions(hierarchy.root), [["A", "AB", 2, 0]]);

  const filtered = buildDeclarationHierarchy(entries.filter((entry) => declarationAllowed(entry, "definition")));
  assert.equal(filtered.find("A.Right"), null);
  assert.equal(filtered.find("A").visibleCounts.total, 1);
  assert.equal(filtered.bundles(filtered.root)[0].ab, 1);
});

test("camera selection, parent transitions, and reset keep the visible scope consistent", () => {
  const navigation = createMapNavigation(960, 670);
  const parent = { x: 480, y: 335, radius: 140, children: [], points: [] };
  const child = { x: 420, y: 385, radius: 25, children: [], points: [], parent };
  const sibling = { x: 540, y: 385, radius: 25, children: [], points: [], parent };
  parent.children.push(child, sibling);
  const siblingPoint = { positions: new Map([[null, { x: 10, y: 10 }], [parent, { x: 540, y: 385 }]]) };
  navigation.open(child, false);
  assert.deepEqual(navigation.pointOnScreen(siblingPoint), navigation.screen(540, 385));
  const point = { x: child.x, y: child.y, region: child,
    positions: new Map([[child, { x: child.x, y: child.y }]]) };
  navigation.select(point);
  assert.equal(navigation.selected, point);
  assert.deepEqual(navigation.pointOnScreen(point), [480, 335]);
  assert.equal(navigation.zoom(1 / 1.5), true);
  assert.equal(navigation.active, parent);
  assert.equal(navigation.selected, null);
  assert.equal(navigation.zoom(1 / 1.5), false);
  navigation.step(0);
  navigation.step(210);
  assert.equal(navigation.animating, true);
  navigation.pan(30, 0);
  assert.equal(navigation.animating, false);
  navigation.zoom(0.01);
  assert.equal(navigation.active, null);
  assert.deepEqual(navigation.view, { x: 480, y: 335, zoom: 1 });
});

test("zoom keeps the cursor anchored and camera completion is deterministic", () => {
  const navigation = createMapNavigation(960, 670);
  navigation.zoom(2, 800, 150);
  assert.deepEqual(navigation.screen(800, 150), [800, 150]);
  navigation.open({ x: 100, y: 120, radius: 20, children: [] }, true);
  navigation.step(10);
  navigation.step(430);
  assert.equal(navigation.animating, false);
  assert.deepEqual(navigation.screen(100, 120), [480, 335]);
});
