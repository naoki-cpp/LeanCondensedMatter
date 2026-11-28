import { test } from "node:test";
import assert from "node:assert/strict";
import { buildDeclarationHierarchy } from "../declaration-hierarchy.js";
import { declarationAllowed } from "../declaration-model.js";
import { createMapNavigation } from "../map-navigation.js";
import { createMapScene } from "../map-scene.js";
import { createDeclarationVisibility } from "../declaration-visibility.js";

test("map labels and hit tests use the same visible child regions", () => {
  const hierarchy = buildDeclarationHierarchy([
    { name: "left", module: "Example.Left", kind: "def" },
    { name: "right", module: "Example.Right", kind: "theorem" },
  ]);
  const scene = createMapScene([...hierarchy.root.children.values()], hierarchy, 960, 670);
  const navigation = createMapNavigation(960, 670);
  const example = scene.region("Example");
  const left = scene.region("Example.Left");
  navigation.open(example, false);
  const frame = scene.frame(navigation);
  assert.ok(frame.labels.includes(left));
  const [x, y] = frame.screen(left.x, left.y);
  assert.equal(frame.target(x, y).region, left);
  assert.equal(frame.hoverPoint(x, y), null);
  navigation.open(left, false);
  const leaf = scene.frame(navigation);
  assert.equal(leaf.target(...leaf.pointOnScreen(scene.point("left"))).point.entry.name, "left");
});

test("catalog visibility agrees across search, module filtering, and map hierarchy", () => {
  const catalog = [
    { name: "a", module: "A", kind: "theorem" },
    { name: "b", module: "B", kind: "def", generated: true },
    { name: "c", module: "A", kind: "abbrev" },
  ];
  const visibility = createDeclarationVisibility(catalog, "definition", false);
  assert.deepEqual(visibility.entries.map(({ name }) => name), ["c"]);
  assert.equal(visibility.allows("c", "A"), true);
  assert.equal(visibility.allows("c", "B"), false);
  assert.equal(visibility.mapHierarchy().find("B"), null);
  assert.equal(createDeclarationVisibility(catalog, "definition", true).allows("b", "B"), true);
});
import { ZOOM_STEP, createCameraFrames, zoomFactorForKey, zoomFactorForWheel } from "../map-zoom.js";

test("camera scheduling ignores repeat starts and cancels pending frames", (t) => {
  const callbacks = new Map();
  let id = 0;
  const schedule = (step) => {
    callbacks.set(++id, step);
    return id;
  };
  const raf = globalThis.requestAnimationFrame;
  const cancel = globalThis.cancelAnimationFrame;
  globalThis.requestAnimationFrame = schedule;
  globalThis.cancelAnimationFrame = (frame) => callbacks.delete(frame);
  t.after(() => {
    globalThis.requestAnimationFrame = raf;
    globalThis.cancelAnimationFrame = cancel;
  });
  const frames = createCameraFrames();
  frames.start(() => true);
  frames.start(() => assert.fail("Existing frame was replaced"));
  assert.equal(callbacks.size, 1);
  const first = callbacks.get(1);
  callbacks.delete(1);
  first(100);
  assert.equal(frames.running, true);
  frames.stop();
  assert.equal(frames.running, false);
  assert.equal(callbacks.size, 0);
});

test("shared zoom input matches reciprocal steps and leaves ordinary scrolling alone", () => {
  assert.equal(zoomFactorForKey("+"), ZOOM_STEP);
  assert.equal(zoomFactorForKey("-"), 1 / ZOOM_STEP);
  assert.equal(zoomFactorForWheel({ deltaY: -40 }), null);
  assert.equal(zoomFactorForWheel({ ctrlKey: true, deltaY: 0 }), null);
  const wheelIn = zoomFactorForWheel({ ctrlKey: true, deltaY: -2, deltaMode: 1 });
  const wheelOut = zoomFactorForWheel({ metaKey: true, deltaY: 32, deltaMode: 0 });
  assert.ok(wheelIn > 1 && wheelOut < 1);
  assert.ok(Math.abs(wheelIn * wheelOut - 1) < Number.EPSILON);
});

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
  navigation.zoom(0.01, undefined, undefined, false);
  assert.equal(navigation.active, null);
  assert.deepEqual(navigation.view, { x: 480, y: 335, zoom: 1 });
});

test("reset animates from the current camera back to the whole map", () => {
  const navigation = createMapNavigation(960, 670);
  navigation.open({ x: 100, y: 120, radius: 20, children: [] }, false);
  const start = { ...navigation.view };
  navigation.reset(true);
  assert.equal(navigation.active, null);
  assert.deepEqual(navigation.view, start);
  navigation.step(100);
  navigation.step(310);
  assert.ok(navigation.view.zoom > 1 && navigation.view.zoom < start.zoom);
  const midway = { ...navigation.view };
  navigation.reset(true);
  assert.deepEqual(navigation.view, midway);
  navigation.step(520);
  assert.equal(navigation.animating, false);
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
