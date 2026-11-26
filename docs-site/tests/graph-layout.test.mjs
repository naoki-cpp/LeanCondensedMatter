import { test } from "node:test";
import assert from "node:assert/strict";
import { buildGraphScene } from "../graph-layout.js";

function catalog(edges) {
  const entries = new Map();
  for (const name of new Set(edges.flat())) entries.set(name, { dependencies: [], dependents: [] });
  for (const [source, target] of edges) {
    entries.get(source).dependencies.push(target);
    entries.get(target).dependents.push(source);
  }
  return entries;
}

test("scene handles cycles, missing references, filtering and direction without changing input", () => {
  const entries = catalog([["root", "a"], ["a", "b"], ["b", "root"], ["consumer", "root"], ["root", "hidden"]]);
  entries.get("a").dependencies.push("missing");
  const before = structuredClone(entries);
  const scene = buildGraphScene(entries, { root: "root", accepts: (name) => name !== "hidden" });
  assert.deepEqual(entries, before);
  assert.equal(scene.levels.get("root"), 0);
  assert.equal(scene.levels.get("a"), -1);
  assert.equal(scene.levels.get("consumer"), 1);
  assert.equal(scene.levels.has("hidden"), false);
  assert.equal(scene.levels.has("missing"), false);
  assert.equal(scene.positions.size, scene.levels.size);
  for (const [name, point] of scene.positions) {
    assert.ok(Number.isFinite(point.x) && Number.isFinite(point.y));
    if (scene.levels.get(name) < 0) assert.ok(point.x < scene.cx);
    if (scene.levels.get(name) > 0) assert.ok(point.x > scene.cx);
  }
  const onlyDependencies = buildGraphScene(entries, { root: "root", direction: "dependencies", depth: 1 });
  assert.equal(onlyDependencies.levels.has("consumer"), false);
  assert.equal(onlyDependencies.levels.has("b"), false);
});

test("scene is deterministic and caps dense neighborhoods", () => {
  const entries = catalog(Array.from({ length: 100 }, (_, i) => ["root", `node${i}`]));
  const scene = buildGraphScene(entries, { root: "root" });
  assert.equal(scene.levels.size, 80);
  assert.equal(scene.truncated, true);
  assert.deepEqual(buildGraphScene(new Map([...entries].reverse()), { root: "root" }), scene);
  assert.equal(new Set([...scene.positions.values()].map((p) => `${p.x}:${p.y}`)).size, 80);
});
