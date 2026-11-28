import { test } from "node:test";
import assert from "node:assert/strict";
import { readExplorerLocation, writeExplorerLocation } from "../explorer-location.js";

const origin = "https://example.test";
const catalog = {
  hasImports: true,
  hasImport: (name) => name === "LeanCondensedMatter.Example",
  hasModule: (name) => ["Example", "LeanCondensedMatter.Example"].includes(name),
  hasGraphModule: (name) => name === "LeanCondensedMatter.Example",
  hasDeclaration: (name) => name === "Example.result",
};

test("dependency graph history preserves the module and map selection across restoration", () => {
  const graph = { page: "theorem", root: "Example.result", direction: "both", depth: 2, module: "*",
    returnBrowse: "Example", returnMap: null };
  const entry = writeExplorerLocation(origin + "/?browse=Example", graph);
  const restored = readExplorerLocation(new URL(entry.path, origin), entry.navigation, catalog);
  assert.equal(restored.root, "Example.result");
  assert.equal(restored.returnBrowse, "Example");
  const back = writeExplorerLocation(origin + entry.path, {
    page: "overview", browse: restored.returnBrowse, direction: restored.direction, depth: restored.depth, module: "*",
  }, "Example.result");
  const overview = readExplorerLocation(new URL(back.path, origin), back.navigation, catalog);
  assert.equal(overview.browse, "Example");
  assert.equal(overview.mapSelection, "Example.result");
});

test("imports and legacy module URLs retain their routing rules", () => {
  const imports = readExplorerLocation(new URL("/?view=imports&import-module=LeanCondensedMatter.Example&depth=3", origin), null, catalog);
  assert.equal(imports.page, "imports");
  assert.equal(imports.depth, 3);
  assert.equal(imports.canonicalize, false);
  const legacy = readExplorerLocation(new URL("/?module=LeanCondensedMatter.Example", origin), null, catalog);
  assert.equal(legacy.page, "overview");
  assert.equal(legacy.browse, "LeanCondensedMatter.Example");
  assert.equal(legacy.canonicalize, true);
});
