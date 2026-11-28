import { test } from "node:test";
import assert from "node:assert/strict";
import { createExplorerComposition } from "../explorer-composition.js";

function container() {
  return {
    children: [],
    append(child) {
      const previous = child.parentElement;
      if (previous) previous.children = previous.children.filter((node) => node !== child);
      child.parentElement = this;
      this.children.push(child);
    },
    prepend(child) { this.append(child); },
    replaceChildren(...children) {
      this.children = [];
      for (const child of children) this.append(child);
    },
    querySelector(selector) { return this.children.find((child) => child.selector === selector); },
    classList: { toggle() {} },
    before() {},
    setAttribute() {},
    contains() { return false; },
  };
}

test("only the current overview mounts shared controls after asynchronous preparation", async () => {
  globalThis.document = { body: {}, activeElement: {} };
  const ui = Object.fromEntries([
    "tabs", "controls", "controlsHome", "overviewLink", "moduleImportsLink", "importsPanel",
    "declarationsPanel", "appShell", "graphMapControls",
    "graphStatus", "graphToolbar", "backToMap", "overview", "viewport", "searchForm",
  ].map((key) => [key, container()]));
  ui.graph = { closest: () => container() };
  ui.graphMapHeader = Object.fromEntries(["header", "heading", "status", "tabs", "search"]
    .map((key) => [key, container()]));
  const composition = createExplorerComposition(ui);
  const unavailable = () => assert.fail("Unexpected unavailable overview");
  const failed = (error) => assert.fail(error);
  composition.show("overview");
  let resolveOld;
  const old = composition.renderOverview({
    render: () => new Promise((resolve) => { resolveOld = resolve; }), unavailable, failed,
  });
  composition.show("imports", "Example");
  assert.equal(ui.tabs.parentElement, ui.graphMapHeader.tabs);
  assert.equal(ui.controls.parentElement, ui.graphMapControls);
  assert.equal(ui.searchForm.parentElement, ui.graphMapHeader.search);
  assert.equal(ui.backToMap.hidden, true);
  composition.show("theorem", "Dependency graph for Example");
  assert.equal(ui.tabs.parentElement, ui.graphMapHeader.tabs);
  assert.equal(ui.controls.parentElement, ui.graphMapControls);
  assert.equal(ui.searchForm.parentElement, ui.graphMapHeader.search);
  assert.equal(ui.graphMapHeader.heading.textContent, "Dependency graph for Example");
  assert.equal(ui.backToMap.hidden, false);
  composition.show("overview");
  const tabSlot = { ...container(), selector: ".map-tabs-slot" };
  const controlSlot = { ...container(), selector: ".map-controls-slot" };
  const searchSlot = { ...container(), selector: ".map-search-slot" };
  let mounts = 0;
  let disposals = 0;
  await composition.renderOverview({
    render: () => () => ({
      nodes: [tabSlot, controlSlot, searchSlot],
      mount() { mounts += 1; },
      dispose() { disposals += 1; },
    }), unavailable, failed,
  });
  resolveOld(() => assert.fail("Superseded content was built"));
  await old;
  assert.equal(ui.tabs.parentElement, tabSlot);
  assert.equal(ui.controls.parentElement, controlSlot);
  assert.equal(ui.searchForm.parentElement, searchSlot);
  assert.equal(ui.controlsHome.hidden, true);
  assert.equal(ui.overviewLink.tabIndex, 0);
  assert.equal(mounts, 1);
  composition.show("imports", "Example");
  composition.show("imports", "Another module");
  assert.equal(disposals, 1);
});
