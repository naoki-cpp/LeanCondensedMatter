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
    "declarationsPanel", "appShell", "importMapHeader", "importMapControls", "importMapTabs",
    "graphStatus", "graphToolbar", "overview", "viewport", "searchForm", "importMapSearch",
  ].map((key) => [key, container()]));
  ui.graph = { closest: () => container() };
  ui.importMapHeader.append({ selector: ".research-map-title" });
  const composition = createExplorerComposition(ui);
  const unavailable = () => assert.fail("Unexpected unavailable overview");
  const failed = (error) => assert.fail(error);
  composition.show("overview");
  let resolveOld;
  const old = composition.renderOverview({
    render: () => new Promise((resolve) => { resolveOld = resolve; }), unavailable, failed,
  });
  composition.show("imports", "Example");
  assert.equal(ui.tabs.parentElement, ui.importMapTabs);
  assert.equal(ui.controls.parentElement, ui.importMapControls);
  assert.equal(ui.searchForm.parentElement, ui.importMapSearch);
  composition.show("overview");
  const tabSlot = { ...container(), selector: ".map-tabs-slot" };
  const controlSlot = { ...container(), selector: ".map-controls-slot" };
  const searchSlot = { ...container(), selector: ".map-search-slot" };
  await composition.renderOverview({
    render: () => () => [tabSlot, controlSlot, searchSlot], unavailable, failed,
  });
  resolveOld(() => assert.fail("Superseded content was built"));
  await old;
  assert.equal(ui.tabs.parentElement, tabSlot);
  assert.equal(ui.controls.parentElement, controlSlot);
  assert.equal(ui.searchForm.parentElement, searchSlot);
  assert.equal(ui.controlsHome.hidden, true);
  assert.equal(ui.overviewLink.tabIndex, 0);
});
