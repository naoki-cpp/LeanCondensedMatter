import { test } from "node:test";
import assert from "node:assert/strict";
import { createCatalogData } from "../catalog-data.js";

const base = "https://example.invalid/";
const path = "declaration-details/" + "a".repeat(64) + ".json";
const a = { name: "A", module: "M" };
const b = { name: "B", module: "M" };
const c = { name: "C", module: "N" };
const structure = { version: 1, binders: [] };
const index = { version: 1, modules: { M: path }, declarations: [a, b, c] };
const response = (value, status = 200) => ({
  status, ok: status === 200, json: async () => value,
});

test("loads only the index initially and shares one module request", async () => {
  const calls = [];
  const data = createCatalogData(async (url) => {
    calls.push(url);
    return response(url.endsWith("declaration-index.json") ? index : { A: structure });
  }, base);
  assert.deepEqual(await data.load(), [a, b, c]);
  assert.deepEqual(calls, [base + "declaration-index.json"]);
  assert.equal(data.hasDeferredStatement(c), false);
  assert.equal(await data.statement(c), null);
  assert.deepEqual(await Promise.all([data.statement(a), data.statement(b)]), [structure, null]);
  assert.deepEqual(await data.statement(a), structure);
  assert.deepEqual(calls, [base + "declaration-index.json", base + path]);
});

test("failed shard requests are not permanently cached", async () => {
  let attempts = 0;
  const data = createCatalogData(async (url) => {
    if (url.endsWith("declaration-index.json")) return response(index);
    return ++attempts === 1 ? response(null, 404) : response({ A: structure });
  }, base);
  await data.load();
  await assert.rejects(data.statement(a), /404/);
  assert.deepEqual(await data.statement(a), structure);
  assert.equal(attempts, 2);
});

test("uses legacy declarations only if the split index has not been published", async () => {
  const calls = [];
  const legacy = [{ ...a, structuredStatement: structure }];
  const data = createCatalogData(async (url) => {
    calls.push(url);
    return url.endsWith("declaration-index.json") ? response(null, 404) : response(legacy);
  }, base);
  assert.deepEqual(await data.load(), legacy);
  assert.equal(data.hasDeferredStatement(legacy[0]), false);
  assert.deepEqual(await data.statement(legacy[0]), structure);
  assert.deepEqual(calls, [base + "declaration-index.json", base + "declarations.json"]);
});

test("rejects unsupported index schemas and invalid shard paths", async () => {
  const invalid = createCatalogData(async () => response({ ...index, version: 2 }), base);
  await assert.rejects(invalid.load(), /unsupported/);
  const unsafe = createCatalogData(async () => response({ ...index, modules: { M: "../x" } }), base);
  await unsafe.load();
  await assert.rejects(unsafe.statement(a), /invalid declaration detail path/);
});
