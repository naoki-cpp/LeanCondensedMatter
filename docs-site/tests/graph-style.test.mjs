import { test } from "node:test";
import assert from "node:assert/strict";
import { graphLabelLines } from "../graph-style.js";

test("graph labels preserve identifiers that fit two lines and bound longer labels", () => {
  for (const name of ["Observable", "pairingTransport_preserves_block", "a".repeat(52), "𝕜".repeat(52)]) {
    const lines = graphLabelLines(name);
    assert.equal(lines.join(""), name);
    assert.ok(lines.length <= 2);
    assert.ok(lines.every((line) => Array.from(line).length <= 26));
  }
  const lines = graphLabelLines("long_".repeat(30));
  assert.equal(lines.length, 2);
  assert.ok(lines.every((line) => Array.from(line).length <= 26));
  assert.ok(lines[1].endsWith("…"));
});
