import { test } from "node:test";
import assert from "node:assert/strict";
import { curvedEdgePath } from "../graph-edge.js";

const point = (radius, angle) => ({ x: radius * Math.cos(angle), y: radius * Math.sin(angle), radius, angle });

function assertForward(source, target) {
  const numbers = curvedEdgePath(source, target, 0, 0).match(/-?\d+(?:\.\d+)?(?:e[+-]?\d+)?/gi).map(Number);
  const points = Array.from({ length: 4 }, (_, i) => ({ x: numbers[2 * i], y: numbers[2 * i + 1] }));
  const dx = target.x - source.x;
  const dy = target.y - source.y;
  for (let i = 0; i <= 100; i += 1) {
    const t = i / 100;
    const weights = [(1 - t) ** 2, 2 * (1 - t) * t, t ** 2];
    const progress = weights.reduce((sum, weight, j) => sum + weight * (
      (points[j + 1].x - points[j].x) * dx + (points[j + 1].y - points[j].y) * dy
    ), 0);
    assert.ok(progress >= -1e-8, `curve reverses at t=${t}: ${JSON.stringify({ source, target })}`);
  }
}

test("dependency arrows advance toward their target at every angle and depth", () => {
  for (const sourceRadius of [0, 100, 200]) {
    for (const targetRadius of [0, 100, 200]) {
      for (let a = 0; a < 16; a += 1) {
        for (let b = 0; b < 16; b += 1) {
          assertForward(point(sourceRadius, a * Math.PI / 8), point(targetRadius, b * Math.PI / 8));
        }
      }
    }
  }
});

test("center connections follow the other node's direction with a translated center", () => {
  const cx = 640, cy = 480;
  const root = { x: cx, y: cy, radius: 0, angle: 0 };
  const outer = { x: cx - 100, y: cy + 100, radius: Math.sqrt(20000), angle: 3 * Math.PI / 4 };
  for (const [source, target] of [[root, outer], [outer, root]]) {
    const numbers = curvedEdgePath(source, target, cx, cy).match(/-?\d+(?:\.\d+)?(?:e[+-]?\d+)?/gi).map(Number);
    assert.deepEqual(numbers.slice(0, 2), [source.x, source.y]);
    assert.deepEqual(numbers.slice(-2), [target.x, target.y]);
    for (let i = 2; i < 6; i += 2) {
      assert.ok(Math.abs(numbers[i] + numbers[i + 1] - cx - cy) < 1e-8);
    }
  }
});
